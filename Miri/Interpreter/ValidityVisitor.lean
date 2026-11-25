import Miri.Interpreter.PlaceDynamic
import Miri.Interpreter.Discriminant
import Miri.Interpreter.MemoryErrors
import Miri.Memory.Validity

/-! Canonical typed runtime visitor from pinned validity.rs and visitor.rs.
Traversal consumes actual RuntimePlace/TyAndLayout, not a pre-resolved value
graph. Compiler facts and machine accesses remain required effectful leaves.
-/
namespace Miri.Interpreter.ValidityVisitor
open Miri.ABI Miri.Memory
open Miri.Memory.Validity

inductive TypeKind where
  | boolean | character | integer | float | functionPointer | never | foreign | functionDefinition
  | rawPointer (pointee : MIR.TyId) (pointeeSized : Bool)
  | reference (mutable : Bool)
  | string
  | sequence (element : MIR.TyId)
  | dynamic (expectedTrait : PredicateList)
  | box
  | pattern (base : MIR.TyId)
  | aggregate (maybeDangling unsafeCell isEnum : Bool)
  | unsafeBinder
  | invalid
  deriving DecidableEq, Repr

inductive MetadataTail where
  | dynamic (expectedTrait : PredicateList)
  | sliceOrStr | foreign
  deriving DecidableEq, Repr

structure Key (P : Type) where
  mplace : MemPlace P
  layout : LocalLayout
  deriving DecidableEq, Repr
abbrev Session (P : Type) := ValidationSession (Key P)
abbrev M (S A : Type) := EStateM StepError S A

/-- Memory operations here run under withGhostValidation, including provenance
writes. Retagging is the source exception: its actual machine reborrow effects
must still execute. readBytes strips provenance and checks initialization; it
must not validate UTF-8 (source str validity only checks bytes). beginPadding
obtains mutable allocation access once, followed by writePadding per gap. -/
structure Hooks (P S C E Fn ABI Padding : Type) where
  target : RuntimeTargetDataLayout
  projection : PlaceProjectionHooks P S C E
  vtable : VTableHooks P S C Fn ABI
  discriminant : DiscriminantHooks P S C (RuntimePlace P)
  debugAssertions : Bool
  classify : C → MIR.TyId → M S TypeKind
  unitLayout : C → M S LocalLayout
  typeName : C → MIR.TyId → M S String
  opsemInhabited : C → MIR.TyId → M S Bool
  isFreeze : C → MIR.TyId → M S Bool
  fieldPath : C → LocalLayout → Nat → MIR.TyId → M S PathElem
  variantPath : C → LocalLayout → Nat → M S PathElem
  projectBox : C → RuntimePlace P → M S (RuntimePlace P × RuntimePlace P)
  toOp : C → RuntimePlace P → M S (OpTy P)
  readImmediate : C → RuntimePlace P → ExpectedValue → M S (RvalueImmTy P)
  clearProvenance : C → RuntimePlace P → M S Unit
  writeNoValidate : C → Immediate P → RuntimePlace P → M S Unit
  sizeAndAlign : C → MPlaceTy P → M S (Option (Size × Align))
  ptrToPlace : C → RvalueImmTy P → M S (MPlaceTy P)
  metadataTail : C → MIR.TyId → M S MetadataTail
  checkPointerAccess : C → Pointer (Option P) → Size → M S (Except AccessError Unit)
  checkPointerAlign : C → Pointer (Option P) → Align → M S Unit
  /-- Typed result for validity's source-specific AlignmentCheckFailed mapping.
  Other consumers keep the ordinary machine alignment error behavior. -/
  checkPointerAlignResult : C → Pointer (Option P) → Align → M S (Except Misalignment Unit)
  scalarMayBeNull : C → Scalar P → M S Bool
  retagPointer : C → RvalueImmTy P → MIR.TyId → M S (Option (RvalueImmTy P))
  ctfePointerLookup : C → MPlaceTy P → CtfeMode → M S PointerAllocLookup
  inMutableMemory : C → RuntimePlace P → M S Bool
  readBytes : C → MPlaceTy P → Size → ExpectedValue → M S Unit
  clearBytesProvenance : C → MPlaceTy P → Size → M S Unit
  beginPadding : C → MPlaceTy P → Size → M S (Option Padding)
  writePadding : C → Padding → AllocRange → M S Unit
  cachedUnionRanges : C → LocalLayout → M S DataRangeSet → M S DataRangeSet
  withGhostValidation : {A : Type} → M S A → M S A

private def liftResult (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def failure (session : Session P) (message : String) : M S A :=
  throw (.undefinedBehavior s!"validation{session.path.render}: {message}")

/-- `validity.rs::check_safe_pointer` gives retag failures two pieces of
source-specific treatment. A mutable reborrow of immutable memory is reported
as a validity failure at the current path, while an aliasing-model machine
stop carries the path as diagnostic context. This runner keeps the callback's
successor state in either case, including when it fails after changing the
borrow tree. -/
def classifyRetagError (path : ValidationPath) (kind : SafePointerKind)
    (error : StepError) : StepError :=
  match error with
  | .retagWriteToReadOnly =>
    let target := match kind with | .box => "box" | .reference _ => "mutable reference"
    .undefinedBehavior s!"validation{path.render}: encountered {target} pointing to read-only memory"
  | .machineStop message =>
    if path.projections.isEmpty then .machineStop message
    else .machineStop s!"{message}; while retagging field {path.render}"
  | other => other

-- Mirrors pinned `PtrKind::Display`: mutability does not change `reference`.
private def safePointerName : SafePointerKind → String
  | .reference _ => "reference"
  | .box => "box"

def classifyPointerAlignmentError (path : ValidationPath) (kind : SafePointerKind)
    (misalignment : Misalignment) : StepError :=
  match misalignment.required.bytes, misalignment.has.bytes with
  | .ok required, .ok found =>
    .undefinedBehavior s!"validation{path.render}: encountered an unaligned {safePointerName kind} (required {required} byte alignment but found {found})"
  | .error error, _ | _, .error error =>
    .invalidProgram s!"validity alignment formatting: {reprStr error}"

/-- Keep the source check_ptr_align successor state when turning its one
source-remapped failure into a validation UB. Other machine failures retain
their original classification and successor state. -/
def mapPointerAlignmentOutcome (path : ValidationPath) (kind : SafePointerKind)
    (check : M S (Except Misalignment Unit)) : M S Unit := fun state =>
  match check state with
  | .ok (.ok ()) successor => .ok () successor
  | .ok (.error misalignment) successor =>
    .error (classifyPointerAlignmentError path kind misalignment) successor
  | .error error successor => .error error successor

def classifyPointerAccessError (path : ValidationPath) (kind : SafePointerKind)
    (error : AccessError) : StepError :=
  match error with
  | .danglingIntegerPointer address _ _ =>
    let diagnostic := if address == 0 then s!"encountered a null {safePointerName kind}"
      else s!"encountered a dangling {safePointerName kind} (address {address} has no provenance)"
    .undefinedBehavior s!"validation{path.render}: {diagnostic}"
  | .allocationLookup (.deadAllocation _) =>
    .undefinedBehavior s!"validation{path.render}: encountered a dangling {safePointerName kind} (use-after-free)"
  | .pointerOutOfBounds .. =>
    .undefinedBehavior s!"validation{path.render}: encountered a dangling {safePointerName kind} (going beyond the bounds of its allocation)"
  | _ => Miri.Interpreter.MemoryErrors.access error

def mapRetagOutcome (path : ValidationPath) (kind : SafePointerKind)
    (retag : M S A) : M S A := fun state =>
  match retag state with
  | .ok adjusted successor => .ok adjusted successor
  | .error error successor => .error (classifyRetagError path kind error) successor

def retagSafePointer (path : ValidationPath) (kind : SafePointerKind)
    (retag : C → RvalueImmTy P → MIR.TyId → M S (Option (RvalueImmTy P)))
    (c : C) (pointer : RvalueImmTy P) (ty : MIR.TyId) : M S (Option (RvalueImmTy P)) :=
  mapRetagOutcome path kind (retag c pointer ty)
private def scalarOf (value : Immediate P) : M S (Scalar P) :=
  liftResult (value.toScalar.mapError fun error => .invalidProgram s!"validity scalar: {repr error}")
private def sizeResult (value : Except SizeError A) : M S A :=
  liftResult (value.mapError fun error => .invalidProgram s!"validity size: {repr error}")
private def rangeResult (value : Except RangeSetError A) : M S A :=
  liftResult (value.mapError fun error => .invalidProgram s!"validity range: {repr error}")

private def sizePlace (h : Hooks P S C E F A Pad) (c : C) (place : RuntimePlace P) : M S (Option (Size × Align)) := do
  if place.layout.layout.isSized then return some (place.layout.layout.size,place.layout.layout.align.abi)
  match place.ref with
  | .memory memory => h.sizeAndAlign c ⟨memory,place.layout⟩
  | .local .. => throw (.invalidProgram "unsized local validity place")

private def markRange (session : Session P) (offset size : Size) : M S (Session P) := do
  let some ranges := session.dataBytes | return session
  let ranges ← rangeResult (ranges.addRange offset size)
  return {session with dataBytes := some ranges}
private def dataOffset (h : Hooks P S C E F A Pad) (c : C) (place : RuntimePlace P) : M S Size := do
  match (← h.toOp c place).op with
  | .indirect memory => return memory.ptr.offset
  | .immediate _ => throw (.invalidProgram "tracked validity data is not in memory")
private def markPlace (h : Hooks P S C E F A Pad) (c : C) (session : Session P)
    (place : RuntimePlace P) : M S (Session P) := do
  if session.dataBytes.isNone then return session
  if !place.layout.layout.isSized then throw (.invalidProgram "unsized validity data range")
  markRange session (← dataOffset h c place) place.layout.layout.size

private def resetPointer (h : Hooks P S C E F A Pad) (c : C) (place : RuntimePlace P)
    (pointer : RvalueImmTy P) : M S Unit := do
  match pointer.layout.layout.backendRepr with
  | .Scalar _ => if !(← scalarOf pointer.imm).isPointer then h.clearProvenance c place
  | _ => h.writeNoValidate c pointer.imm place

private def checkMetadata [PointerProvenance P] (h : Hooks P S C E F A Pad) (c : C)
    (place : MPlaceTy P) : M S Unit := do
  match ← h.metadataTail c place.layout.ty with
  | .foreign => pure ()
  | .sliceOrStr =>
    let scalar ← liftResult (place.mplace.metadata.unwrapMeta.mapError fun e => .invalidProgram (reprStr e))
    let _ ← liftResult ((scalar.toTargetUsize h.target.pointerSize).mapError ScalarOps.scalarError)
  | .dynamic expected =>
    let scalar ← liftResult (place.mplace.metadata.unwrapMeta.mapError fun e => .invalidProgram (reprStr e))
    let pointer ← liftResult ((scalar.toPointer h.target.base).mapError ScalarOps.scalarError)
    let _ ← VTable.getPtrVTableType h.vtable c pointer (some expected)

private def checkSafe [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (session : Session P) (value : RuntimePlace P) (ty : MIR.TyId) (kind : SafePointerKind) : M S (Session P) := do
  let pointer ← h.readImmediate c value (match kind with | .box => .box | _ => .reference)
  let mut session := session
  if session.flags.resetProvenanceAndPadding then session ← markPlace h c session value
  let place ← h.ptrToPlace c pointer
  if !place.layout.layout.isSized then checkMetadata h c place
  let dynamic ← h.sizeAndAlign c place
  let (size, align) := dynamic.getD (place.layout.layout.size, place.layout.layout.align.abi)
  let adjusted ← if !session.flags.mayDangle then do
      match ← h.checkPointerAccess c place.mplace.ptr size with
      | .ok () => pure ()
      | .error error => throw (classifyPointerAccessError session.path kind error)
      if session.flags.resetProvenanceAndPadding then
        retagSafePointer session.path kind h.retagPointer c pointer ty
      else pure none
    else do
      let scalar ← liftResult ((Scalar.fromMaybePointer h.target.base place.mplace.ptr).mapError ScalarOps.scalarError)
      match scalar.tryToScalarInt with
      | .ok (.integer integer) =>
        let address ← liftResult ((integer.toTargetUsize h.target.pointerSize).mapError fun e => .invalidProgram (reprStr e))
        let maximum := (2^h.target.base.pointerWidth.bits.toNat - 1 : Nat)
        if address.toNat + size.bytes.toNat > maximum then failure session "safe pointer too close to address-space end"
      | .ok (.erasedPointer ..) => pure ()
      | .error error => throw (ScalarOps.scalarError error)
      pure none
  if let some adjusted := adjusted then h.writeNoValidate c adjusted.imm value
  else if session.flags.resetProvenanceAndPadding then resetPointer h c value pointer
  let scalar ← liftResult ((Scalar.fromMaybePointer h.target.base place.mplace.ptr).mapError ScalarOps.scalarError)
  if ← h.scalarMayBeNull c scalar then failure session "null or maybe-null safe pointer"
  unless ← h.opsemInhabited c place.layout.ty do failure session "safe pointer to uninhabited type"
  mapPointerAlignmentOutcome session.path kind
    (h.checkPointerAlignResult c place.mplace.ptr align)
  if let some tracker := session.refTracking then
    unless session.flags.mayDangle do
      let mut skip := false
      if let some mode := session.ctfeMode then
        let lookup ← h.ctfePointerLookup c place mode
        match ctfeRecursionDecision mode kind lookup with
        | .error error => failure session (reprStr error)
        | .ok value => skip := value
      unless skip do
        let key : Key P := ⟨place.mplace, place.layout⟩
        let tracker := tracker.track key (fun _ => session.path.push .deref)
        session := {session with refTracking := some tracker}
  return session

/-- Data-byte union layout walk. It traverses compiler layouts, never reads an
active union field, and preserves the source scalar-array fast path. -/
def unionRanges (h : Hooks P S C E F A Pad) (c : C) : Nat → LocalLayout → Size → DataRangeSet → M S DataRangeSet
  | 0, _, _, _ => throw (.resourceExhaustion "union layout traversal fuel")
  | fuel+1, layout, base, initial => do
    if layout.layout.isZst then return initial
    let mut ranges := initial
    match layout.layout.fields with
    | .Primitive => ranges ← rangeResult (ranges.addRange base layout.layout.size)
    | .Union count =>
      for field in [:count] do
        ranges ← unionRanges h c fuel (← h.projection.field c layout field) base ranges
    | .Array stride count =>
      let element ← h.projection.field c layout 0
      if element.layout.backendRepr.isScalar then
        ranges ← rangeResult (ranges.addRange base (← sizeResult (element.layout.size.mul count)))
      else
        for index in [:count.toNat] do
          let offset ← sizeResult (stride.mul (UInt64.ofNat index))
          ranges ← unionRanges h c fuel element (← sizeResult (base.add offset)) ranges
    | .Arbitrary offsets _ =>
      for index in [:offsets.size] do
        let some offset := offsets[index]? | throw (.invalidProgram "union layout field offset")
        ranges ← unionRanges h c fuel (← h.projection.field c layout index) (← sizeResult (base.add offset)) ranges
    if let .Multiple _ _ _ variants := layout.layout.variants then
      for variant in [:variants.size] do
        ranges ← unionRanges h c fuel (← h.projection.variant c layout variant) base ranges
    return ranges

private def checkScalarRange [PointerProvenance P] (h : Hooks P S C E F A Pad) (c : C)
    (session : Session P) (scalar : Scalar P) (abi : ABI.Scalar) : M S Unit := do
  match abi with
  | .Union .. => pure ()
  | .Initialized (value := primitive) (validRange := validRange) =>
    let size ← liftResult ((Primitive.size primitive h.target).mapError fun e => .invalidProgram (reprStr e))
    let callback := fun scalar state => h.scalarMayBeNull c scalar state
    match Validity.checkScalar ⟨size, validRange⟩ scalar callback (← get) with
    | .ok () state => set state
    | .error (.machine error) state => set state; throw error
    | .error error state => set state; failure session (reprStr error)

private def abiRanges [PointerProvenance P] (h : Hooks P S C E F A Pad) (c : C)
    (session : Session P) (place : RuntimePlace P) : M S Unit := do
  match place.layout.layout.backendRepr with
  | .Scalar abi =>
    if let .Initialized .. := abi then
      let scalar ← scalarOf (← h.readImmediate c place .integer).imm
      checkScalarRange h c session scalar abi
  | .ScalarPair (a := abiA) (b := abiB) .. =>
    if let .Initialized .. := abiA then
      if let .Initialized .. := abiB then
        match (← h.readImmediate c place .integer).imm with
        | .scalarPair a b => checkScalarRange h c session a abiA; checkScalarRange h c session b abiB
        | _ => throw (.invalidProgram "validity scalar-pair ABI mismatch")
  | _ => pure ()

private def primitive [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (session : Session P) (place : RuntimePlace P) (kind : TypeKind) : M S (Option (Session P)) := do
  match kind with
  | .never => failure session "never value"
  | .foreign | .functionDefinition => return some session
  | .unsafeBinder => throw (.unsupported "upstream unsafe-binder validity is unimplemented")
  | .invalid => throw (.invalidProgram "invalid/non-normalized type during validity")
  | .boolean | .character | .integer | .float =>
    let expected := match kind with | .boolean => ExpectedValue.boolean | .character => .character | .float => .float | _ => .integer
    let scalar ← scalarOf (← h.readImmediate c place expected).imm
    if kind == .boolean then
      let _ ← liftResult (scalar.toBool.mapError fun error => .undefinedBehavior s!"validation{session.path.render}: {repr error}")
    if kind == .character then
      let _ ← liftResult (scalar.toChar.mapError fun error => .undefinedBehavior s!"validation{session.path.render}: {repr error}")
    if session.flags.resetProvenanceAndPadding then
      h.clearProvenance c place
      return some (← markPlace h c session place)
    return some session
  | .rawPointer _ sized =>
    let pointer ← h.readImmediate c place .rawPointer
    let mut session := session
    if session.flags.resetProvenanceAndPadding then
      resetPointer h c place pointer
      session ← markPlace h c session place
    if !sized then
      let target ← h.ptrToPlace c pointer
      if target.layout.layout.isSized then throw (.invalidProgram "unsized raw-pointer target resolved sized")
      checkMetadata h c target
    return some session
  | .reference mutable => return some (← checkSafe h c session place place.layout.ty (.reference mutable))
  | .functionPointer =>
    let scalar ← scalarOf (← h.readImmediate c place .functionPointer).imm
    if session.refTracking.isSome then
      let pointer ← liftResult ((scalar.toPointer h.target.base).mapError ScalarOps.scalarError)
      let _ ← VTable.getPtrFn h.vtable c pointer
    else if ← h.scalarMayBeNull c scalar then failure session "null or maybe-null function pointer"
    if session.flags.resetProvenanceAndPadding then
      if !scalar.isPointer then h.clearProvenance c place
      return some (← markPlace h c session place)
    return some session
  | _ => return none

/-- Recursive ValueVisitor plus validity-specific primitive/array/union rules.
Fuel exhaustion is visible resource failure; it never validates an unexplored
subvalue. Fields follow in-memory order; enum tag precedes active variant. -/
def visit [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C) :
    Nat → Session P → RuntimePlace P → M S (Session P)
  | 0, _, _ => throw (.resourceExhaustion "validity traversal fuel")
  | fuel+1, session, place => do
    let kind ← h.classify c place.layout.ty
    if let some session ← primitive h c session place kind then return session
    let mut session := session
    if let some mode := session.ctfeMode then
      if !allowsImmutableUnsafeCell mode then
        let sized ← sizePlace h c place
        if sized.map Prod.fst != some Size.ZERO then
          if let .aggregate _ true _ := kind then
            unless ← h.inMutableMemory c place do failure session "UnsafeCell in read-only memory"
    match kind with
    | .string =>
      let .indirect memory := (← h.toOp c place).op | throw (.invalidProgram "str immediate")
      let len ← PlaceDynamic.length h.projection c place
      h.readBytes c ⟨memory, place.layout⟩ (Size.ofBytes len) .string
    | .sequence element =>
      let elementKind ← h.classify c element
      if elementKind == .integer || elementKind == .float then
        let len ← PlaceDynamic.length h.projection c place
        let elementLayout ← h.projection.layoutOf c element
        let size ← sizeResult (elementLayout.layout.size.mul len)
        if size == Size.ZERO then return session
        let op ← h.toOp c place
        let memory ← match op.op with
          | .indirect memory => pure memory
          | .immediate .uninit => failure session "uninitialized numeric array"
          | .immediate _ => throw (.invalidProgram "numeric array scalar ABI")
        let expected := if elementKind == .float then ExpectedValue.float else .integer
        h.readBytes c ⟨memory, place.layout⟩ size expected
        if session.flags.resetProvenanceAndPadding then
          h.clearBytesProvenance c ⟨memory, place.layout⟩ size
          session ← markRange session memory.ptr.offset size
      else
        let elementLayout ← h.projection.layoutOf c element
        if elementLayout.layout.isZst then
          if (← PlaceDynamic.length h.projection c place) > 0 then
            let child ← PlaceDynamic.index h.projection c place 0
            let path := session.path
            session ← visit h c fuel {session with path := path.push (.arrayElem 0)} child
            session := {session with path}
        else
          let stride ← match place.layout.layout.fields with
            | .Array stride _ => pure stride
            | _ => throw (.invalidProgram "sequence has non-array fields")
          let len ← PlaceDynamic.length h.projection c place
          let element ← h.projection.field c place.layout 0
          let endOffset ← sizeResult (stride.mul len)
          let _ ← PlaceDynamic.offsetWithMeta h.projection c place endOffset .inbounds .none (← h.unitLayout c)
          for index in [:len.toNat] do
            let offset ← sizeResult (stride.mul (UInt64.ofNat index))
            let child ← PlaceDynamic.offsetWithMeta h.projection c place offset .wrapping .none element
            let path := session.path
            session ← visit h c fuel {session with path := path.push (.arrayElem index)} child
            session := {session with path}
    | .pattern base =>
      let layout ← h.projection.layoutOf c base
      if !layout.layout.isSized || !place.layout.layout.isSized || layout.layout.size != place.layout.layout.size then
        throw (.invalidProgram "pattern base transmute layout mismatch")
      let child ← PlaceDynamic.offsetWithMeta h.projection c place .ZERO .wrapping .none layout
      session ← visit h c fuel session child
      abiRanges h c session place
    | _ =>
      let oldMayDangle := session.flags.mayDangle
      if let .aggregate maybeDangling _ _ := kind then
        session := {session with flags := {session.flags with mayDangle := oldMayDangle || maybeDangling}}
      if let .dynamic expected := kind then
        let op ← h.toOp c place
        let inner ← VTable.unpackDynTrait h.vtable c op expected
        let .indirect memory := inner.op | throw (.invalidProgram "dynamic unpack returned immediate")
        let path := session.path
        session ← visit h c fuel {session with path := path.push (← h.fieldPath c place.layout 0 inner.layout.ty)} ⟨.memory memory,inner.layout⟩
        session := {session with path}
      else if kind == .box then
        let (pointer, allocator) ← h.projectBox c place
        session ← checkSafe h c session pointer place.layout.ty .box
        let path := session.path
        session ← visit h c fuel {session with path := path.push (← h.fieldPath c place.layout 1 allocator.layout.ty)} allocator
        session := {session with path}
      else
        match place.layout.layout.fields with
        | .Primitive => pure ()
        | .Union _ =>
          if let some mode := session.ctfeMode then
            if !allowsImmutableUnsafeCell mode then
              let size ← sizePlace h c place
              if size.map Prod.fst != some Size.ZERO then
                unless ← h.isFreeze c place.layout.ty do
                  unless ← h.inMutableMemory c place do failure session "UnsafeCell union in read-only memory"
          if session.flags.resetProvenanceAndPadding && session.dataBytes.isSome then
            let base ← dataOffset h c place
            if !place.layout.layout.isSized then throw (.invalidProgram "unsized union data ranges")
            let ranges ← h.cachedUnionRanges c place.layout (unionRanges h c fuel place.layout Size.ZERO .empty)
            for range in ranges.toArray do
              session ← markRange session (← sizeResult (base.add range.start)) range.size
        | .Arbitrary _ order =>
          for index in order do
            let child ← PlaceDynamic.field h.projection c place index
            let path := session.path
            session ← visit h c fuel {session with path := path.push (← h.fieldPath c place.layout index child.layout.ty)} child
            session := {session with path}
        | .Array stride _ =>
          let len ← PlaceDynamic.length h.projection c place
          let element ← h.projection.field c place.layout 0
          let endOffset ← sizeResult (stride.mul len)
          let _ ← PlaceDynamic.offsetWithMeta h.projection c place endOffset .inbounds .none (← h.unitLayout c)
          for index in [:len.toNat] do
            let offset ← sizeResult (stride.mul (UInt64.ofNat index))
            let child ← PlaceDynamic.offsetWithMeta h.projection c place offset .wrapping .none element
            let path := session.path
            session ← visit h c fuel {session with path := path.push (.arrayElem index)} child
            session := {session with path}
        match place.layout.layout.variants with
        | .Multiple .. =>
          let variant ← Discriminant.readDiscriminant h.discriminant c (← h.toOp c place)
          let child ← PlaceDynamic.downcast h.projection c place variant
          let path := session.path
          session ← visit h c fuel {session with path := path.push (← h.variantPath c place.layout variant)} child
          session := {session with path}
        | .Empty =>
          match kind with
          | .aggregate _ _ true => failure session "zero-variant enum value"
          | _ => throw (.invalidProgram "variantless validity type is not an enum")
        | .Single _ => pure ()
      session := {session with flags := {session.flags with mayDangle := oldMayDangle}}
    unless ← h.opsemInhabited c place.layout.ty do throw (.invalidProgram "uninhabited type passed validity")
    if h.debugAssertions then abiRanges h c session place
    return session

/-- A fieldless inhabited aggregate has no value bytes or child accesses.
The premises expose compiler queries at this state, rather than assuming a
validation-operation outcome. -/
theorem visit_fieldless [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (fuel : Nat) (session : Session P)
    (place : RuntimePlace P) (state : S) (variant : Nat)
    (classify : h.classify c place.layout.ty state =
      .ok (.aggregate false false false) state)
    (inhabited : h.opsemInhabited c place.layout.ty state = .ok true state)
    (fields : place.layout.layout.fields = .Arbitrary #[] #[])
    (variants : place.layout.layout.variants = .Single variant)
    (runtime : session.ctfeMode = none) (debugOff : h.debugAssertions = false) :
    visit h c (fuel+1) session place state = .ok session state := by
  simp [visit, classify, primitive, fields, variants, runtime, inhabited, debugOff,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases session with | mk path flags mode tracking bytes =>
    cases flags
    simp_all

/-- An integer visit reads the scalar and applies provenance reset, if requested.
Without tracked data bytes, it retains the current validation session. -/
theorem visit_integer [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (fuel : Nat) (session : Session P)
    (place : RuntimePlace P) (state : S) (value : Scalar P) (layout : LocalLayout)
    (classify : h.classify c place.layout.ty state = .ok .integer state)
    (read : h.readImmediate c place .integer state = .ok ⟨.scalar value, layout⟩ state)
    (clear : h.clearProvenance c place state = .ok () state)
    (ranges : session.dataBytes = none) :
    visit h c (fuel + 1) session place state = .ok session state := by
  cases reset : session.flags.resetProvenanceAndPadding <;>
    simp [visit, classify, primitive, scalarOf, liftResult, markPlace,
      ranges, read, clear, reset, Immediate.toScalar, Except.mapError,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- Integer validation in a sized memory place marks its byte range after
reading the value and clearing provenance. -/
theorem visit_integer_memory [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (fuel : Nat) (session : Session P)
    (place : RuntimePlace P) (state : S) (value : Scalar P) (layout : LocalLayout)
    (memory : MemPlace P) (ranges updated : DataRangeSet)
    (classify : h.classify c place.layout.ty state = .ok .integer state)
    (read : h.readImmediate c place .integer state = .ok ⟨.scalar value, layout⟩ state)
    (clear : h.clearProvenance c place state = .ok () state)
    (operand : h.toOp c place state = .ok ⟨.indirect memory, place.layout⟩ state)
    (reset : session.flags.resetProvenanceAndPadding = true)
    (tracked : session.dataBytes = some ranges)
    (sized : place.layout.layout.isSized = true)
    (marked : ranges.addRange memory.ptr.offset place.layout.layout.size = .ok updated) :
    visit h c (fuel + 1) session place state = .ok {session with dataBytes := some updated} state := by
  simp [visit, classify, primitive, scalarOf, liftResult, markPlace, markRange, dataOffset,
    rangeResult, marked, operand, tracked, sized, read, clear, reset, Immediate.toScalar,
    Except.mapError, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- A sized raw pointer with pointer provenance needs no metadata lookup.
Its pointer scalar already carries provenance, so reset leaves it intact. -/
theorem visit_raw_sized_pointer [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (fuel : Nat) (session : Session P)
    (place : RuntimePlace P) (state : S) (value : Scalar P) (layout : LocalLayout)
    (target : MIR.TyId) (abi : ABI.Scalar)
    (classify : h.classify c place.layout.ty state = .ok (.rawPointer target true) state)
    (read : h.readImmediate c place .rawPointer state = .ok ⟨.scalar value, layout⟩ state)
    (backend : layout.layout.backendRepr = .Scalar abi) (pointer : value.isPointer = true)
    (ranges : session.dataBytes = none) :
    visit h c (fuel + 1) session place state = .ok session state := by
  cases reset : session.flags.resetProvenanceAndPadding <;>
    simp [visit, classify, primitive, resetPointer, scalarOf, liftResult, markPlace,
      ranges, read, backend, pointer, reset, Immediate.toScalar, Except.mapError,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- A reference reaches the safe-pointer checks with the current session.
Those checks retain their own retag, alignment, and error effects. -/
theorem visit_reference [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (fuel : Nat)
    (session : Session P) (place : RuntimePlace P) (before : S) (isMutable : Bool)
    (kind : h.classify c place.layout.ty before = .ok (.reference isMutable) before) :
    visit h c (fuel + 1) session place before =
      checkSafe h c session place place.layout.ty (.reference isMutable) before := by
  simp only [visit, bind, Bind.bind, EStateM.bind, kind, primitive, Pure.pure, EStateM.pure]
  cases checkSafe h c session place place.layout.ty (.reference isMutable) before <;> rfl

/-- Shallow validation of a sized reference keeps the session after the
actual reborrow and immediate write-back. Each policy runs in source order
on the machine returned by the preceding phase. -/
theorem visit_reference_local [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (fuel : Nat)
    (session : Session P) (value : RuntimePlace P) (before retagged written : S)
    (mutable : Bool) (pointer adjusted : RvalueImmTy P) (place : MPlaceTy P)
    (scalar : Scalar P) (dynamic : Option (Size × Align))
    (classify : h.classify c value.layout.ty before = .ok (.reference mutable) before)
    (read : h.readImmediate c value .reference before = .ok pointer before)
    (ranges : session.dataBytes = none) (reset : session.flags.resetProvenanceAndPadding = true)
    (metadata : h.ptrToPlace c pointer before = .ok place before)
    (sized : place.layout.layout.isSized = true)
    (sizeAlign : h.sizeAndAlign c place before = .ok dynamic before)
    (live : session.flags.mayDangle = false)
    (access : h.checkPointerAccess c place.mplace.ptr
      ((dynamic.getD (place.layout.layout.size, place.layout.layout.align.abi)).1) before =
        .ok (.ok ()) before)
    (retag : h.retagPointer c pointer value.layout.ty before = .ok (some adjusted) retagged)
    (write : h.writeNoValidate c adjusted.imm value retagged = .ok () written)
    (formed : Scalar.fromMaybePointer h.target.base place.mplace.ptr = .ok scalar)
    (nonNull : h.scalarMayBeNull c scalar written = .ok false written)
    (inhabited : h.opsemInhabited c place.layout.ty written = .ok true written)
    (alignment : h.checkPointerAlignResult c place.mplace.ptr
      ((dynamic.getD (place.layout.layout.size, place.layout.layout.align.abi)).2) written =
        .ok (.ok ()) written) (tracking : session.refTracking = none) :
    visit h c (fuel + 1) session value before = .ok session written := by
  rw [visit_reference h c fuel session value before mutable classify]
  simp only [checkSafe, read, markPlace, ranges, reset, metadata, sized, live, sizeAlign,
    access, retagSafePointer, mapRetagOutcome, retag, write, formed, nonNull, inhabited,
    mapPointerAlignmentOutcome, alignment, tracking, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    ↓reduceIte, Option.isNone, Except.mapError, liftResult]

private def resetPadding (h : Hooks P S C E F A Pad) (c : C) (session : Session P)
    (place : RuntimePlace P) : M S Unit := do
  let some ranges := session.dataBytes | return
  let memory ← forceAllocation h.projection.place c place
  let dynamic ← h.sizeAndAlign c memory
  let size := (dynamic.getD (memory.layout.layout.size,memory.layout.layout.align.abi)).1
  let start := memory.mplace.ptr.offset
  if ranges.toArray == #[allocRange start size] then return
  let some handle ← h.beginPadding c memory size | return
  let writes ← liftResult ((paddingWrites ranges start size).mapError fun error => .invalidProgram s!"padding: {repr error}")
  for range in writes do h.writePadding c handle range

/-- No padding allocation is needed for a local-only validation session. -/
@[simp] theorem resetPadding_no_ranges (h : Hooks P S C E F A Pad) (c : C)
    (session : Session P) (place : RuntimePlace P) (empty : session.dataBytes = none) :
    resetPadding h c session place = pure () := by
  simp [resetPadding, empty]

/-- Unit memory validation has no padding bytes. Its zero-size mutable-access
query produces no handle, so reset performs no writes or allocation. -/
theorem resetPadding_memory_zero [PointerProvenance P] (h : Hooks P S C E F A Pad)
    (c : C) (session : Session P) (place : MPlaceTy P) (state : S)
    (ranges : session.dataBytes = some .empty)
    (size : place.layout.layout.size = Size.ZERO)
    (dynamic : h.sizeAndAlign c place state = .ok (some (Size.ZERO,place.layout.layout.align.abi)) state)
    (padding : h.beginPadding c place Size.ZERO state = .ok none state) :
    resetPadding h c session ⟨.memory place.mplace,place.layout⟩ state = .ok () state := by
  simp [resetPadding, ranges, forceAllocation, dynamic, size,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  split
  · rfl
  · simp only [bind, Bind.bind, EStateM.bind, padding, pure, Pure.pure, EStateM.pure]

/-- Runtime validation: root may retag/reset; tracked pointees are checked in
LIFO order without reset, without further tracking, and under may_dangle. -/
def validatePlace [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (place : RuntimePlace P) (recursive reset : Bool) : M S Unit := do
  let name ← h.typeName c place.layout.ty
  let initial : Session P := {
    path := ⟨name,#[]⟩, flags := ⟨reset,false⟩, ctfeMode := none
    refTracking := if recursive then some .empty else none, dataBytes := none }
  let mut session ← h.withGhostValidation do
    let mut session := initial
    if reset then
      if let .indirect _ := (← h.toOp c place).op then session := {session with dataBytes := some .empty}
    session ← visit h c fuel session place
    resetPadding h c session place
    return session
  if recursive then
    let mut remaining := fuel
    let mut continueLoop := true
    while continueLoop do
      match session.refTracking.bind RefTracking.next with
      | none => continueLoop := false
      | some ((key,path),tracking) =>
        if remaining == 0 then throw (.resourceExhaustion "recursive validity tracker fuel")
        remaining := remaining - 1
        session := {session with refTracking := some tracking}
        let childSession : Session P := {path, flags := ⟨false,true⟩,ctfeMode := none,refTracking := none,dataBytes := none}
        h.withGhostValidation do
          let child : RuntimePlace P := ⟨.memory key.mplace,key.layout⟩
          let visited ← visit h c fuel childSession child
          resetPadding h c visited child

/-- Shallow validation runs the root visit in ghost mode and performs its
padding reset within the same scope. -/
theorem validatePlace_shallow [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (fuel : Nat)
    (place : RuntimePlace P) (reset : Bool) :
    validatePlace h c fuel place false reset = (do
      let name ← h.typeName c place.layout.ty
      let initial : Session P := {
        path := ⟨name, #[]⟩, flags := ⟨reset, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none }
      let _ ← h.withGhostValidation do
        let mut session := initial
        if reset then
          if let .indirect _ := (← h.toOp c place).op then
            session := {session with dataBytes := some .empty}
        session ← visit h c fuel session place
        resetPadding h c session place
        return session
      return ()) := by
  unfold validatePlace
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- Const validation exposes the updated worklist to its outer interning loop;
CTFE restrictions are distinct from ordinary recursive runtime checks. -/
def constValidatePlace [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (place : RuntimePlace P) (path : ValidationPath)
    (tracking : RefTracking (Key P) ValidationPath) (mode : CtfeMode) :
    M S (RefTracking (Key P) ValidationPath) := h.withGhostValidation do
  let session : Session P := {path,flags := ⟨false,false⟩,ctfeMode := some mode,refTracking := some tracking,dataBytes := none}
  let session ← visit h c fuel session place
  match session.refTracking with
  | some tracking => return tracking
  | none => throw (.invalidProgram "const validation lost tracker")

/-- Internal zero-padding composition after the original local place has
been proved to denote its existing backing. -/
theorem resetPadding_forced_zero [PointerProvenance P] (h : Hooks P S C E F A Pad)
    (c : C) (session : Session P) (original : RuntimePlace P) (place : MPlaceTy P) (state : S)
    (ranges : session.dataBytes = some .empty)
    (forced : forceAllocation h.projection.place c original state = .ok place state)
    (size : place.layout.layout.size = Size.ZERO)
    (dynamic : h.sizeAndAlign c place state = .ok (some (Size.ZERO,place.layout.layout.align.abi)) state)
    (padding : h.beginPadding c place Size.ZERO state = .ok none state) :
    resetPadding h c session original state = .ok () state := by
  simp [resetPadding,ranges,forced,dynamic,size,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  split
  · rfl
  · simp only [bind,Bind.bind,EStateM.bind,padding,pure,Pure.pure,EStateM.pure]

end Miri.Interpreter.ValidityVisitor
