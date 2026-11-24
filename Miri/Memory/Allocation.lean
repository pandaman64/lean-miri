import Miri.Memory.NativeBuffer
import Miri.Memory.InitMask
import Miri.Memory.ProvenanceMap
import Miri.Memory.Scalar
import Miri.ABI.Align

/-!
The source-level allocation record and checked read-byte operations from the
pinned `rustc_middle::mir::interpret::allocation` module. The byte backend is
represented by `Array UInt8`; host allocation is an explicit callback at the
fallible constructor boundary.
-/

namespace Miri.Memory

open Miri.ABI

inductive Mutability where
  | Not
  | Mut
  deriving DecidableEq, Repr

inductive AllocInit where
  | Uninit
  | Zero
  deriving DecidableEq, Repr

structure BadBytesAccess where
  access : AllocRange
  bad : AllocRange
  deriving DecidableEq, Repr

inductive AllocError where
  | readPointerAsInt (info : Option BadBytesAccess)
  | readPartialPointer (offset : Size)
  | invalidUninitBytes (info : Option BadBytesAccess)
  | memory (reason : MemoryError)
  | provenance (reason : ProvenanceMapError)
  | alignment (reason : AlignError)
  | storageLengthOverflow (length : Nat)
  | storageLengthMismatch (requested : Size) (actual : Nat)
  | storageBackendNotZeroed (index : Nat) (value : UInt8)
  | outOfBounds (range : AllocRange) (allocationSize : Size)
  | invalidSliceEndpoints (start finish available : Nat)
  | nonEmptyProvenanceWithoutEntry
  | readOnlyAllocation
  | pointerSizeMismatch (scalarSize pointerSize : Size)
  | scalar (reason : ScalarError)
  | scalarBytesTooWide (size : Size)
  | pointerBitsDoNotFitOffset (bits : U128)
  | scalarPointerNotTargetSized (scalarSize targetSize : Size)
  | copyRangesOverlap
  | repeatedCopyRequiresNonoverlapping
  | singleByteZeroCountCopy
  | allocationHasByteFragmentProvenance
  | nativeWriteRangeOutOfBounds (range : AllocRange) (allocationSize : Size)
  | hostMemoryExhausted
  deriving DecidableEq, Repr

inductive AllocationAdjustError (CallbackError : Type) where
  | allocation (reason : AllocError)
  | byteConversion (reason : CallbackError)
  | pointerAdjustment (reason : CallbackError)
  deriving DecidableEq, Repr

private def provenanceErrorText : ProvenanceMapError → String
  | .memory reason => toString reason
  | .pointerSizeZero => "zero-sized target pointer"
  | .unsortedOrDuplicateKeys => "unsorted or duplicate provenance keys"
  | .readPartialPointer offset => s!"partial pointer at {offset.bytes}"
  | .missingWildcard => "missing wildcard provenance"
  | .pointerSizedProvenanceAtByte offset => s!"pointer-sized provenance at byte {offset.bytes}"
  | .insertOverlapsExistingProvenance => "provenance insertion overlaps an existing pointer"
  | .pointerSizeExceedsFragmentStorage bytes =>
      s!"pointer size {bytes} exceeds the supported fragment byte count"
  | .fragmentSliceOutOfBounds start size available =>
      s!"fragment byte slice starts at {start.bytes} with size {size.bytes}, beyond {available} bytes"
  | .copyEntryCountOverflow => "provenance copy entry count exceeds the supported host index range"

instance : ToString ProvenanceMapError where
  toString := provenanceErrorText

instance : ToString AllocError where
  toString
    | .readPointerAsInt _ => "allocation read encountered pointer provenance where bytes were required"
    | .readPartialPointer offset => s!"allocation read encountered a partial pointer at {offset.bytes}"
    | .invalidUninitBytes _ => "allocation read encountered uninitialized bytes"
    | .memory reason => toString reason
    | .provenance reason => s!"provenance-map error: {reason}"
    | .alignment reason => s!"alignment error: {reason}"
    | .storageLengthOverflow length => s!"byte length {length} does not fit in rustc Size"
    | .storageLengthMismatch requested actual =>
        s!"zeroed storage has {actual} bytes, but {requested.bytes} were requested"
    | .storageBackendNotZeroed index value =>
        s!"zeroed-storage backend returned byte {value} at index {index}"
    | .outOfBounds range allocationSize =>
        s!"byte range starting at {range.start.bytes} with length {range.size.bytes} is outside allocation size {allocationSize.bytes}"
    | .invalidSliceEndpoints start finish available =>
        s!"slice [{start}..{finish}] is outside {available} stored bytes"
    | .nonEmptyProvenanceWithoutEntry =>
        "provenance map reported a nonempty overlap without yielding an entry"
    | .readOnlyAllocation => "cannot mutate an immutable allocation"
    | .pointerSizeMismatch scalarSize pointerSize =>
        s!"pointer scalar size {scalarSize.bytes} differs from target pointer size {pointerSize.bytes}"
    | .scalar reason => s!"scalar error: {reason}"
    | .scalarBytesTooWide size => s!"{size.bytes}-byte scalar exceeds the 16-byte integer width"
    | .pointerBitsDoNotFitOffset bits => s!"pointer bits {bits.toNat} do not fit a u64 offset"
    | .scalarPointerNotTargetSized scalarSize targetSize =>
        s!"pointer scalar size {scalarSize.bytes} differs from target pointer size {targetSize.bytes}"
    | .copyRangesOverlap => "nonoverlapping memory copy received overlapping source and destination ranges"
    | .repeatedCopyRequiresNonoverlapping => "repeated memory copies require nonoverlapping mode"
    | .singleByteZeroCountCopy => "single-byte repeated copy asserted a nonzero copy count"
    | .allocationHasByteFragmentProvenance =>
        "CTFE allocation adjustment requires interned pointer-only provenance"
    | .nativeWriteRangeOutOfBounds range allocationSize =>
        s!"native-write range starting at {range.start.bytes} with length {range.size.bytes} is outside allocation size {allocationSize.bytes}"
    | .hostMemoryExhausted => "host allocation failed while creating the rustc allocation"

private def maxU64Nat : Nat := 18446744073709551615

private def checkedAlign (align : Align) : Except AllocError Align := do
  let bytes ← (Align.bytes align).mapError AllocError.alignment
  let normalized ← (Align.fromBytes bytes).mapError AllocError.alignment
  if normalized == align then return align
  throw (.alignment (.tooLarge bytes))

private def sizeForArray (length : Nat) : Except AllocError Size := do
  if length > maxU64Nat then throw (.storageLengthOverflow length)
  let size := Size.ofBytes (UInt64.ofNat length)
  if size.bytes.toNat == length then return size
  throw (.storageLengthOverflow length)

private def pointerSize (layout : TargetDataLayout) : Size :=
  Size.fromBits layout.pointerWidth.bits

private def targetUIntBytes (layout : TargetDataLayout) (size : Size) (bits : U128) :
    Except AllocError (Array UInt8) := do
  if size.bytes > 16 then throw (.scalarBytesTooWide size)
  let count := size.bytes.toNat
  let mut result := #[]
  for index in [:count] do
    let valueIndex := if layout.endian == .little then index else count - index - 1
    let byte := (bits.toNat / 2 ^ (8 * valueIndex)) % 256
    result := result.push (UInt8.ofNat byte)
  return result

private def readTargetUInt (layout : TargetDataLayout) (bytes : Array UInt8) :
    Except AllocError U128 := do
  if bytes.size > 16 then throw (.scalarBytesTooWide (Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

private def firstNonZero (bytes : Array UInt8) : Option (Nat × UInt8) := Id.run do
  for index in [:bytes.size] do
    match bytes[index]? with
    | some byte => if byte != 0 then return some (index, byte)
    | none => return some (index, 0)
  return none

structure Allocation (Prov : Type := CtfeProvenance) (Extra : Type := Unit) where
  private mk ::
  private rawBytes : Array UInt8
  private size : Size
  private provenance : ProvenanceMap Prov
  private initMask : InitMask
  align : Align
  mutability : Mutability
  extra : Extra
  nativeBuffer : Option NativeBufferOwnership := none

namespace Allocation

def fromBytes (bytes : Array UInt8) (align : Align) (mutability : Mutability) :
    Except AllocError (Allocation Prov Unit) := do
  let align ← checkedAlign align
  let size ← sizeForArray bytes.size
  if _h : bytes.size = size.bytes.toNat then
    return ⟨bytes, size, ProvenanceMap.new, InitMask.new size true,
      align, mutability, (), none⟩
  else
    throw (.storageLengthOverflow bytes.size)

def fromBytesByteAlignedImmutable (bytes : Array UInt8) :
    Except AllocError (Allocation Prov Unit) :=
  fromBytes bytes Align.ONE .Not

/-- `zeroedStorage` is the explicit host `AllocBytes::zeroed` boundary. A
`none` result preserves the source's `MemoryExhausted` failure. The backend's
zeroed-storage contract is checked before an allocation value is returned. -/
def tryNew (size : Size) (align : Align) (init : AllocInit)
    (zeroedStorage : Size → Align → Option (Array UInt8)) :
    Except AllocError (Allocation Prov Unit) := do
  let align ← checkedAlign align
  let bytes ← match zeroedStorage size align with
    | some bytes => pure bytes
    | none => throw .hostMemoryExhausted
  if bytes.size != size.bytes.toNat then
    throw (.storageLengthMismatch size bytes.size)
  if let some (index, value) := firstNonZero bytes then
    throw (.storageBackendNotZeroed index value)
  let initialized := match init with
    | .Uninit => false
    | .Zero => true
  if _h : bytes.size = size.bytes.toNat then
    return ⟨bytes, size, ProvenanceMap.new, InitMask.new size initialized,
      align, .Mut, (), none⟩
  else
    throw (.storageLengthMismatch size bytes.size)

def withExtra (allocation : Allocation Prov Unit) (extra : Extra) :
    Allocation Prov Extra :=
  ⟨allocation.rawBytes, allocation.size,
    allocation.provenance, allocation.initMask, allocation.align,
    allocation.mutability, extra, allocation.nativeBuffer⟩

/-- Map only allocation metadata. Byte storage, size, provenance, init mask,
alignment, and mutability are copied unchanged, matching the source fieldwise
metadata update boundary used by tree-retagging. -/
def mapExtra (allocation : Allocation Prov Extra) (f : Extra → Extra') :
    Allocation Prov Extra' :=
  ⟨allocation.rawBytes, allocation.size, allocation.provenance,
    allocation.initMask, allocation.align, allocation.mutability,
    f allocation.extra, allocation.nativeBuffer⟩

/-- Replace only allocation metadata while retaining all allocation storage
and semantic state. -/
def setExtra (allocation : Allocation Prov Extra) (extra : Extra) :
    Allocation Prov Extra :=
  allocation.mapExtra (fun _ => extra)

/-- Attach once at actual backing creation; metadata transformations preserve
this owner. Cloning bytes must allocate a fresh backing before attaching it. -/
def attachNativeBuffer (allocation : Allocation Prov Extra) (owner : NativeBufferOwnership) :
    Except String (Allocation Prov Extra) := do
  if owner.pointer == 0 then throw "cannot attach null native backing"
  if allocation.nativeBuffer.isSome then throw "allocation already owns native backing"
  pure {allocation with nativeBuffer := some owner}

def withoutNativeBuffer (allocation : Allocation Prov Extra) : Allocation Prov Extra :=
  {allocation with nativeBuffer := none}

def len (allocation : Allocation Prov Extra) : Nat := allocation.rawBytes.size

def byteSize (allocation : Allocation Prov Extra) : Size := allocation.size

def provenanceMap (allocation : Allocation Prov Extra) : ProvenanceMap Prov :=
  allocation.provenance

def initializationMask (allocation : Allocation Prov Extra) : InitMask :=
  allocation.initMask

/-- Source `Allocation::adjust_from_tcx`, used when importing interned global
and thread-local allocations into a machine with a different byte backend or
provenance representation. The two callbacks preserve the source's allocation
and pointer-conversion failure boundaries. The source `ptrs()` assertion is
reported explicitly when byte-fragment provenance is present. -/
def adjustFromTcx [PointerProvenance Prov] {CallbackError HookState : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (allocateBytes : Array UInt8 → Align → HookState →
      EStateM.Result CallbackError HookState (Array UInt8))
    (adjustPointer : Pointer CtfeProvenance → HookState →
      EStateM.Result CallbackError HookState (Pointer Prov)) :
    EStateM (AllocationAdjustError CallbackError) HookState (Allocation Prov Unit) :=
  fun initialHookState => Id.run do
    let allocationResult ← match allocateBytes source.rawBytes source.align initialHookState with
      | .ok bytes nextState => pure (bytes, nextState)
      | .error reason nextState => return .error (.byteConversion reason) nextState
    let mut bytes := allocationResult.1
    let mut hookState := allocationResult.2
    if bytes.size != source.rawBytes.size then
      return .error (.allocation (.storageLengthMismatch source.size bytes.size)) hookState
    if source.provenance.byteFragments.isSome then
      return .error (.allocation .allocationHasByteFragmentProvenance) hookState
    let ptrBytes := pointerSize layout
    let mut newProvenance := #[]
    for (offset, sourceProvenance) in source.provenance.ptrs do
      let start := offset.bytes.toNat
      let finish := start + ptrBytes.bytes.toNat
      if finish > bytes.size then
        return .error (.allocation (.invalidSliceEndpoints start finish bytes.size)) hookState
      let pointerBytes := bytes.extract start finish
      let bits ← match readTargetUInt layout pointerBytes with
        | .ok bits => pure bits
        | .error reason => return .error (.allocation reason) hookState
      if bits.toNat > maxU64Nat then
        return .error (.allocation (.pointerBitsDoNotFitOffset bits)) hookState
      let adjusted ← match adjustPointer
          (Pointer.new sourceProvenance (Size.ofBytes (UInt64.ofNat bits.toNat))) hookState with
        | .ok adjusted nextState =>
            hookState := nextState
            pure adjusted
        | .error reason nextState =>
            return .error (.pointerAdjustment reason) nextState
      let encoded ← match targetUIntBytes layout ptrBytes
          (BitVec.ofNat 128 adjusted.offset.bytes.toNat) with
        | .ok encoded => pure encoded
        | .error reason => return .error (.allocation reason) hookState
      bytes := bytes.extract 0 start ++ encoded ++ bytes.extract finish bytes.size
      newProvenance := newProvenance.push (offset, adjusted.provenance)
    let provenance ← match ProvenanceMap.fromPresortedPtrs newProvenance with
      | .ok provenance => pure provenance
      | .error reason =>
          return .error (.allocation (.provenance reason)) hookState
    return .ok ⟨bytes, source.size, provenance, source.initMask, source.align,
      source.mutability, (), none⟩ hookState

private def checkedSlice (allocation : Allocation Prov Extra) (range : AllocRange) :
    Except AllocError (Array UInt8) := do
  if allocation.rawBytes.size != allocation.size.bytes.toNat then
    throw (.storageLengthMismatch allocation.size allocation.rawBytes.size)
  let finish ← range.endExclusive |>.mapError AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.size.bytes then
    throw (.outOfBounds range allocation.size)
  return allocation.rawBytes.extract range.start.bytes.toNat finish.bytes.toNat

/-- Raw bytes with the source method's caller-side bounds precondition made
explicit rather than relying on a host array indexing panic. -/
def getBytesUnchecked (allocation : Allocation Prov Extra) (range : AllocRange) :
    Except AllocError (Array UInt8) :=
  checkedSlice allocation range

/-- Inspect raw bytes outside interpreter execution, including uninitialized
bytes and provenance. The source slice panics for invalid endpoints; Lean
reports that invalid domain explicitly. -/
def inspectWithUninitAndPtrOutsideInterpreter
    (allocation : Allocation Prov Extra) (start finish : Nat) :
    Except AllocError (Array UInt8) := do
  if start > finish || finish > allocation.rawBytes.size then
    throw (.invalidSliceEndpoints start finish allocation.rawBytes.size)
  return allocation.rawBytes.extract start finish

/-- Adopt a snapshot of this allocation's actual native backing storage after
an external host operation. The host must report the very same allocation;
this is not an interpreter write: initialization, provenance, permissions and
extras remain unchanged until source process_native_write/trace processing. -/
def refreshNativeBytes (allocation : Allocation Prov Extra) (bytes : Array UInt8) :
    Except AllocError (Allocation Prov Extra) := do
  unless bytes.size == allocation.size.bytes.toNat do
    throw (.storageLengthMismatch allocation.size bytes.size)
  return {allocation with rawBytes := bytes}

/-- Matches `Allocation::get_bytes_strip_provenance`: check initialization
first, then reject overlapping non-address provenance when required, then
return bytes. `layout` supplies the target pointer width used by the map. -/
def getBytesStripProvenance [PointerProvenance Prov]
    (allocation : Allocation Prov Extra) (layout : TargetDataLayout)
    (range : AllocRange) : Except AllocError (Array UInt8) := do
  match ← (allocation.initMask.isRangeInitialized range).mapError AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  if !PointerProvenance.offsetIsAddr (Prov := Prov) then
    let ptrBytes := pointerSize layout
    let isEmpty ← (allocation.provenance.rangeEmpty range ptrBytes).mapError AllocError.provenance
    if !isEmpty then
      let entries ← (allocation.provenance.getRange range ptrBytes).mapError AllocError.provenance
      let some (provRange, _) := entries[0]?
        | throw .nonEmptyProvenanceWithoutEntry
      let provFinish ← provRange.endExclusive |>.mapError AllocError.memory
      let rangeFinish ← range.endExclusive |>.mapError AllocError.memory
      let badStart := if provRange.start.bytes > range.start.bytes
        then provRange.start else range.start
      let badFinish := if provFinish.bytes < rangeFinish.bytes
        then provFinish else rangeFinish
      let bad ← (AllocRange.fromEndpoints badStart badFinish).mapError AllocError.memory
      throw (.readPointerAsInt (some ⟨range, bad⟩))
  checkedSlice allocation range

/-! Scalar memory access. The source assumes caller-side bounds and alignment;
these Lean methods keep invalid ranges as explicit errors instead of array
panics. -/

def readScalar [DecidableEq Prov] [PointerProvenance Prov]
    (allocation : Allocation Prov Extra) (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    Except AllocError (Scalar Prov) := do
  match ← (allocation.initMask.isRangeInitialized range).mapError AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← checkedSlice allocation range
  let bits ← readTargetUInt layout bytes
  if readProvenance then
    let targetSize := pointerSize layout
    if range.size != targetSize then
      throw (.scalarPointerNotTargetSized range.size targetSize)
    let provenance ← match allocation.provenance.readPtr range.start targetSize with
      | .ok provenance => pure provenance
      | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
      | .error reason => throw (.provenance reason)
    match provenance with
    | some provenance =>
      if bits.toNat > 18446744073709551615 then
        throw (.pointerBitsDoNotFitOffset bits)
      return Scalar.fromPointer layout
        (Pointer.new provenance (Size.ofBytes (UInt64.ofNat bits.toNat)))
    | none =>
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
  else
    if PointerProvenance.offsetIsAddr (Prov := Prov) then
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
    let isEmpty ← (allocation.provenance.rangeEmpty range (pointerSize layout)).mapError AllocError.provenance
    if isEmpty then
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

/-- The full source `Allocation::write_scalar` state transition. It checks
mutability, decodes the scalar, marks initialization, clears overwritten
provenance against the old bytes, writes target-endian bits, then inserts a
pointer provenance entry when the value is a pointer. -/
def writeScalar (layout : TargetDataLayout) (range : AllocRange)
    (value : Scalar Prov) : EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let bitsAndPointer ← match value.toBitsOrPtrInternal range.size with
    | .ok converted => pure converted
    | .error reason => return .error (.scalar reason) state
  match checkedSlice state range with
  | .error error => return .error error state
  | .ok _ => pure ()
  let nextMask ← match state.initMask.setRange range true with
    | .ok mask => pure mask
    | .error error => return .error (.memory error) state
  let beforeClear := { state with initMask := nextMask }
  match state.provenance.clear range state.rawBytes (pointerSize layout) with
  | .error reason mapAfter =>
    return .error (.provenance reason) { beforeClear with provenance := mapAfter }
  | .ok () clearedMap =>
    let finish := range.start.bytes.toNat + range.size.bytes.toNat
    let start := range.start.bytes.toNat
    let (bits, provenance) := match bitsAndPointer with
      | .bits bits => (bits, none)
      | .pointer pointer => (BitVec.ofNat 128 pointer.offset.bytes.toNat, some pointer.provenance)
    let data ← match targetUIntBytes layout range.size bits with
      | .ok data => pure data
      | .error error => return .error error { beforeClear with provenance := clearedMap }
    let bytes := state.rawBytes.extract 0 start ++ data ++
      state.rawBytes.extract finish state.rawBytes.size
    if bytes.size != state.size.bytes.toNat then
      return .error (.storageLengthMismatch state.size bytes.size)
        { beforeClear with provenance := clearedMap }
    let afterWrite := { beforeClear with rawBytes := bytes, provenance := clearedMap }
    match provenance with
    | none => return .ok () afterWrite
    | some provenance =>
      if range.size != pointerSize layout then
        return .error (.scalarPointerNotTargetSized range.size (pointerSize layout)) afterWrite
      match clearedMap.insertPtr range.start provenance (pointerSize layout) with
      | .error reason mapAfter =>
        return .error (.provenance reason) { afterWrite with provenance := mapAfter }
      | .ok () insertedMap =>
        return .ok () { afterWrite with provenance := insertedMap }

/-- Pointer-valued convenience wrapper around the source scalar write path. -/
def writePointer (layout : TargetDataLayout) (range : AllocRange)
    (pointer : Pointer Prov) : EStateM AllocError (Allocation Prov Extra) Unit :=
  writeScalar layout range (Scalar.fromPointer layout pointer)

private def runProvenanceMutation {α : Type}
    (mutation : EStateM.Result ProvenanceMapError (ProvenanceMap Prov) α)
    (state : Allocation Prov Extra) :
    EStateM.Result AllocError (Allocation Prov Extra) α :=
  match mutation with
  | .ok value provenance => .ok value { state with provenance }
  | .error reason provenance => .error (.provenance reason) { state with provenance }

private def setInitialization (state : Allocation Prov Extra) (range : AllocRange)
    (initialized : Bool) : Except AllocError (Allocation Prov Extra) := do
  let initMask ← state.initMask.setRange range initialized |>.mapError AllocError.memory
  return { state with initMask }

private def overwriteRawBytes (state : Allocation Prov Extra) (range : AllocRange)
    (bytes : Array UInt8) : Except AllocError (Allocation Prov Extra) := do
  let finish ← range.endExclusive |>.mapError AllocError.memory
  let start := range.start.bytes.toNat
  let endIndex := finish.bytes.toNat
  let updated := state.rawBytes.extract 0 start ++ bytes ++
    state.rawBytes.extract endIndex state.rawBytes.size
  if updated.size != state.size.bytes.toNat then
    throw (.storageLengthMismatch state.size updated.size)
  return { state with rawBytes := updated }

/-- Source `get_bytes_unchecked_for_overwrite`: mark bytes initialized and
clear any overlapping provenance before the caller writes new bytes. -/
private def prepareForOverwrite (range : AllocRange) (pointerSize : Size)
    (state : Allocation Prov Extra) :
    EStateM.Result AllocError (Allocation Prov Extra) Unit := Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if range.size.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let initialized ← if range.size.bytes == 0 then pure state else
    match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  return runProvenanceMutation
    (initialized.provenance.clear range initialized.rawBytes pointerSize) initialized

/-- Write a finite byte stream into this allocation. The array length is the
exact iterator length used by `write_bytes_ptr`; the range is derived from
that length, and bounds remain an explicit caller-side check. -/
def writeBytes (start : Size) (bytes : Array UInt8) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let writeSize ← match sizeForArray bytes.size with
    | .ok size => pure size
    | .error reason => return .error reason state
  let range := allocRange start writeSize
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if writeSize.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let initialized ← match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  let clearedResult := initialized.provenance.clear range initialized.rawBytes pointerSize
  let cleared ← match clearedResult with
    | .ok () provenance => pure { initialized with provenance }
    | .error reason provenance =>
        return .error (.provenance reason) { initialized with provenance }
  match overwriteRawBytes cleared range bytes with
  | .ok updated => return .ok () updated
  | .error reason => return .error reason cleared

/-- Write a repeated byte without materializing an input array. This is the
finite-array counterpart of rustc `write_bytes_ptr` with
`std::iter::repeat_n`: perform the same checked range, mutability,
initialization, and provenance transitions as `writeBytes`, then fill the
already allocated storage in place. -/
def writeRepeatedByte (start : Size) (byte : UInt8) (count : UInt64)
    (pointerSize : Size) : EStateM AllocError (Allocation Prov Extra) Unit :=
  fun state => Id.run do
    let range := allocRange start (Size.ofBytes count)
    match checkedSlice state range with
    | .error reason => return .error reason state
    | .ok _ => pure ()
    if count == 0 then return .ok () state
    if state.mutability != .Mut then return .error .readOnlyAllocation state
    let initialized ← match setInitialization state range true with
      | .ok initialized => pure initialized
      | .error reason => return .error reason state
    let clearedResult := initialized.provenance.clear range initialized.rawBytes pointerSize
    let cleared ← match clearedResult with
      | .ok () provenance => pure { initialized with provenance }
      | .error reason provenance =>
          return .error (.provenance reason) { initialized with provenance }
    let startIndex := start.bytes.toNat
    let mut bytes := cleared.rawBytes
    for offset in [:count.toNat] do
      let index := startIndex + offset
      if h : index < bytes.size then
        bytes := bytes.set index byte h
      else
        return .error (.invalidSliceEndpoints startIndex (index + 1) bytes.size) cleared
    return .ok () { cleared with rawBytes := bytes }

/-- Source `Allocation::write_uninit`: clear initialization first, then clear
overlapping provenance, while leaving the arbitrary byte representation alone. -/
def writeUninit (range : AllocRange) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if range.size.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let uninitialized ← match setInitialization state range false with
    | .ok uninitialized => pure uninitialized
    | .error reason => return .error reason state
  let cleared := uninitialized.provenance.clear range uninitialized.rawBytes pointerSize
  match cleared with
  | .ok () provenance => return .ok () { uninitialized with provenance }
  | .error reason provenance =>
      return .error (.provenance reason) { uninitialized with provenance }

/-- Source `Allocation::clear_provenance`: preserve bytes and initialization,
but remove or fragment all pointer provenance intersecting the checked range. -/
def clearProvenance (range : AllocRange) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  let cleared := state.provenance.clear range state.rawBytes pointerSize
  match cleared with
  | .ok () provenance => return .ok () { state with provenance }
  | .error reason provenance => return .error (.provenance reason) { state with provenance }

/-- Source `Allocation::process_native_write`: mark the selected range
initialized, then replace provenance in it with wildcard byte fragments. This
is intentionally available only to provenance types with a wildcard. Range
and mutability failures are explicit; a missing wildcard remains an error
after the source-ordered initialization transition. -/
def processNativeWrite [PointerProvenance Prov]
    (layout : TargetDataLayout) (range? : Option AllocRange) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let range := range?.getD (allocRange Size.ZERO state.size)
  if range.size.bytes != 0 then
    match checkedSlice state range with
    | .error _ => return .error (.nativeWriteRangeOutOfBounds range state.size) state
    | .ok _ => pure ()
  if range.size.bytes != 0 && state.mutability != .Mut then
    return .error .readOnlyAllocation state
  let initialized ← if range.size.bytes == 0 then pure state else
    match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  return runProvenanceMutation
    (initialized.provenance.writeWildcards range initialized.rawBytes (pointerSize layout))
    initialized

/-- Source `Allocation::provenance_merge_bytes`: attempt to coalesce complete
byte-fragment pointers. A `false` result may retain successful earlier
coalescings, exactly as the source map iteration does. -/
def provenanceMergeBytes [DecidableEq Prov]
    (layout : TargetDataLayout) :
    EStateM AllocError (Allocation Prov Extra) Bool := fun state => Id.run do
  match state.provenance.mergeBytes (pointerSize layout) with
  | .ok merged provenance => return .ok merged { state with provenance }
  | .error reason provenance => return .error (.provenance reason) { state with provenance }

/-- Source allocation-level half of `mem_copy_repeatedly`. Pointer resolution,
access checks, and machine hooks are supplied by the caller. The source's
initialization and provenance snapshots are prepared before destination
overwrite clears its old metadata. -/
def copyRepeatedly
    (source : Allocation Prov Extra) (sourceRange : AllocRange) (destStart : Size)
    (repeatCount : UInt64) (pointerSize : Size) (sameAllocation nonoverlapping : Bool) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let sourceBytes ← match checkedSlice source sourceRange with
    | .error reason => return .error reason state
    | .ok sourceBytes => pure sourceBytes
  let totalSize ← match Size.mul sourceRange.size repeatCount with
    | .ok size => pure size
    | .error reason => return .error (.memory (.sizeError reason)) state
  let destRange := allocRange destStart totalSize
  match checkedSlice state destRange with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  let provenance ← match source.provenance.prepareCopy sourceRange source.rawBytes pointerSize with
    | .ok copy => pure copy
    | .error reason => return .error (.provenance reason) state
  let initialized ← match source.initMask.prepareCopy sourceRange with
    | .ok copy => pure copy
    | .error reason => return .error (.memory reason) state
  let prepared := prepareForOverwrite destRange pointerSize state
  let afterClear ← match prepared with
    | .ok () updated => pure updated
    | .error reason updated => return .error reason updated
  if sameAllocation && nonoverlapping then
    let sourceFinish ← match sourceRange.endExclusive with
      | .ok finish => pure finish
      | .error reason => return .error (.memory reason) afterClear
    let firstDestFinish ← match (allocRange destStart totalSize).endExclusive with
      | .ok finish => pure finish
      | .error reason => return .error (.memory reason) afterClear
    if (sourceRange.start.bytes <= destStart.bytes && destStart.bytes < sourceFinish.bytes) ||
        (destStart.bytes <= sourceRange.start.bytes && sourceRange.start.bytes < firstDestFinish.bytes) then
      return .error .copyRangesOverlap afterClear
  if repeatCount > 1 && !nonoverlapping then
    return .error .repeatedCopyRequiresNonoverlapping afterClear
  if initialized.noBytesInit then
    let uninitResult := Allocation.writeUninit destRange pointerSize afterClear
    match uninitResult with
    | .error reason updated => return .error reason updated
    | .ok () updated => return .ok () updated
  if sourceRange.size.bytes == 1 && repeatCount == 0 && !initialized.noBytesInit then
    return .error .singleByteZeroCountCopy afterClear
  let mut copiedBytes := #[]
  for _ in [:repeatCount.toNat] do
    copiedBytes := copiedBytes ++ sourceBytes
  let afterBytes ← match overwriteRawBytes afterClear destRange copiedBytes with
    | .ok updated => pure updated
    | .error reason => return .error reason afterClear
  let afterInit ← match afterBytes.initMask.applyCopy initialized
      (allocRange destStart sourceRange.size) repeatCount with
    | .ok initMask => pure { afterBytes with initMask }
    | .error reason => return .error (.memory reason) afterBytes
  match afterInit.provenance.applyCopy provenance
      (allocRange destStart sourceRange.size) repeatCount with
  | .ok () provenance => return .ok () { afterInit with provenance }
  | .error reason provenance =>
      return .error (.provenance reason) { afterInit with provenance }

/-- The source `mem_copy` operation is a one-copy specialization. -/
def copy
    (source : Allocation Prov Extra) (sourceRange : AllocRange) (destStart : Size)
    (pointerSize : Size) (sameAllocation nonoverlapping : Bool) :
    EStateM AllocError (Allocation Prov Extra) Unit :=
  copyRepeatedly source sourceRange destStart 1 pointerSize sameAllocation nonoverlapping

/-- Source allocation mutability is a public field. This update preserves
all byte, initialization, provenance and allocation-extra state. -/
def withMutability (self : Allocation Prov Extra) (mutability : Mutability) :
    Allocation Prov Extra :=
  ⟨self.rawBytes, self.size, self.provenance, self.initMask, self.align, mutability, self.extra, self.nativeBuffer⟩

/-- Validated serialization boundary for an interned compiler allocation.
Unlike writes, importing its image does not initialize bytes, clear provenance,
or change the byte representation of pointers. -/
def fromCompilerImage (bytes : Array UInt8) (align : Align) (mutability : Mutability)
    (mask : InitMask) (provenance : ProvenanceMap CtfeProvenance) (pointerSize : Size) :
    Except AllocError (Allocation CtfeProvenance Unit) := do
  let align ← checkedAlign align
  let size ← sizeForArray bytes.size
  if mask.len != size then throw (.storageLengthMismatch size mask.len.bytes.toNat)
  for i in [:bytes.size] do
    let _ ← (mask.get (Size.ofBytes (UInt64.ofNat i))).mapError AllocError.memory
  if pointerSize.bytes == 0 then throw (.provenance .pointerSizeZero)
  if provenance.byteFragments.isSome then throw .allocationHasByteFragmentProvenance
  let _ ← (ProvenanceMap.fromPresortedPtrs provenance.ptrs).mapError AllocError.provenance
  let mut previousEnd := 0
  for (offset, _) in provenance.ptrs do
    let start := offset.bytes.toNat
    let finish := start + pointerSize.bytes.toNat
    if start < previousEnd then throw (.provenance .insertOverlapsExistingProvenance)
    if finish > bytes.size then throw (.outOfBounds (allocRange offset pointerSize) size)
    previousEnd := finish
  return ⟨bytes, size, provenance, mask, align, mutability, (), none⟩

end Allocation

end Miri.Memory

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
variable {P E E' : Type}
theorem writeScalar_mapExtra (layout : TargetDataLayout) (range : AllocRange)
    (value : Scalar P) (allocation : Allocation P E) (f : E → E') :
    Allocation.writeScalar layout range value (allocation.mapExtra f) =
      (match Allocation.writeScalar layout range value allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : Allocation.getBytesUnchecked (allocation.mapExtra f) range =
      Allocation.getBytesUnchecked allocation range := rfl
  unfold Allocation.getBytesUnchecked at slices
  unfold Allocation.writeScalar
  rw [slices]
  simp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  by_cases mutable : allocation.mutability = .Mut
  · cases converted : value.toBitsOrPtrInternal range.size <;>
      simp_all only [Allocation.mapExtra,mutable,beq_self_eq_true,Bool.not_true,↓reduceIte]
    all_goals repeat' (split <;> try simp_all [Allocation.mapExtra])
  · simp [Allocation.mapExtra,mutable]

theorem writeUninit_mapExtra (range : AllocRange) (pointerSize : Size)
    (allocation : Allocation P E) (f : E → E') :
    Allocation.writeUninit range pointerSize (allocation.mapExtra f) =
      (match Allocation.writeUninit range pointerSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : Allocation.getBytesUnchecked (allocation.mapExtra f) range =
      Allocation.getBytesUnchecked allocation range := rfl
  unfold Allocation.getBytesUnchecked at slices
  unfold Allocation.writeUninit
  rw [slices]
  unfold setInitialization
  simp only [Id.run,bind,Bind.bind,pure,Pure.pure,Except.mapError,Except.bind]
  cases mask : allocation.initializationMask.setRange range false <;>
    simp only [Allocation.initializationMask] at mask
  all_goals simp only [mask,Except.pure,Allocation.mapExtra]
  all_goals repeat' (split <;> try simp_all [Allocation.mapExtra,Except.pure])


end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
variable {P : Type}

theorem tryNew_uninit_image (size : Size) (align : Align) (pointerSize : Size)
    (allocation : Allocation P Unit) (positive : pointerSize.bytes ≠ 0)
    (created : Allocation.tryNew size align .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation) :
    allocation.len = size.bytes.toNat ∧
    ∃ initialized, Allocation.fromBytes (Array.replicate size.bytes.toNat 0) align .Mut = .ok initialized ∧
      Allocation.writeUninit (allocRange Size.ZERO size) pointerSize initialized =
        .ok () (if size.bytes = 0 then {allocation with initMask := InitMask.new size true} else allocation) := by
  unfold Allocation.tryNew at created
  cases checked : checkedAlign align with
  | error error => simp [checked,bind,Bind.bind,Except.bind] at created
  | ok normalized =>
    simp only [checked,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] at created
    simp only [Array.size_replicate] at created
    cases nz : firstNonZero (Array.replicate size.bytes.toNat 0) with
    | some pair => cases pair; simp_all [throw,MonadExceptOf.throw,throwThe]
    | none =>
      simp_all
      subst allocation
      refine ⟨by simp [Allocation.len],?_⟩
      refine ⟨⟨Array.replicate size.bytes.toNat 0,size,ProvenanceMap.new,
        InitMask.new size true,normalized,.Mut,(),none⟩,?_,?_⟩
      · have bound : ¬maxU64Nat < size.bytes.toNat := by
          unfold maxU64Nat
          have := size.bytes.toNat_lt
          omega
        have eta : Size.ofBytes size.bytes = size := by cases size; rfl
        unfold Allocation.fromBytes sizeForArray
        simp only [Array.size_replicate,bound,↓reduceIte]
        simp_all [eta,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
      · have endEq : (allocRange Size.ZERO size).endExclusive = .ok size := by
          cases size
          simp [AllocRange.endExclusive,AllocRange.end,allocRange,Size.ZERO,Size.add,Size.ofBytes,Except.mapError]
        unfold Allocation.writeUninit setInitialization checkedSlice
        simp only [Array.size_replicate]
        rw [endEq]
        simp only [bind,Bind.bind,Except.bind,Except.mapError,pure,Pure.pure,Except.pure,Id.run]
        simp only [allocRange,Size.ZERO,Size.ofBytes]
        simp only [UInt64.not_lt_zero,UInt64.lt_irrefl,↓reduceIte]
        have maskEq := InitMask.full_overwrite_stays_lazy size size true false (allocRange Size.ZERO size)
          endEq rfl (by exact UInt64.le_refl _)
        simp only [allocRange,Size.ZERO,Size.ofBytes] at maskEq
        rw [maskEq]
        by_cases zero : size.bytes = 0
        · simp [zero]
        · simp only [zero,↓reduceIte,Except.bind,Except.mapError,pure,Pure.pure,Except.pure]
          have cleared := ProvenanceMap.clear_new (P := P) (allocRange Size.ZERO size)
            (Array.replicate size.bytes.toNat 0) pointerSize size positive endEq
          simp only [allocRange,Size.ZERO,Size.ofBytes] at cleared
          rw [cleared]
          simp [zero,bind,Bind.bind,Except.bind,Except.mapError,pure,Pure.pure,Except.pure,Id.run]

end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
private theorem firstNonZero_replicate (n : Nat) : firstNonZero (Array.replicate n 0) = none := by
  let step : Nat → Option (Option (Nat × UInt8)) × Unit → Id (ForInStep (Option (Option (Nat × UInt8)) × Unit)) :=
    fun index _ => match (Array.replicate n 0)[index]? with
      | some byte => if byte != 0 then pure (.done (some (some (index,byte)),())) else pure (.yield (none,()))
      | none => pure (.done (some (some (index,0)),()))
  have scan : ∀ indices : List Nat, (∀ index ∈ indices, index < n) →
      forIn indices (none,()) step = (none,()) := by
    intro indices
    induction indices with
    | nil => intro good; rfl
    | cons head tail ih =>
      intro good
      have bound := good head (by simp)
      have atHead : (Array.replicate n (0 : UInt8))[head]? = some 0 := by simp [bound]
      rw [List.forIn_cons]
      simp only [step,atHead,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte,
        pure,Pure.pure,bind,Bind.bind]
      exact ih (by intro index member; exact good index (by simp [member]))
  simp only [firstNonZero]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Array.size_replicate,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  dsimp only [step,Id.run,pure,Pure.pure] at scan
  rw [scan (List.range' 0 n) (by intro index member; have := List.mem_range'.mp member; omega)]
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
variable {P : Type}

theorem tryNew_replicate (size : Size) (align : Align) (alignmentBytes : UInt64)
    (bytes : Align.bytes align = .ok alignmentBytes)
    (normalized : Align.fromBytes alignmentBytes = .ok align) :
    ∃ allocation : Allocation P Unit,
      Allocation.tryNew size align .Uninit (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation ∧
      allocation.byteSize = size ∧ allocation.len = size.bytes.toNat ∧
      allocation.nativeBuffer = none ∧ allocation.mutability = .Mut := by
  refine ⟨⟨Array.replicate size.bytes.toNat 0,size,ProvenanceMap.new,
    InitMask.new size false,align,.Mut,(),none⟩,?_,rfl,by simp [Allocation.len],rfl,rfl⟩
  simp [Allocation.tryNew,checkedAlign,bytes,normalized,firstNonZero_replicate,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Except.mapError]

end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
variable {P : Type}

theorem tryNew_replicate_full (size : Size) (align : Align) (alignmentBytes : UInt64)
    (bytes : Align.bytes align = .ok alignmentBytes)
    (normalized : Align.fromBytes alignmentBytes = .ok align) :
    ∃ allocation : Allocation P Unit,
      Allocation.tryNew size align .Uninit (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation ∧
      allocation.byteSize = size ∧ allocation.len = size.bytes.toNat ∧
      allocation.nativeBuffer = none ∧ allocation.mutability = .Mut ∧ allocation.align = align := by
  refine ⟨⟨Array.replicate size.bytes.toNat 0,size,ProvenanceMap.new,
    InitMask.new size false,align,.Mut,(),none⟩,?_,rfl,by simp [Allocation.len],rfl,rfl,rfl⟩
  simp [Allocation.tryNew,checkedAlign,bytes,normalized,firstNonZero_replicate,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Except.mapError]

end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem target_bytes_exists (layout : TargetDataLayout) (size : Size) (bits : U128)
    (limit : size.bytes.toNat ≤ 16) :
    ∃ bytes, targetUIntBytes layout size bits = .ok bytes ∧ bytes.size = size.bytes.toNat := by
  let step : Nat → Array UInt8 → Except AllocError (ForInStep (Array UInt8)) := fun index bytes =>
    let valueIndex := if layout.endian == .little then index else size.bytes.toNat-index-1
    pure (.yield (bytes.push (UInt8.ofNat ((bits.toNat / 2^(8*valueIndex)) % 256))))
  have build : ∀ (indices : List Nat) (initial : Array UInt8),
      ∃ bytes, forIn indices initial step = .ok bytes ∧ bytes.size = initial.size+indices.length := by
    intro indices
    induction indices with
    | nil => intro initial; exact ⟨initial,rfl,by simp⟩
    | cons index rest ih =>
      intro initial
      let byte := UInt8.ofNat ((bits.toNat / 2^(8*(if layout.endian == .little then index else size.bytes.toNat-index-1))) % 256)
      obtain ⟨bytes,ok,length⟩ := ih (initial.push byte)
      refine ⟨bytes,?_,?_⟩
      · simpa only [List.forIn_cons,step,byte,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] using ok
      · simp_all [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have small : ¬size.bytes > 16 := by
    simp only [UInt64.lt_iff_toNat_lt]
    simpa using Nat.not_lt.mpr limit
  unfold targetUIntBytes
  simp only [small,↓reduceIte,Std.Legacy.Range.forIn_eq_forIn_range']
  obtain ⟨bytes,ok,length⟩ := build (List.range' 0 [:size.bytes.toNat].size) #[]
  refine ⟨bytes,?_,?_⟩
  · dsimp only [step] at ok
    rw [ok]
    rfl
  · simpa using length
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
variable {P E : Type}
private theorem write_add_size (left right : Size)
    (fits : left.bytes.toNat+right.bytes.toNat < 2^64) :
    Size.add left right = .ok (Size.ofBytes (left.bytes+right.bytes)) := by
  have noWrap : ¬left.bytes+right.bytes < left.bytes := by
    simp only [UInt64.lt_iff_toNat_lt,UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    omega
  simp [Size.add,noWrap]

private theorem scalar_with_transitions (layout : TargetDataLayout)
    (allocation : Allocation P E) (range : AllocRange) (value : Scalar P)
    (converted : ScalarBitsOrPointer P) (cleared nextProvenance : ProvenanceMap P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0) (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat+range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal range.size = .ok converted)
    (clear : allocation.provenanceMap.clear range allocation.rawBytes (pointerSize layout) = .ok () cleared)
    (insert : match converted with
      | .bits _ => nextProvenance = cleared
      | .pointer pointer => range.size = pointerSize layout ∧
          cleared.insertPtr range.start pointer.provenance (pointerSize layout) = .ok () nextProvenance) :
    ∃ updated, Allocation.writeScalar layout range value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧ updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧ updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧ updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧ updated.provenanceMap = nextProvenance := by
  have fits : range.start.bytes.toNat+range.size.bytes.toNat < 2^64 := by
    have := allocation.byteSize.bytes.toNat_lt
    omega
  let finish := Size.ofBytes (range.start.bytes+range.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size range.start range.size fits)
  have finishNat : finish.bytes.toNat = range.start.bytes.toNat+range.size.bytes.toNat := by
    simp only [finish,Size.ofBytes,UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have positive : 0 < range.size.bytes.toNat := Nat.pos_of_ne_zero (by
    intro zero; exact nonzero (UInt64.toNat_inj.mp zero))
  obtain ⟨mask,maskOk,maskSize,maskWF⟩ := InitMask.WriteProof.set_range_exists allocation.initializationMask range finish true
    maskValid endpoint (by omega) (by rw [maskLength]; simpa only [finishNat] using bound)
  let bits := match converted with
    | .bits bits => bits
    | .pointer pointer => BitVec.ofNat 128 pointer.offset.bytes.toNat
  obtain ⟨data,dataOk,dataSize⟩ := target_bytes_exists layout range.size bits width
  let bytes := allocation.rawBytes.extract 0 range.start.bytes.toNat ++ data ++
    allocation.rawBytes.extract (range.start.bytes.toNat+range.size.bytes.toNat) allocation.rawBytes.size
  have startBound : range.start.bytes.toNat ≤ allocation.rawBytes.size := by
    change range.start.bytes.toNat ≤ allocation.len
    omega
  have endBound : finish.bytes.toNat ≤ allocation.rawBytes.size := by
    change finish.bytes.toNat ≤ allocation.len
    omega
  have bytesLength : bytes.size = allocation.byteSize.bytes.toNat := by
    simp only [bytes,Array.size_append,Array.size_extract,Nat.min_eq_left startBound,Nat.min_self,
      Nat.sub_zero,dataSize,Nat.min_eq_left (by omega : range.start.bytes.toNat+range.size.bytes.toNat ≤ allocation.rawBytes.size)]
    change _ = allocation.byteSize.bytes.toNat
    change allocation.rawBytes.size = allocation.byteSize.bytes.toNat at storage
    omega
  let updated : Allocation P E :=
    ⟨bytes,allocation.byteSize,nextProvenance,mask,allocation.align,allocation.mutability,allocation.extra,allocation.nativeBuffer⟩
  refine ⟨updated,?_,rfl,?_,rfl,rfl,rfl,rfl,maskSize,maskWF,rfl⟩
  · have slice : checkedSlice allocation range = .ok (allocation.rawBytes.extract range.start.bytes.toNat finish.bytes.toNat) := by
      unfold checkedSlice
      change allocation.rawBytes.size = allocation.size.bytes.toNat at storage
      simp [storage,endpoint,finishNat,UInt64.lt_iff_toNat_lt,bound,bind,Bind.bind,Except.bind,Except.mapError,pure,Pure.pure,Except.pure]
      exact bound
    simp only [Allocation.initializationMask] at maskOk
    simp only [Allocation.provenanceMap] at clear
    unfold Allocation.writeScalar
    simp only [mutable,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,conversion]
    simp only [Id.run,bind,Bind.bind,pure,Pure.pure]
    rw [slice,maskOk]
    simp only [bind,Bind.bind,pure,Pure.pure]
    rw [clear]
    simp only [bind,Bind.bind,pure,Pure.pure]
    dsimp only [bytes,Allocation.byteSize] at bytesLength
    cases converted with
    | bits payload =>
      dsimp only [bits] at dataOk
      rw [dataOk]
      simp only [bytesLength,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
      simp [insert,updated,bytes,mutable,bind,Bind.bind,pure,Pure.pure]
      rfl
    | pointer pointer =>
      dsimp only [bits] at dataOk
      rw [dataOk]
      simp only [bytesLength,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
      rcases insert with ⟨sizeEq,inserted⟩
      simp only [sizeEq,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
      rw [inserted]
      simp [updated,bytes,mutable,sizeEq]
      rfl
  · change bytes.size = allocation.len
    exact bytesLength.trans storage.symm
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
variable {P E : Type}
private def zeroPointer (provenance : P) : ProvenanceMap P :=
  match ProvenanceMap.insertPtr Size.ZERO provenance (Size.ofBytes 8) ProvenanceMap.new with
  | .ok _ state => state
  | .error _ state => state

/-- Successful physical first component write in fresh uninitialized storage.
All non-byte metadata is retained; only an optional zero-offset pointer entry
can be present for the subsequent disjoint component. -/
theorem writeScalar_fresh_zero (layout : TargetDataLayout) (allocation : Allocation P E) (value : Scalar P)
    (converted : ScalarBitsOrPointer P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (empty : allocation.provenanceMap = ProvenanceMap.new)
    (nonzero : value.size.bytes ≠ 0) (width : value.size.bytes.toNat ≤ 16)
    (bound : value.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (target : layout.pointerWidth = .w64)
    (pointerWidth : match converted with | .bits _ => True | .pointer _ => value.size = Size.fromBits layout.pointerWidth.bits)
    (conversion : value.toBitsOrPtrInternal value.size = .ok converted) :
    ∃ updated, Allocation.writeScalar layout (allocRange Size.ZERO value.size) value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧ updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧ updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧ updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      (updated.provenanceMap = ProvenanceMap.new ∨
        value.size = pointerSize layout ∧ ∃ provenance, updated.provenanceMap = zeroPointer provenance) := by
  have pointerDef : pointerSize layout = Size.fromBits layout.pointerWidth.bits := rfl
  simp only [←pointerDef] at pointerWidth
  have positive : (pointerSize layout).bytes ≠ 0 := by simp [pointerSize,target,PointerWidth.bits,Size.fromBits,Size.ofBytes]
  have endpoint : (allocRange Size.ZERO value.size).endExclusive = .ok value.size := by
    cases sized : value.size
    simp [allocRange,AllocRange.endExclusive,AllocRange.end,Size.ZERO,Size.ofBytes,Size.add,Except.mapError]
  have clear : allocation.provenanceMap.clear (allocRange Size.ZERO value.size) allocation.rawBytes (pointerSize layout) =
      .ok () ProvenanceMap.new := by
    rw [empty]
    exact ProvenanceMap.clear_new _ _ _ _ positive endpoint
  cases converted with
  | bits bits =>
    obtain ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,provenance⟩ :=
      scalar_with_transitions layout allocation (allocRange Size.ZERO value.size) value (.bits bits)
        ProvenanceMap.new ProvenanceMap.new storage mutable maskLength maskValid nonzero width
        (by simpa [allocRange,Size.ZERO,Size.ofBytes] using bound) conversion clear rfl
    exact ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,Or.inl provenance⟩
  | pointer pointer =>
    have inserted : ProvenanceMap.insertPtr Size.ZERO pointer.provenance (pointerSize layout) ProvenanceMap.new =
        .ok () (zeroPointer pointer.provenance) := by
      have ptr8 : pointerSize layout = Size.ofBytes 8 := by simp [pointerSize,target,PointerWidth.bits,Size.fromBits]
      have actual := ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8) pointer.provenance
        (by decide) (by decide)
      unfold zeroPointer
      rw [ptr8,actual]
    obtain ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,provenance⟩ :=
      scalar_with_transitions layout allocation (allocRange Size.ZERO value.size) value (.pointer pointer)
        ProvenanceMap.new (zeroPointer pointer.provenance) storage mutable maskLength maskValid nonzero width
        (by simpa [allocRange,Size.ZERO,Size.ofBytes] using bound) conversion clear ⟨pointerWidth,inserted⟩
    exact ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,
      Or.inr ⟨pointerWidth,pointer.provenance,provenance⟩⟩
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
variable {P E : Type}
/-- The second component writes a disjoint window of fresh storage. It keeps
an earlier pointer entry intact and derives every provenance operation. -/
theorem writeScalar_separated (layout : TargetDataLayout) (allocation : Allocation P E) (offset : Size)
    (value : Scalar P) (converted : ScalarBitsOrPointer P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat) (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (separated : allocation.provenanceMap = ProvenanceMap.new ∨
      ∃ provenance, allocation.provenanceMap = zeroPointer provenance ∧
        (pointerSize layout).bytes.toNat ≤ offset.bytes.toNat)
    (nonzero : value.size.bytes ≠ 0) (width : value.size.bytes.toNat ≤ 16)
    (bound : offset.bytes.toNat+value.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (target : layout.pointerWidth = .w64)
    (pointerWidth : match converted with | .bits _ => True | .pointer _ => value.size = Size.fromBits layout.pointerWidth.bits)
    (conversion : value.toBitsOrPtrInternal value.size = .ok converted) :
    ∃ updated, Allocation.writeScalar layout (allocRange offset value.size) value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧ updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧ updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧ updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask := by
  have pointerDef : pointerSize layout = Size.fromBits layout.pointerWidth.bits := rfl
  simp only [←pointerDef] at pointerWidth
  let range := allocRange offset value.size
  have fits : offset.bytes.toNat+value.size.bytes.toNat < 2^64 := by have := allocation.byteSize.bytes.toNat_lt; omega
  let finish := Size.ofBytes (offset.bytes+value.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end range allocRange
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size offset value.size fits)
  have ptr8 : pointerSize layout = Size.ofBytes 8 := by simp [pointerSize,target,PointerWidth.bits,Size.fromBits]
  have positive : (pointerSize layout).bytes ≠ 0 := by rw [ptr8]; decide
  have clear : allocation.provenanceMap.clear range allocation.rawBytes (pointerSize layout) =
      .ok () allocation.provenanceMap := by
    rcases separated with empty | ⟨old,present,before⟩
    · rw [empty]; exact ProvenanceMap.clear_new _ _ _ _ positive endpoint
    · have initial := ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8) old
        (by decide) (by decide)
      unfold zeroPointer at present
      rw [initial] at present
      dsimp only at present
      rw [present]
      exact ProvenanceMap.clear_singleton_before range allocation.rawBytes (pointerSize layout) finish old
        positive before endpoint
  cases converted with
  | bits bits =>
    obtain ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,_⟩ :=
      scalar_with_transitions layout allocation range value (.bits bits) allocation.provenanceMap allocation.provenanceMap
        storage mutable maskLength maskValid nonzero width bound conversion clear rfl
    exact ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid⟩
  | pointer pointer =>
    have insertExists : ∃ next, allocation.provenanceMap.insertPtr offset pointer.provenance (pointerSize layout) =
        .ok () next := by
      rcases separated with empty | ⟨old,present,before⟩
      · rw [empty]
        have actual := ProvenanceMap.insertPtr_new offset (pointerSize layout) finish pointer.provenance positive
          (by simpa only [range,pointerWidth] using endpoint)
        let next := match ProvenanceMap.insertPtr offset pointer.provenance (pointerSize layout) ProvenanceMap.new with
          | .ok _ state => state | .error _ state => state
        refine ⟨next,?_⟩
        dsimp only [next]
        rw [actual]
      · have initial := ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8) old
          (by decide) (by decide)
        unfold zeroPointer at present
        rw [initial] at present
        dsimp only at present
        rw [present]
        exact ProvenanceMap.insertPtr_singleton_after offset (pointerSize layout) finish old pointer.provenance
          positive before (by simpa only [range,pointerWidth] using endpoint)
    obtain ⟨next,inserted⟩ := insertExists
    obtain ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,_⟩ :=
      scalar_with_transitions layout allocation range value (.pointer pointer) allocation.provenanceMap next
        storage mutable maskLength maskValid nonzero width bound conversion clear ⟨pointerWidth,inserted⟩
    exact ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid⟩
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
variable {P : Type}
theorem tryNew_uninit_shape (size : Size) (align : Align) (allocation : Allocation P Unit)
    (created : Allocation.tryNew size align .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation) :
    allocation.provenanceMap = ProvenanceMap.new ∧ allocation.initializationMask = InitMask.new size false := by
  unfold tryNew at created
  cases checked : checkedAlign align with
  | error error => simp [checked,bind,Bind.bind,Except.bind] at created
  | ok normalized =>
    simp [checked,firstNonZero_replicate,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] at created
    subst allocation
    exact ⟨rfl,rfl⟩
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation.Bridge

open Miri.ABI
open Miri.Memory
open Miri.Memory.Allocation

set_option autoImplicit false

variable {P E E' : Type}

/-! Minimal equation and step bridges exposing module-private helpers
(`Allocation.mk`, `rawBytes`, `checkedSlice`, `checkedAlign`, `sizeForArray`,
`pointerSize`, `targetUIntBytes`, `readTargetUInt`, `setInitialization`,
`overwriteRawBytes`, `prepareForOverwrite`) in terms of public operations for
`Miri.Memory.AllocationVerification`. -/

private theorem full_range_endExclusive (sz : Size) :
    (allocRange Size.ZERO sz).endExclusive = .ok sz := by
  cases sz
  simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]

private theorem checkedSlice_ok (allocation : Allocation P E) (range : AllocRange) (finish : Size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    checkedSlice allocation range =
      .ok (allocation.rawBytes.extract range.start.bytes.toNat finish.bytes.toNat) := by
  unfold checkedSlice
  change allocation.rawBytes.size = allocation.size.bytes.toNat at storage
  have h_not_s : ¬(finish.bytes < range.start.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr startLe)
  have h_not_f : ¬(allocation.size.bytes < finish.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr inBounds)
  simp only [storage, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, endEq, Except.mapError,
    Bind.bind, Except.bind, gt_iff_lt, h_not_s, h_not_f, decide_false, Bool.or_self,
    Pure.pure, Except.pure]

private theorem getBytesUnchecked_full_raw (allocation : Allocation P E)
    (storage : allocation.len = allocation.byteSize.bytes.toNat) :
    allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok allocation.rawBytes := by
  unfold Allocation.getBytesUnchecked
  rw [checkedSlice_ok allocation (allocRange Size.ZERO allocation.byteSize) allocation.byteSize
    storage (full_range_endExclusive allocation.byteSize) (Nat.zero_le _) (Nat.le_refl _)]
  dsimp only [allocRange]
  have h_zero : Size.ZERO.bytes.toNat = 0 := rfl
  rw [h_zero, ← storage]
  exact congrArg Except.ok (Array.extract_size (xs := allocation.rawBytes))

/-- An allocation whose backing length matches `byteSize` returns its full byte
array on the full range `[0, byteSize)`. -/
theorem getBytesUnchecked_full_exists (allocation : Allocation P E)
    (storage : allocation.len = allocation.byteSize.bytes.toNat) :
    ∃ fullBytes,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes ∧
      fullBytes.size = allocation.byteSize.bytes.toNat :=
  ⟨allocation.rawBytes, getBytesUnchecked_full_raw allocation storage, storage⟩

/-- Any successful `getBytesUnchecked` call implies storage-length consistency
and in-bounds endpoints. -/
theorem getBytesUnchecked_ok_bounds (allocation : Allocation P E) (range : AllocRange)
    (finish : Size) (bytes : Array UInt8)
    (endEq : range.endExclusive = .ok finish)
    (h_ok : allocation.getBytesUnchecked range = .ok bytes) :
    allocation.len = allocation.byteSize.bytes.toNat ∧
    range.start.bytes.toNat ≤ finish.bytes.toNat ∧
    finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat := by
  unfold Allocation.getBytesUnchecked checkedSlice at h_ok
  by_cases h_mis : allocation.rawBytes.size != allocation.size.bytes.toNat
  · simp only [h_mis, ↓reduceIte, throw, MonadExceptOf.throw, throwThe, Bind.bind, Except.bind] at h_ok
    cases h_ok
  · have h_raw : allocation.rawBytes.size = allocation.size.bytes.toNat := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_mis; exact h_mis
    simp only [h_mis, Bool.false_eq_true, ↓reduceIte, endEq, Except.mapError, Bind.bind, Except.bind] at h_ok
    by_cases h_oob : range.start.bytes > finish.bytes || finish.bytes > allocation.size.bytes
    · simp only [h_oob, ↓reduceIte, throw, MonadExceptOf.throw, throwThe] at h_ok
      cases h_ok
    · simp only [Bool.or_eq_true, not_or, decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt] at h_oob
      exact ⟨h_raw, Nat.le_of_not_lt h_oob.1, Nat.le_of_not_lt h_oob.2⟩

/-- Expresses any in-bounds `getBytesUnchecked` slice as `Array.extract` over
the full byte snapshot returned on `[0, byteSize)`. -/
theorem getBytesUnchecked_eq_extract (allocation : Allocation P E) (range : AllocRange)
    (finish : Size) (fullBytes : Array UInt8)
    (h_full : allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    allocation.getBytesUnchecked range =
      .ok (fullBytes.extract range.start.bytes.toNat finish.bytes.toNat) := by
  have storage : allocation.len = allocation.byteSize.bytes.toNat :=
    (getBytesUnchecked_ok_bounds allocation _ allocation.byteSize fullBytes
      (full_range_endExclusive allocation.byteSize) h_full).1
  have h_eq : fullBytes = allocation.rawBytes :=
    Except.ok.inj (h_full.symm.trans (getBytesUnchecked_full_raw allocation storage))
  subst h_eq
  exact checkedSlice_ok allocation range finish storage endEq startLe inBounds

private theorem setInitialization_mapExtra (allocation : Allocation P E) (range : AllocRange)
    (initialized : Bool) (f : E → E') :
    setInitialization (allocation.mapExtra f) range initialized =
      (setInitialization allocation range initialized).map (·.mapExtra f) := by
  unfold setInitialization
  dsimp only [Allocation.mapExtra]
  cases allocation.initMask.setRange range initialized <;> rfl

private theorem overwriteRawBytes_mapExtra (allocation : Allocation P E) (range : AllocRange)
    (bytes : Array UInt8) (f : E → E') :
    overwriteRawBytes (allocation.mapExtra f) range bytes =
      (overwriteRawBytes allocation range bytes).map (·.mapExtra f) := by
  unfold overwriteRawBytes
  cases range.endExclusive with
  | error _ => rfl
  | ok fin =>
    dsimp only [Allocation.mapExtra, Except.mapError, Bind.bind, Except.bind]
    by_cases h_sz : ((allocation.rawBytes.extract 0 range.start.bytes.toNat ++ bytes ++
        allocation.rawBytes.extract fin.bytes.toNat allocation.rawBytes.size).size !=
        allocation.size.bytes.toNat) = true
    · simp only [h_sz, ↓reduceIte]; rfl
    · simp only [h_sz]; rfl

/-- `writeBytes` commutes with `mapExtra` on both success and failure states. -/
theorem writeBytes_mapExtra_bridge (start : Size) (bytes : Array UInt8) (ptrSize : Size)
    (allocation : Allocation P E) (f : E → E') :
    Allocation.writeBytes start bytes ptrSize (allocation.mapExtra f) =
      (match Allocation.writeBytes start bytes ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : ∀ r, checkedSlice (allocation.mapExtra f) r = checkedSlice allocation r := fun _ => rfl
  unfold Allocation.writeBytes
  dsimp only [Id.run, Bind.bind, Pure.pure]
  cases sizeForArray bytes.size with
  | error _ => rfl
  | ok writeSize =>
    dsimp only
    rw [slices]
    cases checkedSlice allocation (allocRange start writeSize) with
    | error _ => rfl
    | ok _ =>
      dsimp only
      by_cases h0 : (writeSize.bytes == 0) = true
      · rw [ite_eq_left h0, ite_eq_left h0]
      · rw [ite_eq_right h0, ite_eq_right h0]
        change (if (allocation.mutability != .Mut) = true then _ else _) = _
        by_cases hm : (allocation.mutability != .Mut) = true
        · rw [ite_eq_left hm, ite_eq_left hm]
        · rw [ite_eq_right hm, ite_eq_right hm, setInitialization_mapExtra]
          cases setInitialization allocation (allocRange start writeSize) true with
          | error _ => rfl
          | ok initAlloc =>
            dsimp only [Except.map, Allocation.mapExtra]
            cases initAlloc.provenance.clear (allocRange start writeSize) initAlloc.rawBytes ptrSize with
            | error _ _ => rfl
            | ok _ prov =>
              dsimp only
              have h_ov := overwriteRawBytes_mapExtra { initAlloc with provenance := prov }
                (allocRange start writeSize) bytes f
              dsimp only [Allocation.mapExtra] at h_ov
              rw [h_ov]
              cases overwriteRawBytes { initAlloc with provenance := prov } (allocRange start writeSize) bytes <;> rfl

/-- `clearProvenance` commutes with `mapExtra` on both success and failure states. -/
theorem clearProvenance_mapExtra_bridge (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (f : E → E') :
    Allocation.clearProvenance range ptrSize (allocation.mapExtra f) =
      (match Allocation.clearProvenance range ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : checkedSlice (allocation.mapExtra f) range = checkedSlice allocation range := rfl
  unfold Allocation.clearProvenance
  rw [slices]
  simp only [Id.run, Pure.pure, Allocation.mapExtra]
  cases checkedSlice allocation range with
  | error _ => rfl
  | ok _ =>
    dsimp only
    cases allocation.provenance.clear range allocation.rawBytes ptrSize <;> rfl

/-- Field and full-byte characterization of a successful `Allocation.fromBytes`. -/
theorem fromBytes_ok_bridge (bytes : Array UInt8) (align : Align) (mutability : Mutability)
    (alloc : Allocation P Unit)
    (created : Allocation.fromBytes bytes align mutability = .ok alloc) :
    alloc.byteSize.bytes.toNat = bytes.size ∧
      alloc.len = bytes.size ∧
      alloc.mutability = mutability ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      alloc.initializationMask = InitMask.new alloc.byteSize true ∧
      alloc.getBytesUnchecked (allocRange Size.ZERO alloc.byteSize) = .ok bytes := by
  unfold Allocation.fromBytes at created
  cases h_al : checkedAlign align with
  | error _ => simp only [h_al, Bind.bind, Except.bind] at created; cases created
  | ok _ =>
    simp only [h_al, Bind.bind, Except.bind] at created
    cases h_sz : sizeForArray bytes.size with
    | error _ => simp only [h_sz] at created; cases created
    | ok sz =>
      simp only [h_sz] at created
      by_cases h_eq : bytes.size = sz.bytes.toNat
      · simp only [h_eq, ↓reduceDIte, Pure.pure, Except.pure, Except.ok.injEq] at created
        subst created
        exact ⟨h_eq.symm, rfl, rfl, rfl, rfl, rfl, rfl, getBytesUnchecked_full_raw _ h_eq⟩
      · simp only [h_eq, ↓reduceDIte, throw, MonadExceptOf.throw, throwThe] at created; cases created

/-- Existence witness bridge for `Allocation.fromBytes`. -/
theorem fromBytes_exists_bridge (bytes : Array UInt8) (align : Align) (alignmentBytes : UInt64)
    (mutability : Mutability)
    (h_bytes : Align.bytes align = .ok alignmentBytes)
    (h_norm : Align.fromBytes alignmentBytes = .ok align)
    (h_fits : bytes.size < 2 ^ 64) :
    ∃ alloc : Allocation P Unit,
      Allocation.fromBytes bytes align mutability = .ok alloc ∧
      alloc.byteSize = Size.ofBytes (UInt64.ofNat bytes.size) ∧
      alloc.align = align := by
  have h_ca : checkedAlign align = .ok align := by
    unfold checkedAlign
    simp only [h_bytes, h_norm, Except.mapError, Bind.bind, Except.bind, beq_self_eq_true,
      ↓reduceIte, Pure.pure, Except.pure]
  have h_not_gt : ¬(bytes.size > maxU64Nat) := Nat.not_lt.mpr (Nat.le_of_lt_succ h_fits)
  have h_tonat : (Size.ofBytes (UInt64.ofNat bytes.size)).bytes.toNat = bytes.size := by
    simp only [Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_fits]
  have h_sfa : sizeForArray bytes.size = .ok (Size.ofBytes (UInt64.ofNat bytes.size)) := by
    unfold sizeForArray
    simp only [h_not_gt, ↓reduceIte, h_tonat, beq_self_eq_true, Pure.pure, Except.pure]
  refine ⟨⟨bytes, Size.ofBytes (UInt64.ofNat bytes.size), ProvenanceMap.new,
    InitMask.new (Size.ofBytes (UInt64.ofNat bytes.size)) true, align, mutability, (), none⟩,
    ?_, rfl, rfl⟩
  unfold Allocation.fromBytes
  simp only [h_ca, h_sfa, h_tonat, ↓reduceDIte, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Field and full-byte characterization of a successful `Allocation.tryNew`
backed by `Array.replicate`. -/
theorem tryNew_ok_bridge (size : Size) (align : Align) (init : AllocInit)
    (alloc : Allocation P Unit)
    (created : Allocation.tryNew size align init
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc) :
    alloc.byteSize = size ∧
      alloc.len = size.bytes.toNat ∧
      alloc.mutability = .Mut ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      (init = .Uninit → alloc.initializationMask = InitMask.new size false) ∧
      (init = .Zero → alloc.initializationMask = InitMask.new size true) ∧
      alloc.getBytesUnchecked (allocRange Size.ZERO alloc.byteSize) =
        .ok (Array.replicate size.bytes.toNat 0) := by
  unfold Allocation.tryNew at created
  cases h_al : checkedAlign align with
  | error _ => simp only [h_al, Bind.bind, Except.bind] at created; cases created
  | ok normAlign =>
    simp only [h_al, Array.size_replicate, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      ↓reduceDIte, firstNonZero_replicate, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Except.ok.injEq] at created
    subst created
    exact ⟨rfl, Array.size_replicate, rfl, rfl, rfl, rfl,
      fun h => by subst h; rfl, fun h => by subst h; rfl,
      getBytesUnchecked_full_raw _ Array.size_replicate⟩

/-- Existence witness bridge for `Allocation.tryNew` backed by `Array.replicate`. -/
theorem tryNew_exists_bridge (size : Size) (align : Align) (alignmentBytes : UInt64) (init : AllocInit)
    (h_bytes : Align.bytes align = .ok alignmentBytes)
    (h_norm : Align.fromBytes alignmentBytes = .ok align) :
    ∃ alloc : Allocation P Unit,
      Allocation.tryNew size align init
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc ∧
      alloc.align = align := by
  have h_ca : checkedAlign align = .ok align := by
    unfold checkedAlign
    simp only [h_bytes, h_norm, Except.mapError, Bind.bind, Except.bind, beq_self_eq_true,
      ↓reduceIte, Pure.pure, Except.pure]
  refine ⟨⟨Array.replicate size.bytes.toNat 0, size, ProvenanceMap.new,
    InitMask.new size (match init with | .Uninit => false | .Zero => true), align, .Mut, (), none⟩,
    ?_, rfl⟩
  unfold Allocation.tryNew
  simp only [h_ca, Array.size_replicate, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    ↓reduceDIte, firstNonZero_replicate, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Bridge for `getBytesStripProvenance` when `isRangeInitialized` reports an
uninitialized subrange. -/
theorem getBytesStripProvenance_uninit_bridge [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange)
    (h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    allocation.getBytesStripProvenance layout range =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  unfold Allocation.getBytesStripProvenance
  have h' : allocation.initMask.isRangeInitialized range = .ok (.error bad) := h_uninit
  rw [h']
  rfl

/-- Bridge for `getBytesStripProvenance` on an initialized, provenance-safe range. -/
theorem getBytesStripProvenance_ok_bridge [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range : AllocRange)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.getBytesStripProvenance layout range = allocation.getBytesUnchecked range := by
  unfold Allocation.getBytesStripProvenance Allocation.getBytesUnchecked pointerSize
  have hi : allocation.initMask.isRangeInitialized range = .ok (.ok ()) := h_init
  rw [hi]
  rcases h_prov with h_addr | h_empty
  · simp only [h_addr, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Except.mapError, Bind.bind, Except.bind]
  · by_cases h_addr : PointerProvenance.offsetIsAddr (Prov := P) = true
    · simp only [h_addr, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Except.mapError, Bind.bind, Except.bind]
    · have h_addr_f : PointerProvenance.offsetIsAddr (Prov := P) = false :=
        Bool.eq_false_iff.mpr h_addr
      have he : allocation.provenance.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true := h_empty
      simp only [h_addr_f, Bool.not_false, ↓reduceIte, he, Bool.not_true, Bool.false_eq_true,
        Except.mapError, Bind.bind, Except.bind]

/-- Definitional bridge exposing `readScalar` (including `readTargetUInt`) in
terms of public accessors and stdlib loop operations. -/
theorem readScalar_eq [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    allocation.readScalar layout range readProvenance =
      let readUInt (bytes : Array UInt8) : Except AllocError U128 := do
        if bytes.size > 16 then throw (.scalarBytesTooWide (Size.ofBytes (UInt64.ofNat bytes.size)))
        let mut value := 0
        for index in [:bytes.size] do
          let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
          let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
          value := value + byte.toNat * 2 ^ (8 * valueIndex)
        return BitVec.ofNat 128 value
      (do
        match ← (allocation.initializationMask.isRangeInitialized range).mapError AllocError.memory with
        | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
        | .ok () => pure ()
        let bytes ← allocation.getBytesUnchecked range
        let bits ← readUInt bytes
        if readProvenance then
          let targetSize := Size.fromBits layout.pointerWidth.bits
          if range.size != targetSize then
            throw (.scalarPointerNotTargetSized range.size targetSize)
          let provenance ← match allocation.provenanceMap.readPtr range.start targetSize with
            | .ok provenance => pure provenance
            | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
            | .error reason => throw (.provenance reason)
          match provenance with
          | some provenance =>
            if bits.toNat > 18446744073709551615 then
              throw (.pointerBitsDoNotFitOffset bits)
            return Scalar.fromPointer layout
              (Pointer.new provenance (Size.ofBytes (UInt64.ofNat bits.toNat)))
          | none =>
            let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
            return scalar
        else
          if PointerProvenance.offsetIsAddr (Prov := P) then
            let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
            return scalar
          let isEmpty ← (allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits)).mapError AllocError.provenance
          if isEmpty then
            let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
            return scalar
          throw (.readPointerAsInt none)) :=
  rfl

/-- Step bridge for `Allocation.writeScalar` once initialization, provenance,
endian serialization, and spliced-length side conditions are discharged. -/
theorem writeScalar_step_bridge (layout : TargetDataLayout)
    (allocation : Allocation P E) (range : AllocRange) (value : Scalar P)
    (converted : ScalarBitsOrPointer P) (bits : U128) (nextMask : InitMask)
    (cleared nextProvenance : ProvenanceMap P)
    (fullBytes sliceBytes data : Array UInt8)
    (h_bits : bits = match converted with
      | .bits b => b
      | .pointer p => BitVec.ofNat 128 p.offset.bytes.toNat)
    (h_full : allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes)
    (h_mut : allocation.mutability = .Mut)
    (h_conv : value.toBitsOrPtrInternal range.size = .ok converted)
    (h_slice : allocation.getBytesUnchecked range = .ok sliceBytes)
    (h_mask : allocation.initializationMask.setRange range true = .ok nextMask)
    (h_clear : allocation.provenanceMap.clear range fullBytes (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (h_data :
      (do
        if range.size.bytes > 16 then throw (.scalarBytesTooWide range.size)
        let count := range.size.bytes.toNat
        let mut result := #[]
        for index in [:count] do
          let valueIndex := if layout.endian == .little then index else count - index - 1
          let byte := (bits.toNat / 2 ^ (8 * valueIndex)) % 256
          result := result.push (UInt8.ofNat byte)
        return result : Except AllocError (Array UInt8)) = .ok data)
    (h_spliced_sz :
      (fullBytes.extract 0 range.start.bytes.toNat ++ data ++
        fullBytes.extract (range.start.bytes.toNat + range.size.bytes.toNat) fullBytes.size).size =
        allocation.byteSize.bytes.toNat)
    (h_insert : match converted with
      | .bits _ => nextProvenance = cleared
      | .pointer pointer => range.size = Size.fromBits layout.pointerWidth.bits ∧
          cleared.insertPtr range.start pointer.provenance
            (Size.fromBits layout.pointerWidth.bits) = .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeScalar layout range value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask = nextMask ∧
      updated.provenanceMap = nextProvenance ∧
      updated.getBytesUnchecked (allocRange Size.ZERO updated.byteSize) =
        .ok (fullBytes.extract 0 range.start.bytes.toNat ++ data ++
          fullBytes.extract (range.start.bytes.toNat + range.size.bytes.toNat) fullBytes.size) := by
  have storage : allocation.len = allocation.byteSize.bytes.toNat :=
    (getBytesUnchecked_ok_bounds allocation _ allocation.byteSize fullBytes
      (full_range_endExclusive allocation.byteSize) h_full).1
  have h_raw_eq : fullBytes = allocation.rawBytes :=
    Except.ok.inj (h_full.symm.trans (getBytesUnchecked_full_raw allocation storage))
  subst h_raw_eq
  let spliced := allocation.rawBytes.extract 0 range.start.bytes.toNat ++ data ++
    allocation.rawBytes.extract (range.start.bytes.toNat + range.size.bytes.toNat) allocation.rawBytes.size
  let updated : Allocation P E :=
    ⟨spliced, allocation.byteSize, nextProvenance, nextMask, allocation.align,
      allocation.mutability, allocation.extra, allocation.nativeBuffer⟩
  refine ⟨updated, ?_, rfl, h_spliced_sz.trans storage.symm, rfl, rfl, rfl, rfl, rfl, rfl,
    getBytesUnchecked_full_raw updated h_spliced_sz⟩
  have h_slice' : checkedSlice allocation range = .ok sliceBytes := h_slice
  have h_mask' : allocation.initMask.setRange range true = .ok nextMask := h_mask
  have h_clear' : allocation.provenance.clear range allocation.rawBytes (pointerSize layout) = .ok () cleared := h_clear
  have h_data' : targetUIntBytes layout range.size bits = .ok data := h_data
  have h_sz_bne : ¬((spliced.size != allocation.size.bytes.toNat) = true) := by
    have h : (spliced.size != allocation.byteSize.bytes.toNat) = false := by
      rw [h_spliced_sz]; exact bne_self_eq_false _
    change (spliced.size != allocation.byteSize.bytes.toNat) ≠ true
    rw [h]; exact Bool.false_ne_true
  dsimp only [spliced] at h_sz_bne
  unfold Allocation.writeScalar
  dsimp only [Id.run, Bind.bind, Pure.pure]
  rw [ite_eq_right (by rw [h_mut]; exact Bool.false_ne_true), h_conv]
  dsimp only
  rw [h_slice']
  dsimp only
  rw [h_mask']
  dsimp only
  rw [h_clear']
  dsimp only
  cases converted with
  | bits _ =>
    dsimp only at h_bits h_insert
    subst h_bits
    dsimp only
    rw [h_data']
    dsimp only
    rw [ite_eq_right h_sz_bne]
    dsimp only [updated, spliced]; rw [h_mut, h_insert]; rfl
  | pointer pointer =>
    dsimp only at h_bits h_insert
    subst h_bits
    dsimp only
    rw [h_data']
    dsimp only
    rw [ite_eq_right h_sz_bne]
    rcases h_insert with ⟨sizeEq, inserted⟩
    have h_psz : ¬((range.size != pointerSize layout) = true) := by
      change (range.size != Size.fromBits layout.pointerWidth.bits) ≠ true
      rw [sizeEq, bne_self_eq_false]; exact Bool.false_ne_true
    have h_ins' : cleared.insertPtr range.start pointer.provenance (pointerSize layout) = .ok () nextProvenance := inserted
    rw [ite_eq_right h_psz]
    rw [h_ins']
    dsimp only [updated, spliced]; rw [h_mut]; rfl

/-- Step bridge for `Allocation.writeBytes` on an empty byte array. -/
theorem writeBytes_zero_bridge (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Allocation P E)
    (h_empty : bytes.size = 0)
    (h_slice : allocation.getBytesUnchecked (allocRange start Size.ZERO) = .ok #[]) :
    Allocation.writeBytes start bytes ptrSize allocation = .ok () allocation := by
  have h_sfa : sizeForArray 0 = .ok Size.ZERO := rfl
  have h_slice' : checkedSlice allocation (allocRange start Size.ZERO) = .ok #[] := h_slice
  unfold Allocation.writeBytes
  rw [h_empty, h_sfa]
  simp only [Id.run, Bind.bind, Pure.pure, h_slice']
  rfl

/-- Step bridge for nonempty `Allocation.writeBytes`. -/
theorem writeBytes_step_bridge (start ptrSize finish : Size) (bytes : Array UInt8)
    (allocation : Allocation P E) (nextMask : InitMask) (nextProvenance : ProvenanceMap P)
    (fullBytes sliceBytes : Array UInt8)
    (h_full : allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes)
    (h_fits : bytes.size < 2 ^ 64)
    (h_nz : bytes.size ≠ 0)
    (h_slice : allocation.getBytesUnchecked (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) = .ok sliceBytes)
    (h_mut : allocation.mutability = .Mut)
    (h_mask : allocation.initializationMask.setRange
      (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) true = .ok nextMask)
    (h_clear : allocation.provenanceMap.clear
      (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) fullBytes ptrSize = .ok () nextProvenance)
    (h_end : (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))).endExclusive = .ok finish)
    (h_spliced_sz :
      (fullBytes.extract 0 start.bytes.toNat ++ bytes ++
        fullBytes.extract finish.bytes.toNat fullBytes.size).size = allocation.byteSize.bytes.toNat) :
    ∃ updated,
      Allocation.writeBytes start bytes ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask = nextMask ∧
      updated.provenanceMap = nextProvenance ∧
      updated.getBytesUnchecked (allocRange Size.ZERO updated.byteSize) =
        .ok (fullBytes.extract 0 start.bytes.toNat ++ bytes ++
          fullBytes.extract finish.bytes.toNat fullBytes.size) := by
  have storage : allocation.len = allocation.byteSize.bytes.toNat :=
    (getBytesUnchecked_ok_bounds allocation _ allocation.byteSize fullBytes
      (full_range_endExclusive allocation.byteSize) h_full).1
  have h_raw_eq : fullBytes = allocation.rawBytes :=
    Except.ok.inj (h_full.symm.trans (getBytesUnchecked_full_raw allocation storage))
  subst h_raw_eq
  let writeSize := Size.ofBytes (UInt64.ofNat bytes.size)
  have h_not_gt : ¬(bytes.size > maxU64Nat) := Nat.not_lt.mpr (Nat.le_of_lt_succ h_fits)
  have h_tonat : (Size.ofBytes (UInt64.ofNat bytes.size)).bytes.toNat = bytes.size := by
    simp only [Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_fits]
  have h_sfa : sizeForArray bytes.size = .ok writeSize := by
    unfold sizeForArray
    simp only [h_not_gt, ↓reduceIte, h_tonat, beq_self_eq_true, Pure.pure, Except.pure]
    rfl
  have h_wsz_nz : (writeSize.bytes == 0) = false :=
    beq_false_of_ne (fun h0 => h_nz (h_tonat.symm.trans (congrArg UInt64.toNat h0)))
  let spliced := allocation.rawBytes.extract 0 start.bytes.toNat ++ bytes ++
    allocation.rawBytes.extract finish.bytes.toNat allocation.rawBytes.size
  let updated : Allocation P E :=
    ⟨spliced, allocation.byteSize, nextProvenance, nextMask, allocation.align,
      allocation.mutability, allocation.extra, allocation.nativeBuffer⟩
  refine ⟨updated, ?_, rfl, h_spliced_sz.trans storage.symm, rfl, rfl, rfl, rfl, rfl, rfl,
    getBytesUnchecked_full_raw updated h_spliced_sz⟩
  have h_slice' : checkedSlice allocation (allocRange start writeSize) = .ok sliceBytes := h_slice
  have h_mask' : allocation.initMask.setRange (allocRange start writeSize) true = .ok nextMask := h_mask
  have h_clear' : allocation.provenance.clear (allocRange start writeSize) allocation.rawBytes ptrSize = .ok () nextProvenance := h_clear
  have h_end' : (allocRange start writeSize).endExclusive = .ok finish := h_end
  have h_sz_bne : (spliced.size != allocation.size.bytes.toNat) = false := by
    change (spliced.size != allocation.byteSize.bytes.toNat) = false
    rw [h_spliced_sz]; exact bne_self_eq_false _
  have h_si : setInitialization allocation (allocRange start writeSize) true =
      .ok { allocation with initMask := nextMask } := by
    unfold setInitialization
    rw [h_mask']; rfl
  have h_ov : overwriteRawBytes { allocation with initMask := nextMask, provenance := nextProvenance }
      (allocRange start writeSize) bytes = .ok updated := by
    unfold overwriteRawBytes
    rw [h_end']
    dsimp only [Except.mapError, Bind.bind, Except.bind, allocRange]
    dsimp only [spliced] at h_sz_bne
    rw [ite_eq_right (by rw [h_sz_bne]; exact Bool.false_ne_true)]
    rfl
  unfold Allocation.writeBytes
  rw [h_sfa]
  dsimp only [Id.run, Bind.bind, Pure.pure]
  rw [h_slice', ite_eq_right (by rw [h_wsz_nz]; exact Bool.false_ne_true),
    ite_eq_right (by rw [h_mut]; exact Bool.false_ne_true), h_si]
  dsimp only
  rw [h_clear']
  dsimp only
  rw [h_ov]

/-- Step bridge for zero-sized `Allocation.writeUninit`. -/
theorem writeUninit_zero_bridge (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (sliceBytes : Array UInt8)
    (h_zero : range.size.bytes = 0)
    (h_slice : allocation.getBytesUnchecked range = .ok sliceBytes) :
    Allocation.writeUninit range ptrSize allocation = .ok () allocation := by
  have h_slice' : checkedSlice allocation range = .ok sliceBytes := h_slice
  unfold Allocation.writeUninit
  simp only [Id.run, Pure.pure, h_slice', h_zero, beq_self_eq_true, ↓reduceIte]

/-- Step bridge for nonempty `Allocation.writeUninit`. -/
theorem writeUninit_step_bridge (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (nextMask : InitMask) (nextProvenance : ProvenanceMap P)
    (fullBytes sliceBytes : Array UInt8)
    (h_full : allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes)
    (h_nz : range.size.bytes ≠ 0)
    (h_slice : allocation.getBytesUnchecked range = .ok sliceBytes)
    (h_mut : allocation.mutability = .Mut)
    (h_mask : allocation.initializationMask.setRange range false = .ok nextMask)
    (h_clear : allocation.provenanceMap.clear range fullBytes ptrSize = .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeUninit range ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask = nextMask ∧
      updated.provenanceMap = nextProvenance ∧
      ∀ (anyRange : AllocRange),
        updated.getBytesUnchecked anyRange = allocation.getBytesUnchecked anyRange := by
  have storage : allocation.len = allocation.byteSize.bytes.toNat :=
    (getBytesUnchecked_ok_bounds allocation _ allocation.byteSize fullBytes
      (full_range_endExclusive allocation.byteSize) h_full).1
  have h_raw_eq : fullBytes = allocation.rawBytes :=
    Except.ok.inj (h_full.symm.trans (getBytesUnchecked_full_raw allocation storage))
  subst h_raw_eq
  let updated : Allocation P E :=
    ⟨allocation.rawBytes, allocation.byteSize, nextProvenance, nextMask, allocation.align,
      allocation.mutability, allocation.extra, allocation.nativeBuffer⟩
  refine ⟨updated, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  have h_slice' : checkedSlice allocation range = .ok sliceBytes := h_slice
  have h_mask' : allocation.initMask.setRange range false = .ok nextMask := h_mask
  have h_clear' : allocation.provenance.clear range allocation.rawBytes ptrSize = .ok () nextProvenance := h_clear
  have h_nz_beq : (range.size.bytes == 0) = false := beq_false_of_ne h_nz
  unfold Allocation.writeUninit setInitialization
  simp only [Id.run, Bind.bind, Pure.pure, h_slice', h_nz_beq, Bool.false_eq_true, ↓reduceIte,
    h_mut, bne_self_eq_false, h_mask', Except.mapError, Except.bind, Except.pure]
  rw [h_clear']
  dsimp only [updated]; rw [h_mut]; rfl

/-- Step bridge for `Allocation.copyRepeatedly` on an initialized source range. -/
theorem copyRepeatedly_step_bridge
    (source state : Allocation P E)
    (sourceRange : AllocRange) (srcFinish destStart totalSize destFinish ptrSize : Size)
    (repeatCount : UInt64) (sameAllocation nonoverlapping : Bool)
    (srcFull stFull srcBytes destSliceBytes copiedBytes : Array UInt8)
    (initCopy : InitCopy) (provCopy : ProvenanceCopy P)
    (mask1 mask2 : InitMask) (clearedProv finalProv : ProvenanceMap P)
    (h_srcFull : source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok srcFull)
    (h_srcSlice : source.getBytesUnchecked sourceRange = .ok srcBytes)
    (h_mul : Size.mul sourceRange.size repeatCount = .ok totalSize)
    (h_destFull : state.getBytesUnchecked (allocRange Size.ZERO state.byteSize) = .ok stFull)
    (h_destSlice : state.getBytesUnchecked (allocRange destStart totalSize) = .ok destSliceBytes)
    (h_prepProv : source.provenanceMap.prepareCopy sourceRange srcFull ptrSize = .ok provCopy)
    (h_prepInit : source.initializationMask.prepareCopy sourceRange = .ok initCopy)
    (h_totNz : (totalSize.bytes == 0) = false)
    (h_mut : state.mutability = .Mut)
    (h_mask1 : state.initializationMask.setRange (allocRange destStart totalSize) true = .ok mask1)
    (h_clearProv : state.provenanceMap.clear (allocRange destStart totalSize) stFull ptrSize = .ok () clearedProv)
    (h_srcEnd : sourceRange.endExclusive = .ok srcFinish)
    (h_destEnd : (allocRange destStart totalSize).endExclusive = .ok destFinish)
    (h_noOverlap : sameAllocation = true → nonoverlapping = true →
      ¬((sourceRange.start.bytes ≤ destStart.bytes ∧ destStart.bytes < srcFinish.bytes) ∨
        (destStart.bytes ≤ sourceRange.start.bytes ∧ sourceRange.start.bytes < destFinish.bytes)))
    (h_repChk : (repeatCount > 1 && !nonoverlapping) = false)
    (h_notNoInit : initCopy.noBytesInit = false)
    (h_rcNz : (repeatCount == 0) = false)
    (h_loop : forIn (m := Id) [:repeatCount.toNat] #[] (fun _ acc => pure (ForInStep.yield (acc ++ srcBytes))) = copiedBytes)
    (h_spliced_sz :
      (stFull.extract 0 destStart.bytes.toNat ++ copiedBytes ++
        stFull.extract destFinish.bytes.toNat stFull.size).size = state.byteSize.bytes.toNat)
    (h_applyInit : mask1.applyCopy initCopy (allocRange destStart sourceRange.size) repeatCount = .ok mask2)
    (h_applyProv : clearedProv.applyCopy provCopy (allocRange destStart sourceRange.size) repeatCount = .ok () finalProv) :
    ∃ updated,
      Allocation.copyRepeatedly source sourceRange destStart repeatCount
        ptrSize sameAllocation nonoverlapping state = .ok () updated ∧
      updated.byteSize = state.byteSize ∧
      updated.len = state.len ∧
      updated.mutability = state.mutability ∧
      updated.align = state.align ∧
      updated.extra = state.extra ∧
      updated.nativeBuffer = state.nativeBuffer ∧
      updated.initializationMask = mask2 ∧
      updated.provenanceMap = finalProv ∧
      updated.getBytesUnchecked (allocRange Size.ZERO updated.byteSize) =
        .ok (stFull.extract 0 destStart.bytes.toNat ++ copiedBytes ++
          stFull.extract destFinish.bytes.toNat stFull.size) := by
  have srcStorage : source.len = source.byteSize.bytes.toNat :=
    (getBytesUnchecked_ok_bounds source _ source.byteSize srcFull
      (full_range_endExclusive source.byteSize) h_srcFull).1
  have h_srcRaw : srcFull = source.rawBytes :=
    Except.ok.inj (h_srcFull.symm.trans (getBytesUnchecked_full_raw source srcStorage))
  subst h_srcRaw
  have destStorage : state.len = state.byteSize.bytes.toNat :=
    (getBytesUnchecked_ok_bounds state _ state.byteSize stFull
      (full_range_endExclusive state.byteSize) h_destFull).1
  have h_destRaw : stFull = state.rawBytes :=
    Except.ok.inj (h_destFull.symm.trans (getBytesUnchecked_full_raw state destStorage))
  subst h_destRaw
  let spliced := state.rawBytes.extract 0 destStart.bytes.toNat ++ copiedBytes ++
    state.rawBytes.extract destFinish.bytes.toNat state.rawBytes.size
  let updated : Allocation P E :=
    ⟨spliced, state.byteSize, finalProv, mask2, state.align,
      state.mutability, state.extra, state.nativeBuffer⟩
  refine ⟨updated, ?_, rfl, h_spliced_sz.trans destStorage.symm, rfl, rfl, rfl, rfl, rfl, rfl,
    getBytesUnchecked_full_raw updated h_spliced_sz⟩
  have h_srcSlice' : checkedSlice source sourceRange = .ok srcBytes := h_srcSlice
  have h_destSlice' : checkedSlice state (allocRange destStart totalSize) = .ok destSliceBytes := h_destSlice
  have h_prepProv' : source.provenance.prepareCopy sourceRange source.rawBytes ptrSize = .ok provCopy := h_prepProv
  have h_prepInit' : source.initMask.prepareCopy sourceRange = .ok initCopy := h_prepInit
  have h_mask1' : state.initMask.setRange (allocRange destStart totalSize) true = .ok mask1 := h_mask1
  have h_clearProv' : state.provenance.clear (allocRange destStart totalSize) state.rawBytes ptrSize = .ok () clearedProv := h_clearProv
  have h_sz_bne : (spliced.size != state.size.bytes.toNat) = false := by
    change (spliced.size != state.byteSize.bytes.toNat) = false
    rw [h_spliced_sz]; exact bne_self_eq_false _
  have h_si : setInitialization state (allocRange destStart totalSize) true =
      .ok { state with initMask := mask1 } := by
    unfold setInitialization; rw [h_mask1']; rfl
  have h_prep : prepareForOverwrite (allocRange destStart totalSize) ptrSize state =
      .ok () { state with initMask := mask1, provenance := clearedProv } := by
    have h_tnz : ((allocRange destStart totalSize).size.bytes == 0) = false := h_totNz
    have h_mb : (state.mutability != .Mut) = false := by rw [h_mut]; rfl
    unfold prepareForOverwrite runProvenanceMutation
    dsimp only [Id.run, Bind.bind, Pure.pure]
    rw [h_destSlice']
    dsimp only
    rw [h_tnz, ite_eq_right Bool.false_ne_true, h_mb, ite_eq_right Bool.false_ne_true, h_si]
    dsimp only
    rw [h_clearProv']
    rfl
  have h_ov : overwriteRawBytes { state with initMask := mask1, provenance := clearedProv }
      (allocRange destStart totalSize) copiedBytes =
      .ok { state with rawBytes := spliced, initMask := mask1, provenance := clearedProv } := by
    unfold overwriteRawBytes
    rw [h_destEnd]
    dsimp only [Except.mapError, Bind.bind, Except.bind, allocRange]
    dsimp only [spliced] at h_sz_bne
    rw [ite_eq_right (by rw [h_sz_bne]; exact Bool.false_ne_true)]
    rfl
  have h_loop' : forIn (m := Id) [:repeatCount.toNat] #[] (fun _ acc => ForInStep.yield (acc ++ srcBytes)) = copiedBytes := h_loop
  have h_ov_loop : overwriteRawBytes { state with initMask := mask1, provenance := clearedProv }
      (allocRange destStart totalSize)
      (forIn (m := Id) [:repeatCount.toNat] #[] fun _ acc => ForInStep.yield (acc ++ srcBytes)) =
      .ok { state with rawBytes := spliced, initMask := mask1, provenance := clearedProv } := by
    rw [h_loop']; exact h_ov
  have h_ovl_check : ∀ (k : EStateM.Result AllocError (Allocation P E) Unit),
      (if (sameAllocation && nonoverlapping) = true then
        match sourceRange.endExclusive with
        | .ok sourceFinish =>
          match (allocRange destStart totalSize).endExclusive with
          | .ok firstDestFinish =>
            if ((sourceRange.start.bytes ≤ destStart.bytes && destStart.bytes < sourceFinish.bytes) ||
                (destStart.bytes ≤ sourceRange.start.bytes && sourceRange.start.bytes < firstDestFinish.bytes)) = true then
              EStateM.Result.error .copyRangesOverlap { state with initMask := mask1, provenance := clearedProv }
            else k
          | .error reason => EStateM.Result.error (.memory reason) { state with initMask := mask1, provenance := clearedProv }
        | .error reason => EStateM.Result.error (.memory reason) { state with initMask := mask1, provenance := clearedProv }
      else k) = k := by
    intro k
    by_cases h_sn : (sameAllocation && nonoverlapping) = true
    · rw [ite_eq_left h_sn, h_srcEnd, h_destEnd]
      dsimp only
      simp only [Bool.and_eq_true] at h_sn
      have h_ovl_f : (((sourceRange.start.bytes ≤ destStart.bytes && destStart.bytes < srcFinish.bytes) ||
          (destStart.bytes ≤ sourceRange.start.bytes && sourceRange.start.bytes < destFinish.bytes)) = true) = False := by
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, eq_iff_iff, iff_false]
        exact h_noOverlap h_sn.1 h_sn.2
      rw [ite_eq_right (by rw [h_ovl_f]; exact False.elim)]
    · rw [ite_eq_right h_sn]
  unfold Allocation.copyRepeatedly
  dsimp only [Id.run, Bind.bind, Pure.pure]
  rw [h_srcSlice', h_mul]
  dsimp only
  rw [h_destSlice', h_prepProv', h_prepInit', h_prep]
  dsimp only
  refine (h_ovl_check _).trans ?_
  rw [ite_eq_right (by rw [h_repChk]; exact Bool.false_ne_true),
    ite_eq_right (by rw [h_notNoInit]; exact Bool.false_ne_true),
    ite_eq_right (by rw [h_rcNz, Bool.and_false, Bool.false_and]; exact Bool.false_ne_true),
    h_ov_loop]
  dsimp only
  rw [h_applyInit]
  dsimp only
  rw [h_applyProv]
  rfl

end Miri.Memory.Allocation.Bridge
