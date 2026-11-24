import CanonicalPhysicalLengthContext
import RootActiveLengthToRaw
import RootPositiveWithSharedOutput
import PreparedAliasCompatibility
import CanonicalPreparedPhysicalResources
import duplicate_prefix.GeneratedSafetyOfTrace

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency Miri.DataStructures
open SourceDomain PreparedArguments CanonicalConfigFacts
open GeneralRangeMapOrigins ArchiveForestProjection RetagReleaseFootprint RootZeroShallowReturn NonemptyReturnWatch RootAcceptedAsMutAlias RetagReleaseRights
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem nonemptyPhysicalSharedAccepted
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (validation : options.limits.validation = fuel+1) (statementFuel : limits.validation = fuel+1)
    (dynamic : options.place.dynamicFuel = sizeFuel+1) (dispatchFuel : limits.callDispatch = dispatch+1)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer (Option Provenance)) (length count : UInt64) (positive : 0 < length)
    (nonzero : count ≠ 0) (accepted : ¬ count > length/2)
    (continues : frame.returnContinuation = .stop true)
    (destination : PhysicalBoolDestination (Storage.withCurrent #[] frame machine) frame pointer length true)
    (shared : SharedPhysicalAllocation frame pointer)
    (admitted : Admitted program options remaining preparedTagHeadroom span
      (Storage.withCurrent #[] frame machine) frame pointer length count true)
    (compiler : InitialCompilerControl (Storage.withCurrent #[] frame machine) frame)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (resource : ∀ id tag, pointer.provenance = some (.concrete id tag) →
      ∀ entry, machine.memory.live[id]? = some entry → CopySourceResources entry) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent #[] frame machine) := by
  obtain ⟨context⟩ := reachesPhysicalLengthContext program loaded options limits remaining sizeFuel fuel dispatch span
    validation dynamic dispatchFuel frame machine pointer length count positive nonzero admitted compiler resource
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let profile := admitted.profile
  let original := context.post.branch.ready
  let lower := context.storage.relativeStart.bytes
  let upper := lower + length
  have nonempty : length ≠ 0 := by
    intro equal
    rw [equal] at positive
    exact UInt64.lt_irrefl _ positive
  obtain ⟨sharedId,argument,sharedPlace,savedTag,argumentPointer,savedPlace,savedPointer⟩ := shared
  have sameSource := Option.some.inj (argumentPointer.symm.trans context.pointerTag)
  injection sameSource with sameId sameArgument
  subst sharedId
  subst argument
  obtain ⟨place,id,row,byte,parentTag,outputBase,tracker,owned,parent,outputTag,output,
    saved,layout,aligned,live,mutable,backed,mask,maskLen,prov,fits,ptr,nonnull,address,capacity,cached,
    tracked,ledger,rows,held,coherent,parentKey,parentData,outputKey,outputData,extent,grant,parentGrant,geometry⟩ :=
      (context.destination nonempty destination).storage
  have placeEq := RuntimeStackPlace.memory.inj (saved.symm.trans (context.post.place.trans savedPlace))
  subst sharedPlace
  have sharedKey := Option.some.inj (ptr.symm.trans savedPointer)
  injection sharedKey with outputId sameParentTag
  subst id
  have sourceRow : row = original.entry := Option.some.inj
    (live.symm.trans (by rw [← context.post.branch.id]; exact original.present))
  subst row
  have trackerEq : tracker = original.tracker := Option.some.inj (tracked.symm.trans original.tracked)
  subst tracker
  have sameBase : outputBase = context.base := by
    have sourceBase : context.final.user.addresses.baseAddr.find? (·.allocId == context.ready.id) = some ⟨context.ready.id,context.base⟩ := by
      rw [context.post.branch.stable.addresses]
      exact context.cached
    have equal := Option.some.inj (cached.symm.trans sourceBase)
    injection equal
  subst outputBase
  obtain ⟨outputNode,outputAt,outputTagged,outputParent,outputHidden⟩ := outputData
  obtain ⟨parentNode,parentAt,parentTagged⟩ := parentData
  obtain ⟨separated,noAncestor⟩ : DisjointResultByte (context.base.toNat + byte.bytes.toNat)
      pointer.offset.bytes.toNat length ∧
        ¬ Ancestor original.entry.allocation.extra output original.source := by
    rcases geometry nonempty context.ready.id context.ready.tag context.pointerTag with unequal | same
    · exact False.elim (unequal rfl)
    exact ⟨same.1, same.2 _ (by rw [← context.post.branch.tag]; exact original.indexed)⟩
  have outside : byte.bytes.toNat < lower.toNat ∨ upper.toNat ≤ byte.bytes.toNat := by
    rw [context.address] at separated
    change byte.bytes.toNat < context.storage.relativeStart.bytes.toNat ∨
      (context.storage.relativeStart.bytes + length).toNat ≤ byte.bytes.toNat
    rw [context.upper]
    unfold DisjointResultByte at separated
    omega
  have room : byte.bytes.toNat + 1 < 2^64 := Nat.lt_of_le_of_lt extent.extent
    original.entry.allocation.extra.locations.size.bytes.toNat_lt
  have afterByte : (byte.bytes+1).toNat = byte.bytes.toNat+1 := by
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt room]
  have active : AccessedWithin original.entry.allocation.extra output byte.bytes (byte.bytes+1) := by
    intro point i valid lo hi state fromRow accessed
    simpa only [afterByte,UInt64.toNat_one] using extent.accessedWithin point i valid lo hi state fromRow accessed
  let endTags := (original.tracker.global.endCall owned).protectedTags
  let masks (index : UniIndex) (tags : ProtectedTags) : Prop :=
    (index = output ∧ tags = original.tracker.global.protectedTags) ∨ (index = parent ∧ tags = endTags)
  have parentPoint : AtByte original.entry.allocation.extra byte.bytes endTags parent := by
    intro i valid lo hi
    obtain ⟨segment,member,pLo,pHi,permission⟩ := parentGrant
    obtain ⟨j,inside,same⟩ := Array.mem_iff_getElem.mp member
    subst segment
    have unique : i = j := by
      rcases Nat.lt_trichotomy i j with lt | eq | gt
      · have bound := GeneralRangeMapGeometry.stop_le_start _ coherent.ranges i j lt inside
        have lower := UInt64.le_iff_toNat_le.mp pLo
        have upper := UInt64.lt_iff_toNat_lt.mp hi
        omega
      · exact eq
      · have bound := GeneralRangeMapGeometry.stop_le_start _ coherent.ranges j i gt valid
        have lower := UInt64.le_iff_toNat_le.mp lo
        have upper := UInt64.lt_iff_toNat_lt.mp pHi
        omega
    subst j
    exact permission
  let watch : ReturnWatch original.entry.allocation.extra original.source lower upper := {
    holder := output, writer := parent, holderNode := outputNode, writerNode := parentNode,
    holderAt := outputAt, writerAt := parentAt, foreign := noAncestor, byte := byte.bytes, scope := active,
    allows := masks,
    writerReady := by
      intro i tags proof
      rcases proof with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact ⟨_,outputAt⟩
      · exact ⟨_,parentAt⟩
    rights := by
      intro index tags selected point i valid lo hi _ equal
      subst point
      rcases selected with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact grant _ (Array.getElem_mem valid) lo hi
      · exact parentPoint i valid lo hi }
  have bounded : length ≤ 9223372036854775807 := by
    apply UInt64.le_iff_toNat_le.mpr
    change length.toNat ≤ 9223372036854775807
    have width := admitted.slice.addressable
    omega
  have sourceBase : machine.user.addresses.baseAddr.find? (·.allocId == context.storage.id) =
      some ⟨context.storage.id,context.base⟩ := by simpa only [context.id] using context.cached
  have addressSum : context.base.toNat + lower.toNat < 2^64 := by
    have region := admitted.allocations.regionAddresses ⟨context.storage.id,context.base⟩
      (Array.mem_of_find?_eq_some sourceBase) context.storage.entry context.storage.live
    have fits := context.storage.fits
    change context.base.toNat + context.storage.entry.allocation.byteSize.bytes.toNat < 2^64 at region
    change lower.toNat + length.toNat ≤ context.storage.entry.allocation.byteSize.bytes.toNat at fits
    omega
  have pointerBytes : pointer.offset.bytes = context.base + lower := by
    apply UInt64.toNat.inj
    rw [context.address,UInt64.toNat_add,Nat.mod_eq_of_lt addressSum]
  have sourceNonnull : context.base + lower ≠ 0 := by rw [← pointerBytes]; exact admitted.slice.nonnull
  obtain ⟨old,_,oldTracker,_,_,tagBudget,oldProtections,_,_⟩ := admitted.allocations.ledger
  have sameTracker := Option.some.inj (oldTracker.symm.trans context.loan.tracked)
  subst old
  change context.loan.tracker.global.nextPointerTag.value.toNat + 4 < 2^64 at tagBudget
  have protectedAge (tag : BorTag) (hasProtection : context.loan.tracker.global.protectedTags.contains tag = true) :
      tag.value.toNat < context.loan.tracker.global.nextPointerTag.value.toNat := by
    unfold ProtectedTags.contains ProtectedTags.get at hasProtection
    cases key : context.loan.tracker.global.protectedTags.entries.find? (fun row => row.1 == tag) with
    | none => simp [key] at hasProtection
    | some row =>
      have picked := beq_iff_eq.mp (Array.find?_some (p := fun row : BorTag × ProtectorKind => row.1 == tag) key)
      rw [← picked]
      exact UInt64.lt_iff_toNat_lt.mp (oldProtections row (Array.mem_of_find?_eq_some key))
  obtain ⟨buffer,readBuffer,slot1,slot2⟩ := admitted.aliasInitialArgumentSlots
  have sameBuffer := Except.ok.inj ((concreteSliceImmediate pointer context.storage.id context.ready.tag context.base lower length
    (by simpa only [context.id] using context.pointerTag) pointerBytes).symm.trans readBuffer)
  rw [← sameBuffer,← actual_access_runtime options () (remaining+1) span] at slot1
  have dead (i : Nat) (lo : 15 ≤ i) (hi : i ≤ 24) : frame.locals[i]? = some ⟨.dead, none⟩ := by
    have facts := admitted.aliasInitialTemporarySlot loaded compiler i (by omega) (by omega)
    have n6 : i ≠ 6 := by omega
    have n13 : i ≠ 13 := by omega
    have n14 : i ≠ 14 := by omega
    simpa [Array.contains,n6,n13,n14,Ne.symm n6,Ne.symm n13,Ne.symm n14] using facts
  obtain ⟨rawFrame,rawMachine,rawTrace,⟨raw⟩⟩ :=
    context.post.toAliasedRaw options limits remaining fuel sizeFuel span validation dynamic
      profile.debugOff profile.preciseInteriorMutOff profile.implicitWritesOff accepted
      positive bounded context.storage context.id.symm rfl rfl context.scope.extent context.source.room
      tagBudget protectedAge context.base sourceBase sourceNonnull profile.compilerRuntime profile.noSyntheticSliceCache
      compilerSourceComparator dispatch dispatchFuel profile.raceOff profile.backendOff (show ProjectionMetadataFacts.NullComparator from by decide)
      compiler.highestRelevance slot1 slot2 dead watch

  have beforeOld : original.tracker.global.nextPointerTag.value.toNat + 2 < 2^64 := by
    have age := context.post.nextTag
    change original.tracker.global.nextPointerTag.value.toNat =
      context.loan.tracker.global.nextPointerTag.value.toNat + 2 at age
    rw [age]
    simpa only [Nat.add_assoc] using tagBudget
  have rawAge : (AsMutDisjointByte.rawTag original.tracker.global).value.toNat =
      original.tracker.global.nextPointerTag.value.toNat + 1 := by
    have enough : original.tracker.global.nextPointerTag.value.toNat + 1 < 2^64 := by omega
    have notMax : original.tracker.global.nextPointerTag.value ≠ 18446744073709551615 := by
      intro max
      rw [max] at beforeOld
      simp at beforeOld
    have word : (original.tracker.global.nextPointerTag.value + 1).toNat =
        original.tracker.global.nextPointerTag.value.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt enough]
    have nonzeroNext : original.tracker.global.nextPointerTag.value + 1 ≠ 0 := by
      intro fail
      rw [fail] at word
      simp at word
    simp [AsMutDisjointByte.rawTag,BorTag.succ,BorTag.ofUInt64,notMax,nonzeroNext,word]
  have oldKeys (index : UniIndex) (node : TreeNode)
      (found : original.entry.allocation.extra.nodeAt index = some node) :
      node.tag ≠ original.tracker.global.nextPointerTag ∧
        node.tag ≠ AsMutDisjointByte.rawTag original.tracker.global := by
    have old : node.tag.value.toNat < original.tracker.global.nextPointerTag.value.toNat :=
      context.post.tagAge index node found
    constructor
    · intro equal
      rw [equal] at old
      exact (Nat.lt_irrefl _ old)
    · intro equal
      rw [equal,rawAge] at old
      omega
  have parentAge := oldKeys parent parentNode parentAt
  have outputAge := oldKeys output outputNode outputAt
  rw [parentTagged] at parentAge
  rw [outputTagged] at outputAge
  let tree := raw.region.entry.allocation.extra
  have parentKey' : tree.indexOfTag parentTag = some parent :=
    (raw.output.keys parentTag parentAge.1 parentAge.2).trans parentKey
  have outputKey' : tree.indexOfTag outputTag = some output :=
    (raw.output.keys outputTag outputAge.1 outputAge.2).trans outputKey
  obtain ⟨nextOutput,outAt,outTag,outParent,outHidden⟩ := raw.output.holderAt
  obtain ⟨nextParent,parAt,parTag,_,_⟩ := raw.output.writerAt
  have treeWell : CoherentForest tree := raw.rights.coherent
  have activeAfter : AccessedOnlyWithin tree output byte.bytes.toNat (byte.bytes.toNat+1) := by
    intro point i valid lo hi state fromRow accessed
    simpa only [watch, afterByte] using raw.output.active point i valid lo hi state fromRow accessed
  have region : byte.bytes.toNat+1 ≤ tree.locations.size.bytes.toNat := by
    rw [raw.allocationSize]
    exact extent.extent
  have release := ReleaseRange.ofActiveByteScope treeWell region raw.roots activeAfter raw.original.footprint.vacant
  have outGrant : ByteWriteGrant tree byte.bytes output raw.rights.tracker.global.protectedTags := by
    intro segment member lo hi
    obtain ⟨i,valid,rfl⟩ := Array.mem_iff_getElem.mp member
    rw [raw.protections]
    exact raw.output.rights output original.tracker.global.protectedTags (.inl ⟨rfl,rfl⟩)
      byte.bytes i valid lo hi outside rfl
  have endMask : (raw.rights.tracker.global.endCall owned).protectedTags = endTags := by
    unfold endTags GlobalState.endCall
    rw [raw.protections]
  have parGrant : ∃ segment ∈ tree.locations.entries,
      segment.range.start ≤ byte.bytes ∧ byte.bytes < segment.range.stop ∧
      LocationRights tree segment.data (raw.rights.tracker.global.endCall owned).protectedTags parent := by
    obtain ⟨i,valid,lo,hi⟩ := GeneralRangeMapGeometry.covered tree.locations treeWell.ranges byte.bytes (by omega)
    have lo' := UInt64.le_iff_toNat_le.mpr lo
    have hi' := UInt64.lt_iff_toNat_lt.mp hi
    exact ⟨_,Array.getElem_mem valid,lo',hi',by
      rw [endMask]
      exact raw.output.rights parent endTags (.inr ⟨rfl,rfl⟩) byte.bytes i valid lo' hi' outside rfl⟩
  have sourceAlive : rawMachine.memory.live[context.ready.id]? = some raw.region.entry := by
    calc
      _ = rawMachine.memory.live[raw.region.id]? :=
        congrArg (fun key => rawMachine.memory.live[key]?) (context.id.trans raw.sourceId.symm)
      _ = _ := raw.region.live
  have newGeometry : length ≠ 0 → ∀ sourceId sourceTag,
      pointer.provenance = some (.concrete sourceId sourceTag) → sourceId ≠ context.ready.id ∨
        (DisjointResultByte (context.base.toNat + byte.bytes.toNat) pointer.offset.bytes.toNat length ∧
          ∀ holder, tree.indexOfTag sourceTag = some holder → ¬ Ancestor tree output holder) := by
    intro _ sourceId sourceTag selected
    have equal := Option.some.inj (context.pointerTag.symm.trans selected)
    injection equal with sameId sameTag
    subst sourceId
    subst sourceTag
    refine .inr ⟨?_,?_⟩
    · rw [context.address]
      change context.base.toNat + byte.bytes.toNat + 1 ≤ context.base.toNat + lower.toNat ∨
        context.base.toNat + lower.toNat + length.toNat ≤ context.base.toNat + byte.bytes.toNat
      have stop : upper.toNat = lower.toNat + length.toNat := context.upper
      omega
    · intro holder atTag path
      have picked := Option.some.inj (raw.original.key.symm.trans
        (show tree.indexOfTag original.tag = some holder by rw [context.post.branch.tag]; exact atTag))
      subst holder
      exact raw.output.foreign (ancestor_trans path raw.original.path.1)
  have outputPlace : rawFrame.returnPlace = .memory place :=
    raw.place.trans (context.post.place.symm.trans saved)
  have savedOut : PhysicalBoolDestination (Storage.withCurrent #[] rawFrame rawMachine) rawFrame pointer length true := by
    refine ⟨place,context.ready.id,raw.region.entry,byte,parentTag,context.base,raw.rights.tracker,owned,parent,outputTag,output,
      outputPlace,layout,aligned,sourceAlive,?_,?_,?_,?_,?_,?_,ptr,nonnull,address,?_,?_,
      raw.rights.tracked,?_,rows,?_,treeWell,parentKey',?_,outputKey',?_,release,outGrant,parGrant,newGeometry⟩
    · rw [raw.allocationData]; exact mutable
    · rw [raw.allocationData]; exact backed
    · rw [raw.allocationData]; exact mask
    · rw [raw.allocationData]; exact maskLen
    · rw [raw.allocationData]; exact prov
    · rw [raw.allocationData]; exact fits
    · rw [raw.allocationData]; exact capacity
    · change rawMachine.user.addresses.baseAddr.find? (·.allocId == context.ready.id) = some ⟨context.ready.id,context.base⟩
      rw [raw.addresses]
      exact context.cached
    · rw [raw.extra,← context.post.frameExtra]; exact ledger
    · rw [raw.protections]; exact held
    · exact ⟨nextParent,parAt,parTag.trans parentTagged⟩
    · exact ⟨nextOutput,outAt,outTag.trans outputTagged,outParent.trans outputParent,outHidden.trans outputHidden⟩
  obtain ⟨root,readRoots⟩ := raw.roots
  obtain ⟨node,sourceFound,_⟩ := raw.rights.sourcePresent
  obtain ⟨holderNode,holderAt,holderHidden⟩ := Option.map_eq_some_iff.mp raw.original.hidden
  have nextStart : raw.region.relativeStart.bytes = lower := congrArg Size.bytes raw.relative
  let holder : PhysicalDestinationAfterCopy.SliceHolder tree raw.rights.tracker.global.protectedTags
      (AsMutDisjointByte.rawTag original.tracker.global) raw.region.relativeStart length := {
    source := raw.rights.source, root, holder := original.source, tag := original.tag, node, holderNode
    atSource := sourceFound, atTag := raw.rights.tagKnown, atHolder := holderAt, holderTag := raw.original.key
    unexposed := holderHidden, roots := readRoots, coherent := treeWell
    lineage := raw.original.path.1
    unheld := by rw [raw.protections]; exact raw.original.path.2
    fits := by rw [nextStart]; exact raw.span
    footprint := by rw [raw.protections,nextStart]; exact raw.original.footprint }
  have pointerTag : pointer.provenance = some (.concrete raw.region.id holder.tag) := by
    change pointer.provenance = some (.concrete raw.region.id original.tag)
    rw [raw.sourceId,context.post.branch.tag,← context.id]
    exact context.pointerTag
  have backing (key : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (live : rawMachine.memory.live[key]? = some entry) :
      rawMachine.user.payload.payload.user.runtime.extras.allocations.find? (·.1 == key) =
        some (key,{weakMemory := none, backtrace := (AllocationBacktrace.get
          rawMachine.user.payload.payload.user.runtime.extras.allocations key)}) := by
    have present : machine.memory.live.contains key = true := by
      by_cases same : key = context.storage.id
      · subst key
        have old := context.storage.live
        change machine.memory.live[context.storage.id]? = some context.storage.entry at old
        simp [Std.ExtTreeMap.contains_eq_isSome_getElem?,old]
      · have old := (raw.unrelated key same).symm.trans live
        simp [Std.ExtTreeMap.contains_eq_isSome_getElem?,old]
    obtain ⟨effects,lookup,noWeak,noSync⟩ := admitted.allocations.extras key present
    change machine.user.payload.payload.user.runtime.extras.allocations.find? (·.1 == key) = some (key,effects) at lookup
    rw [raw.extras,AllocationBacktrace.of_lookup lookup,lookup]
    congr 2
    cases effects
    simp_all
  have disjoint : count.toNat + count.toNat ≤ length.toNat :=
    SymbolicBounds.usize_guard accepted
  have nonzeroCount : 0 < count.toNat := by
    have countNat : count.toNat ≠ 0 := by
      intro empty
      exact nonzero (UInt64.toNat.inj (by simpa using empty))
    omega
  have lenFits : length.toNat ≤ 9223372036854775807 := UInt64.le_iff_toNat_le.mp bounded
  have countFits : count.toNat < 2^63 := by omega
  have maxTarget : count ≤ cfg.projection.maxSizeOfVal.bytes := by
    obtain ⟨place, pointers, table, _, projection, _⟩ :=
      (CanonicalConfigFacts.actual_fields options () (remaining+1) span).placeConstruction
    have maximum := ActualRootReferenceDeref.constructor_maximum options (remaining+1) span place pointers table projection
    have projectionMaximum : cfg.projection.maxSizeOfVal = place.maxSizeOfVal := by
      dsimp only [cfg]
      rw [projection]
      rfl
    rw [projectionMaximum,maximum]
    apply UInt64.le_iff_toNat_le.mpr
    change count.toNat ≤ 9223372036854775807
    omega
  have size := raw.size
  let temp16 := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (.new (.concrete context.storage.id original.tracker.global.nextPointerTag)
        (Size.ofBytes (context.base+lower))) length RootCompilerFacts.sliceLayout).imm
  have live16 : (rawFrame.locals[16]'(by omega)).value = .live (.immediate temp16) :=
    congrArg LocalState.value (Array.getElem?_eq_some_iff.mp raw.reservedSlot).2
  have unused (i : Nat) (v : i < rawFrame.locals.size) (lo : 17 ≤ i) (hi : i ≤ 23) :
      rawFrame.locals[i]'v = ⟨.dead,none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem v).symm.trans
      ((raw.tail i lo).trans (dead i (by omega) (by omega))))
  obtain ⟨thread,running,top⟩ := raw.current
  have body := raw.body
  have identity := raw.identity
  have callee := raw.callee
  have extras := backing raw.region.id raw.region.entry raw.region.live
  have originalMask : original.entry.allocation.initializationMask = context.storage.entry.allocation.initializationMask :=
    congrArg (·.allocation.initializationMask) context.post.branch.allocationData
  have originalSize : original.entry.allocation.byteSize = context.storage.entry.allocation.byteSize :=
    congrArg (·.allocation.byteSize) context.post.branch.allocationData
  have originalProvenance : original.entry.allocation.provenanceMap = context.storage.entry.allocation.provenanceMap :=
    congrArg (·.allocation.provenanceMap) context.post.branch.allocationData
  have originalStorage : original.entry.allocation.len = context.storage.entry.allocation.len :=
    congrArg (·.allocation.len) context.post.branch.allocationData
  have rawMask : raw.region.entry.allocation.initializationMask = context.storage.entry.allocation.initializationMask :=
    (congrArg (·.allocation.initializationMask) raw.allocationData).trans originalMask
  have rawSize : raw.region.entry.allocation.byteSize = context.storage.entry.allocation.byteSize :=
    (congrArg (·.allocation.byteSize) raw.allocationData).trans originalSize
  have rawProvenance : raw.region.entry.allocation.provenanceMap = context.storage.entry.allocation.provenanceMap :=
    (congrArg (·.allocation.provenanceMap) raw.allocationData).trans originalProvenance
  have rawStorage : raw.region.entry.allocation.len = context.storage.entry.allocation.len :=
    (congrArg (·.allocation.len) raw.allocationData).trans originalStorage
  have reachesRaw := SuccessfulTrace.append context.trace rawTrace
  obtain ⟨done,finished,stopped,_⟩ :=
    RootPositiveWithSharedOutput.completes options limits remaining span profile.debugOff fuel validation statementFuel
      rawFrame _ rawMachine reachesRaw length count context.base (AsMutDisjointByte.rawTag original.tracker.global)
      raw.region raw.rights nonzeroCount countFits disjoint (by rw [raw.addresses,raw.sourceId]; exact sourceBase)
      size (by rw [raw.sourceId,raw.relative]; exact raw.pointer) temp16 live16 raw.countSlot unused
      ((raw.tail 24 (by decide)).trans (dead 24 (by decide) (by decide)))
      body identity callee raw.location (by rw [raw.extra]; exact admitted.stack.calleeClocksOff)
      raw.mode raw.ghost raw.shallow raw.direct raw.raceOff (raw.track.trans compiler.noTrackCaller)
      thread running top (by rw [raw.extra,compiler.highestRelevance]; decide) dispatch dispatchFuel raw.noBackend
      raw.unchecked raw.noGC raw.fixed compilerSourceComparator
      (by rw [raw.extra]; exact outerRank) (by rw [raw.extra]; exact innerRank)
      (by rw [rawMask,rawSize]; exact context.source.maskLength)
      (by rw [rawMask]; exact context.source.mask)
      (by rw [rawProvenance,rawStorage]; exact context.source.provenance)
      (by rw [rawStorage]; exact context.source.storageBound)
      root readRoots (by rw [nextStart]; exact raw.span) maxTarget extras (raw.resultSlot.trans admitted.resultSlot)
      holder pointer pointerTag (by rw [nextStart]; exact context.address) savedOut backing
      (raw.varargs.trans admitted.stack.noVarargs) (raw.continuation.trans continues)
  exact GeneratedSafetyOfTrace.required program loaded cfg limits _ done admitted.entered finished
    (by simp [Storage.withCurrent,stopped])

#print axioms nonemptyPhysicalSharedAccepted
end DuplicatePrefix.CanonicalCallDomain
