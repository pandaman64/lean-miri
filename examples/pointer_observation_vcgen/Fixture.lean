import Miri.Input.InitialMachine
import Miri.Verification.GeneratedBodyVC
import empty_function.Configuration

/-! Canonical core profile and explicit prepared state for the imported MIR examples. -/
namespace PointerObservation.Fixture

open Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Verification
open EmptyFunction.Configuration

abbrev State := MachineHooks.State MiriMemoryKind RootUser
abbrev Config := ExecutionMachine.Config MiriMemoryKind RootUser Unit Unit ExternAbi Unit
def limits : ExecutionMachine.Limits := ⟨32, 32, 32, 32⟩

def configure (input : ExecutionInput) (root : Nat) : Except String (Config × ULift.{1} EvalPreparation.Prepared × ULift.{1} BodyVCGen.LoadedProgram) := do
  let lowered ← (lowerProgram input.document).map ULift.up
  let attempt := EvalPreparation.prepare lowered.down
  let prepared ← (attempt.outcome.map ULift.up)
  let prepared := prepared.down
  let compiler := prepared.compiler
  let program ← (BodyVCGen.loadProgram input root).map ULift.up
  let bytes ← ((CompilerGlobalBytes.prepare compiler.program compiler.runtime attempt.memory).map ULift.up).mapError toString
  let options := {exampleOptions limits 32 32 32 32 .Shallow ⟨false, false⟩ with
    panicUnwinds := false, userRelevantCrates := #[0]}
  let config ← (rootConfig prepared bytes.down options () 32).mapError reprStr
  return (config, ULift.up prepared, program)

private def address : UInt64 := 4096
def allocId : AllocId := ⟨1, by decide⟩
def child : BorTag := ⟨2, by decide⟩
def pointer (tag : BorTag) (offset : UInt64) : Pointer Provenance :=
  Pointer.new (.concrete allocId tag) (Size.ofBytes (address + offset))

/-- Build a one-allocation managed memory profile with no concurrent threads. -/
def initialMachine (prepared : EvalPreparation.Prepared) (image : Allocation Provenance Unit)
    (tree : BorrowTree) : Except String (ULift.{1} (MachineHooks.MachineState MiriMemoryKind RootUser)) := do
  let empty : MemoryState Provenance BorrowTree MiriMemoryKind := MemoryState.empty.setIssuedIds #[allocId]
  let memory := {empty with live := empty.live.insert allocId ⟨.stack, image.withExtra tree⟩, nextAllocId := 2}
  let options : InitialMachine.Configuration Unit Unit := {
    geometry := ⟨4096,131072,65536⟩
    dummySpan := prepared.dummySpan
    provenance := .default
    addressMode := .managed
    addressStop := 9223372036854775807
    addressReuse := ⟨0,0⟩
    fixedScheduling := true
    trackOutdatedLoads := false
    weakMemory := false
    backend := .none
    trackedTags := some #[]
    validation := .Shallow
    alignment := .Int
    affinity := none
    muteOutput := true
    hostUsizeBits := 64 }
  let host : MinimalHost := ⟨⟨0,0,0,.virtual 0,0,false⟩,#[]⟩
  let state ← ((InitialMachine.create (Os := Unit) (R := Unit) (P := Unit)
    (H := Unit) (D := Unit) (O := Unit) options memory prepared.types {inputs := #[]} host).map ULift.up).mapError reprStr
  let state := ExecutionStateTransport.inward state.down
  let user := state.machine.user
  let stored := user.payload.payload
  let world := stored.user
  let runtime := {world.runtime with extras := {allocations := #[(allocId, {weakMemory := none})]}}
  let user := {user with payload := {user.payload with payload := {stored with user := {world with runtime}}}}
  let addresses := { user.addresses with
    baseAddr := #[⟨allocId, address⟩], intToPtrMap := #[⟨address, allocId⟩] }
  let global : Miri.TreeBorrows.GlobalState := { Miri.TreeBorrows.GlobalState.new with
    nextPointerTag := ⟨3, by decide⟩, rootPointerTags := #[(allocId, BorTag.one)] }
  let machine := {state.machine with borrowTracker := some ⟨global, .Default⟩, user := {user with addresses}}
  return ULift.up machine

/-- Compiler-derived layout of the imported declaration for a cached local. -/
def layoutOfLocal (prepared : EvalPreparation.Prepared) (program : BodyVCGen.LoadedProgram)
    (id : Miri.MIR.LocalId) : Except String (ULift.{1} LocalLayout) := do
  let some ty := program.root.body.locals[id]? | throw "fixture local is missing"
  let fact ← (CompilerFacts.layoutOf prepared.compiler.lifecycle.calls.symbols.facts.context ty).map ULift.up
  return ULift.up ⟨fact.down.ty, fact.down.layout⟩

def localImmediate (imm : Immediate Provenance) (layout : Option LocalLayout := none) :
    LocalState Provenance LocalLayout :=
  ⟨.live (.immediate imm), layout⟩

def pointerImmediate (prepared : EvalPreparation.Prepared) (tag : BorTag) (offset : UInt64) :
    Immediate Provenance :=
  .scalar (Scalar.fromPointer prepared.compiler.runtime.target.base (pointer tag offset))

def frameAt (prepared : EvalPreparation.Prepared) (program : BodyVCGen.LoadedProgram)
    (outputLayout : LocalLayout) (position : Nat) :
    Frame Provenance LocalLayout MachineHooks.FrameExtra :=
  let identity := LocalsIdentity.ofAllocationToken 1
  let frame := Frame.create program.root program.rootInstance ⟨some {}, none, 0, none⟩
    (.stop true) (.frameLocal 0 0 none outputLayout identity) prepared.dummySpan identity
  {frame with location := .mir ⟨0, position⟩}

def scalarAt (state : State) (id : Nat) : Option UInt8 := do
  let frame ← state.stack.currentFrame?
  let row ← frame.locals[id]?
  let .live (.immediate (.scalar scalar)) := row.value | none
  scalar.toUInt8.toOption

def bytesAt (offset : UInt64) (state : State) : Option (Except AllocError (Array UInt8)) :=
  state.machine.memory.live[allocId]?.map fun entry =>
    entry.allocation.getBytesUnchecked (allocRange (Size.ofBytes offset) (Size.ofBytes 1))

/-- Exact bounded VC for consecutive statements of the imported MIR. Check
the live program counter and instruction before applying each selected rule.
The first failing instruction passes its actual successor state to failure. -/
def prefixPre (config : Config) (post : State → Prop) (failure : StepError → State → Prop) :
    Nat → List BodyCFG.Node → State → Prop
  | _, [], state => post state
  | pc, node :: rest, state =>
    BodyCFG.selected state = some (⟨0, pc⟩, node) ∧
      BodyCFG.nodePre config limits () (fun more next =>
        more = true ∧ prefixPre config post failure (pc + 1) rest next) failure state node

/-- Proofs at a selected row apply to the actual canonical machine step.
Use the same continuation at every routed successor. -/
theorem selectedPre_iff (config : Config) (post : Bool → State → Prop)
    (failure : StepError → State → Prop) (state : State) (pc : Location) (node : BodyCFG.Node)
    (selected : BodyCFG.selected state = some (pc, node)) :
    BodyCFG.nodePre config limits () post failure state node ↔
      InstructionWP.resultPre post failure (ExecutionMachine.step config limits () state) := by
  let equation : BodyCFG.Equation := ⟨pc, node, #[]⟩
  let cfg : BodyCFG.Compiled := {blocks := #[]}
  have postEq : (fun more after => if more then
      BodyCFG.route cfg (fun _ => post true) (post true) after else post false after) = post := by
    funext more after
    cases more
    · rfl
    · exact propext (BodyCFG.route_shared cfg (post true) after)
  simpa only [BodyCFG.Equation.pre, equation, postEq, ExecutionMachine.step] using
    BodyCFG.Equation.pre_iff equation config limits cfg () (fun _ => post true)
      (post true) (post false) failure state selected

/-- Evaluate the same finite prefix on the fixed interpreter. A mismatch
or an unexpected stop leaves the selected window without an observation. -/
def executePrefix (config : Config) :
    Nat → List BodyCFG.Node → State → Option (StepResult State Unit)
  | _, [], state => some (state, .ok ())
  | pc, node :: rest, state =>
    if BodyCFG.selected state = some (⟨0, pc⟩, node) then
      match ExecutionMachine.step config limits () state with
      | (after, .ok true) => executePrefix config (pc + 1) rest after
      | (_, .ok false) => none
      | (after, .error error) => some (after, .error error)
    else none

theorem prefixPre_iff_execute (config : Config) (post : State → Prop)
    (failure : StepError → State → Prop) (pc : Nat) (rows : List BodyCFG.Node) (state : State) :
    prefixPre config post failure pc rows state ↔
      (match executePrefix config pc rows state with
      | none => False
      | some result => InstructionWP.resultPre (fun _ => post) failure result) := by
  induction rows generalizing pc state with
  | nil => rfl
  | cons node rest ih =>
    by_cases selected : BodyCFG.selected state = some (⟨0, pc⟩, node)
    · rw [prefixPre, executePrefix]
      simp only [selected, ↓reduceIte, true_and, selectedPre_iff config _ failure state _ node selected]
      rcases stepped : ExecutionMachine.step config limits () state with ⟨after, outcome⟩
      cases outcome with
      | error error => rfl
      | ok more =>
        cases more
        · simp [InstructionWP.resultPre]
        · simpa only [InstructionWP.resultPre, true_and] using ih (pc + 1) after
    · simp only [prefixPre, executePrefix, selected, ite_false, false_and]

/-- Use the public emitted window when its rows match this fixture prefix.
The comparison checks the actual compiler PCs and instruction payloads. -/
theorem prefixPre_iff_windowPrefixPre (config : Config) (post : State → Prop)
    (failure : StepError → State → Prop) (pc : Nat) (nodes : List BodyCFG.Node)
    (rows : List (GeneratedBodyVC.WindowRow config limits)) (state : State)
    (same : rows.map (fun row => (row.location.pc, row.reduced.node)) =
      (nodes.zipIdx pc).map (fun (node, index) => (⟨0, index⟩, node))) :
    prefixPre config post failure pc nodes state ↔
      GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True) post failure rows state := by
  induction nodes generalizing pc rows state with
  | nil => cases rows <;> simp_all [prefixPre, GeneratedBodyVC.windowPrefixPre]
  | cons node nodes ih =>
    cases rows with
    | nil => simp [List.zipIdx_cons] at same
    | cons row rows =>
      simp only [List.map_cons, List.zipIdx_cons, List.cons.injEq, Prod.mk.injEq] at same
      have next : GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
          post failure rows = prefixPre config post failure (pc + 1) nodes :=
        funext fun state => propext (ih (pc + 1) rows state same.2).symm
      rw [prefixPre, GeneratedBodyVC.windowPrefixPre]
      simp only [same.1.1, same.1.2, next, true_implies]
      apply and_congr_right
      intro _
      constructor
      · intro checked ⟨⟩
        exact (row.reduced.exact () _ _ _).mpr (same.1.2.symm ▸ checked)
      · intro checked
        exact same.1.2 ▸ (row.reduced.exact () _ _ _).mp (checked ())

end PointerObservation.Fixture
