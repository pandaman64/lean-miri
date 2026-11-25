#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Build Miri.Interpreter.Call before running this check.
baseline="${1:-68d4f078cc036440929d6fde863cda3583f87d35}"
mkdir -p scratch
scratch_dir="$(mktemp -d "$PWD/scratch/call-frame-agreement.XXXXXX")"
git show "${baseline}:Miri/Interpreter/Call.lean" > "$scratch_dir/baseline.txt"

python3 - "$scratch_dir" <<'PYTHON'
import sys
from pathlib import Path

scratch = Path(sys.argv[1])
source = (scratch / "baseline.txt").read_text()
require_start = source.index("private def require")
require_end = source.index("\n\n", require_start)
require = source[require_start:require_end].replace("private def require", "private def priorRequire")
start = source.index("def initStackFrame")
end = source.index("/-- One source dispatch", start)
initializer = source[start:end].replace("def initStackFrame", "private def priorInitStackFrame")
initializer = initializer.replace("    require (", "    priorRequire (").replace("  require (", "  priorRequire (")

header = r'''
import Miri.Interpreter.Call

namespace Miri.Interpreter.Call
open Miri.Memory Miri.MIR
variable {P S C E Other Extern FnABI ArgABI : Type}
local notation "Hooks" => CallHooks P S C E Other Extern FnABI ArgABI
local notation "M" => CallM S
''' + require + r'''


private theorem ordinaryAgreement {A : Type}
    (h : Hooks) (choice : C) (args : Array (FnArg P)) (callerAbis calleeAbis : Array ArgABI)
    (callerIndex calleeIndex : Nat) (dest : Place) (ty : TyId) (next : A) :
    (do
      let calleeAbi ← at? calleeAbis calleeIndex "missing callee ABI"
      let caller ← match args[callerIndex]? with
        | none => throw (.undefinedBehavior "calling a function with fewer arguments than it requires")
        | some arg => pure arg
      let callerAbi ← at? callerAbis callerIndex "missing caller ABI"
      passArgument h choice caller callerAbi calleeAbi calleeIndex dest ty false
      pure next : CallM S A) =
    (do
      initOrdinaryArgument h choice args callerAbis calleeAbis callerIndex calleeIndex dest ty
      pure next) := by
  cases arg : args[callerIndex]? <;>
    simp [initOrdinaryArgument, arg, map_eq_pure_bind, bind_assoc, -bind_pure_comp]

'''
proof = r'''
set_option maxHeartbeats 2000000 in
theorem initStackFrame_agrees (h : Hooks) (choice : C) (fnInstance : CallInstance)
    (loadedBody : LoadedBody) (callerFnAbi : FnABI) (args : Array (FnArg P))
    (withCallerLocation : Bool) (destination : RuntimeStackPlace P) (cont : ReturnContinuation) :
    initStackFrame h choice fnInstance loadedBody callerFnAbi args withCallerLocation destination cont =
      priorInitStackFrame h choice fnInstance loadedBody callerFnAbi args withCallerLocation destination cont := by
  simp only [initStackFrame, priorInitStackFrame, initFrameArguments, initFrameArgumentsBody, initFrameArgumentStep, finishFrameInit,
    Call.require_eq, priorRequire, ordinaryAgreement, map_eq_pure_bind, bind_assoc]
  try rfl

end Miri.Interpreter.Call

#print axioms Miri.Interpreter.Call.initStackFrame_agrees
'''
(scratch / "Agreement.lean").write_text(header + initializer + proof)
PYTHON

LEAN_PATH="${LEAN_PATH:-$PWD/.lake/build/lib/lean}" lean "$scratch_dir/Agreement.lean"
