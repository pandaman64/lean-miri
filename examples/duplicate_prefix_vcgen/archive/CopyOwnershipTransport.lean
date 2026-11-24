import SourceDomain

namespace DuplicatePrefix.CopyOwnershipTransport
open Miri Miri.Memory Miri.Interpreter
open PreparedArguments SourceDomain

/-- Carry the same region across control-only steps of the interpreter. -/
def storageAfter {K U : Type} {before after : MachineHooks.State K U} {length : UInt64}
    (storage : InitializedRegion before length) (memory : after.machine.memory = before.machine.memory) :
    InitializedRegion after length where
  id := storage.id
  relativeStart := storage.relativeStart
  entry := storage.entry
  live := by rw [memory]; exact storage.live
  writable := storage.writable
  backed := storage.backed
  fits := storage.fits
  initialized := storage.initialized

/-- The source authority remains available when the owned heap and its
global tracker are preserved while control advances. -/
def rightsAfter {K U : Type} {before after : MachineHooks.State K U} {length : UInt64} {tag : BorTag}
    {storage : InitializedRegion before length} (right : ExclusiveRegion before length storage tag)
    (memory : after.machine.memory = before.machine.memory) (tracker : after.machine.borrowTracker = before.machine.borrowTracker) :
    ExclusiveRegion after length (storageAfter storage memory) tag where
  tracker := right.tracker
  tracked := tracker.trans right.tracked
  coherent := right.coherent
  source := right.source
  tagKnown := right.tagKnown
  sourcePresent := right.sourcePresent
  covers := right.covers
  exclusive := right.exclusive

end DuplicatePrefix.CopyOwnershipTransport

#print axioms DuplicatePrefix.CopyOwnershipTransport.storageAfter
#print axioms DuplicatePrefix.CopyOwnershipTransport.rightsAfter
