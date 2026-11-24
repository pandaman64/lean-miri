import duplicate_prefix.ActiveReleaseOwned
import duplicate_prefix.CanonicalConfigFacts
import SourceDomain

namespace DuplicatePrefix.RootZeroShallowReturn

open Miri Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
open SourceDomain

/-- Allocation and scheduling data for the source slice. It is independent
of the frame's own return destination and protector ledger. -/
structure RetainedSlice (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) where
  id : AllocId
  tag : BorTag
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  present : machine.memory.live[id]? = some entry
  tracker : MachineHooks.BorrowState
  tracked : machine.borrowTracker = some tracker
  source : UniIndex
  root : UniIndex
  indexed : entry.allocation.extra.indexOfTag tag = some source
  roots : entry.allocation.extra.roots = #[root]
  node : TreeNode
  found : entry.allocation.extra.nodeAt source = some node
  unexposed : node.isExposed = false
  thread : ThreadRecord
  active : machine.threads.activeThread? = some thread

end DuplicatePrefix.RootZeroShallowReturn
