import duplicate_prefix.LanguageZeroEntryFacts
import duplicate_prefix.RuntimeZeroEntryFacts

namespace DuplicatePrefix.RootGuardRelevance

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- Both emitted guards are dependency code under the stock relevance
configuration. Neither changes the suspended root's rank-255 cache. -/
theorem stock :
    DuplicatePrefix.LanguageZeroEntryFacts.rank #[] = 1 ∧
    DuplicatePrefix.RuntimeZeroEntryFacts.rank #[] = 1 := by
  constructor <;> with_unfolding_all rfl

#print axioms stock
end DuplicatePrefix.RootGuardRelevance
