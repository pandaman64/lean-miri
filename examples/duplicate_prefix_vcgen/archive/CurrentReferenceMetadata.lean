import duplicate_prefix.ProjectionMetadataFacts
import duplicate_prefix.ReferenceMetadataFacts
import duplicate_prefix.ActualCurrentSlice

namespace DuplicatePrefix.CurrentReferenceMetadata
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR
open CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

abbrev refTy (mutable : Bool) : TyId := if mutable then 1 else 7
abbrev refName (mutable : Bool) : String := if mutable then "&mut [u8]" else "&[u8]"

theorem named (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (mutable : Bool) :
    (PreparedContracts.actualConfig options () remaining span).validity.typeName () (refTy mutable) =
      pure (refName mutable) := by
  obtain ⟨pointers, table, discriminant, validity⟩ :=
    (CanonicalConfigFacts.actual_fields options () remaining span).validity
  rw [validity]
  cases mutable
  · with_unfolding_all rfl
  · with_unfolding_all rfl

theorem classified (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (mutable : Bool) :
    (PreparedContracts.actualConfig options () remaining span).validity.classify () (refTy mutable) =
      pure (.reference mutable) := by
  obtain ⟨pointers, table, discriminant, validity⟩ :=
    (CanonicalConfigFacts.actual_fields options () remaining span).validity
  rw [validity]
  cases mutable
  · with_unfolding_all rfl
  · with_unfolding_all rfl

theorem metadataTail (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).validity.metadataTail () 2 =
      pure .sliceOrStr := by
  obtain ⟨pointers, table, discriminant, validity⟩ :=
    (CanonicalConfigFacts.actual_fields options () remaining span).validity
  rw [validity]
  with_unfolding_all rfl

theorem inhabited (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).validity.opsemInhabited () 2 =
      pure true := by
  obtain ⟨pointers, table, discriminant, validity⟩ :=
    (CanonicalConfigFacts.actual_fields options () remaining span).validity
  rw [validity]
  with_unfolding_all rfl

end DuplicatePrefix.CurrentReferenceMetadata

#print axioms DuplicatePrefix.CurrentReferenceMetadata.named
#print axioms DuplicatePrefix.CurrentReferenceMetadata.classified
#print axioms DuplicatePrefix.CurrentReferenceMetadata.metadataTail
#print axioms DuplicatePrefix.CurrentReferenceMetadata.inhabited
