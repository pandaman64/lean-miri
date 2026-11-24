import duplicate_prefix.ActualReferenceMetadata
import duplicate_prefix.EmptyReferenceContext
import duplicate_prefix.ProjectionMetadataFacts
import duplicate_prefix.ActualCurrentSlice
import duplicate_prefix.ReferenceMetadataFacts
import duplicate_prefix.RootCompilerFacts

namespace DuplicatePrefix.EmptyReferenceMetadata
open Miri Miri.ABI Miri.Input Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

open ActualReferenceMetadata CanonicalConfigFacts EmptyReferenceContext

noncomputable abbrev pointee := ProjectionMetadataFacts.sliceLayout
theorem pointee_ty : pointee.ty = 2 := ProjectionMetadataFacts.slice_layout_shape.1

export ActualReferenceMetadata (reference reference_ty pointee_layout reference_sized reference_repr)

theorem reference_queries (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (pointers : RootPointers) :
    TypedRetagFields.ReferenceQueries (adapted options remaining span pointers) reference.ty pointee.ty := by
  rw [reference_ty, pointee_ty]
  apply TypedRetagFields.adapted_reference_queries
  · exact RootMetadataQueries.mutable_slice_shape
  · exact RootMetadataQueries.mutable_slice_reference
  · exact RootMetadataQueries.slice_unpin
  · exact RootMetadataQueries.slice_unsafe_unpin
  · exact RootMetadataQueries.slice_freeze

theorem visitor_metadata (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (config options remaining span).validity.target = (config options remaining span).access.runtime ∧
    (config options remaining span).validity.metadataTail () 2 = pure .sliceOrStr ∧
    (config options remaining span).validity.opsemInhabited () 2 = pure true ∧
    (config options remaining span).validity.typeName () 1 = pure "&mut [u8]" ∧
    (config options remaining span).validity.classify () 1 = pure (.reference true) := by
  obtain ⟨pointers, table, discr, validity⟩ := (actual_fields options () remaining span).validity
  have target : (config options remaining span).validity.target = (config options remaining span).access.runtime := by
    rw [validity]; rfl
  have tail : (config options remaining span).validity.metadataTail =
      (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared (config options remaining span).validity).metadataTail := by
    rw [validity]; rfl
  have inhabit : (config options remaining span).validity.opsemInhabited =
      (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared (config options remaining span).validity).opsemInhabited := by
    rw [validity]; rfl
  have name : (config options remaining span).validity.typeName =
      (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared (config options remaining span).validity).typeName := by
    rw [validity]; rfl
  have kind : (config options remaining span).validity.classify =
      (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared (config options remaining span).validity).classify := by
    rw [validity]; rfl
  refine ⟨target, ?_, ?_, ?_, ?_⟩
  · rw [tail]; exact ReferenceMetadataFacts.hooks_metadata_tail _ ()
  · rw [inhabit]
    unfold CompilerFactAdapters.validityHooks
    dsimp only
    rw [show ReferenceMetadataFacts.prepared.context = RootMetadataQueries.context from rfl,
      ReferenceMetadataFacts.slice_inhabited]
    with_unfolding_all rfl
  · rw [name]; exact ReferenceMetadataFacts.hooks_reference_name _ ()
  · rw [kind]; exact ReferenceMetadataFacts.hooks_reference_kind _ ()

theorem visitor_target (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (config options remaining span).validity.target.base.pointerWidth = .w64 ∧
    (config options remaining span).validity.target.pointerSize = Size.ofBytes 8 := by
  rw [(visitor_metadata options remaining span).1, actual_access_runtime]
  exact ⟨rfl, rfl⟩

end DuplicatePrefix.EmptyReferenceMetadata
