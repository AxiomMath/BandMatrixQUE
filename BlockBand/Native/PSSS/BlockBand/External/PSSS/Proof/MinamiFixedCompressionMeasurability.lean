module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedSelectedSampleMeasurability

/-!
# Measurability of the fixed-target ambient compression

The full public deformation reconstructed from an exterior sample and a selected matrix argument
depends jointly measurably on both.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 400000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The reconstructed full deformation is jointly measurable. -/
theorem measurable_reconstructedFullDeformation
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k) :
    Measurable (fun p : BlockProductDisintegration.ExteriorSample dims j ×
      Matrix (Fin (dims j)) (Fin (dims j)) ℂ =>
      reconstructedFullDeformation A₀ j p.1 p.2) := by
  apply (measurable_publicBlockDeformation dims A₀).comp
  apply (BlockProductDisintegration.split dims j).symm.measurable.comp
  exact measurable_fst.prodMk
    ((measurable_selectedSampleOfMatrix dims j).comp measurable_snd)

end PSSSNative.BlockBand.PSSS
