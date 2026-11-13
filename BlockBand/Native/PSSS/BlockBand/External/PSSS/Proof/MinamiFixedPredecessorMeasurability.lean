module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedAmbientCompressionMeasurability
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiMovingCountMeasurability

/-!
# Measurability of the fixed-target predecessor

The corrected predecessor in the compression representation of PSSS (2.13)
uses the fixed target `Icc a b` and removes only the ambient compression's
canonical zero.  In particular, this theorem has no radial `xi` argument.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 300000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The fixed-target ambient-compression predecessor is jointly measurable in the
fixed exterior and selected matrix input. -/
theorem measurable_fixedTargetPredecessorWeight
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) (a b : ℝ) (r : ℕ) :
    Measurable (fixedTargetPredecessorWeight A₀ j φ a b r) := by
  have hcount : Measurable (fun p :
      BlockProductDisintegration.ExteriorSample dims j ×
        Matrix (Fin (dims j)) (Fin (dims j)) ℂ =>
      eigenCount (reconstructedFullCompression A₀ j φ p.1 p.2)
        (Set.Icc a b)) :=
    (measurable_eigenCount_Icc a b).comp
      (measurable_reconstructedFullCompression dims A₀ j φ)
  have hpred : Measurable (fun p :
      BlockProductDisintegration.ExteriorSample dims j ×
        Matrix (Fin (dims j)) (Fin (dims j)) ℂ =>
      eigenCount (reconstructedFullCompression A₀ j φ p.1 p.2)
        (Set.Icc a b) -
        (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)) := by
    fun_prop
  exact Measurable.ennreal_descFactorial _ hpred r

end PSSSNative.BlockBand.PSSS
