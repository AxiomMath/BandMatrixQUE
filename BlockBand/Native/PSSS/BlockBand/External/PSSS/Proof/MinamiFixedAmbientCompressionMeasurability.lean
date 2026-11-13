module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedCompressionMeasurability

/-!
# Measurability of the fixed-target ambient compression

This module adds only the two constant ambient projector multiplications to
the measurable full public reconstruction.  It remains independent of every
energy, Cauchy, radial, and dyadic parameter in PSSS (2.13).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 300000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The reconstructed full ambient compression is jointly measurable. -/
theorem measurable_reconstructedFullCompression
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) :
    Measurable (fun p : BlockProductDisintegration.ExteriorSample dims j ×
      Matrix (Fin (dims j)) (Fin (dims j)) ℂ =>
      reconstructedFullCompression A₀ j φ p.1 p.2) := by
  let H := fun p : BlockProductDisintegration.ExteriorSample dims j ×
      Matrix (Fin (dims j)) (Fin (dims j)) ℂ =>
    (reconstructedFullDeformation A₀ j p.1 p.2).1
  have hH : Measurable H := measurable_subtype_coe.comp
    (measurable_reconstructedFullDeformation dims A₀ j)
  let P := orthogonalProjector (selectedAmbientDirection j φ)
  apply Measurable.subtype_mk
  change Measurable (fun p => P * H p * Pᴴ)
  rw [Matrix.measurable_iff]
  intro x y
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro z _
  apply Measurable.mul
  · apply Finset.measurable_sum
    intro w _
    exact measurable_const.mul (Matrix.measurable_iff.mp hH w z)
  · exact measurable_const

end PSSSNative.BlockBand.PSSS
