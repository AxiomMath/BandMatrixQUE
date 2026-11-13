module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedPredecessorMeasurability

/-!
# Selected-sample fixed-target predecessor

This module substitutes the projected selected GUE block into the corrected
fixed-target predecessor and identifies it with the ambient
compression of the original full public deformation.  This is the algebraic
content needed after the sphere-insertion step in PSSS (2.13); it does not
replace that step, since the compressed weight depends on the sphere direction.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 400000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- Correct fixed-target predecessor after substituting the projected selected
GUE matrix. -/
def fixedSelectedPredecessorWeight
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) (a b : ℝ) (r : ℕ)
    (p : BlockProductDisintegration.ExteriorSample dims j ×
      BlockProductDisintegration.SelectedSample dims j) : ℝ≥0∞ :=
  fixedTargetPredecessorWeight A₀ j φ a b r
    (p.1, orthProj φ * (p.2 ⟨j, by simp⟩).1 * orthProj φ)

/-- The selected matrix projection is jointly measurable. -/
theorem measurable_selectedProjectedMatrix
    {k : ℕ} (dims : Fin k → ℕ) (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) :
    Measurable (fun p : BlockProductDisintegration.ExteriorSample dims j ×
      BlockProductDisintegration.SelectedSample dims j =>
      orthProj φ * (p.2 ⟨j, by simp⟩).1 * orthProj φ) := by
  let V := fun p : BlockProductDisintegration.ExteriorSample dims j ×
      BlockProductDisintegration.SelectedSample dims j =>
    (p.2 ⟨j, by simp⟩).1
  have hV : Measurable V := measurable_subtype_coe.comp
    ((measurable_pi_apply (⟨j, by simp⟩ : {i : Fin k // ¬ i ≠ j})).comp
      measurable_snd)
  change Measurable (fun p => orthProj φ * V p * orthProj φ)
  rw [Matrix.measurable_iff]
  intro x y
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro z _
  apply Measurable.mul
  · apply Finset.measurable_sum
    intro w _
    exact measurable_const.mul (Matrix.measurable_iff.mp hV w z)
  · exact measurable_const

/-- The concrete selected-sample predecessor is jointly measurable. -/
theorem measurable_fixedSelectedPredecessorWeight
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) (a b : ℝ) (r : ℕ) :
    Measurable (fixedSelectedPredecessorWeight A₀ j φ a b r) := by
  apply (measurable_fixedTargetPredecessorWeight dims A₀ j φ a b r).comp
  exact measurable_fst.prodMk (measurable_selectedProjectedMatrix dims j φ)

/-- On a unit sphere direction the corrected selected weight is the
fixed-interval factorial count of the full original public deformation's
ambient compression, with exactly its canonical zero removed. -/
theorem fixedSelectedPredecessorWeight_eq_literal_compression
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) (hφ : ‖φ‖ = 1)
    (a b : ℝ) (r : ℕ)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j) :
    fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj) =
      (((eigenCount
        (compressHermitian
          (publicBlockDeformation A₀
            ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
          (selectedAmbientDirection j φ))
        (Set.Icc a b) -
          (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r : ℝ≥0∞)) := by
  unfold fixedSelectedPredecessorWeight fixedTargetPredecessorWeight
  rw [reconstructedFullCompression_projected_eq_compressHermitian
    A₀ j φ hφ Gext Gj]

end PSSSNative.BlockBand.PSSS
