module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.FixedVectorWeightedAllThresholds
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerSelectedBlockSchur

/-!
# Weighted fixed-vector averaging in a selected public block

The weighted fixed-vector tail estimate for the inverse `(A + G_j)⁻¹ φ` transfers to the selected
block coordinates of the public block-product disintegration, with a weight that depends only on
the projected block `Pφ G_j Pφ`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators

/-- The weighted inverse-vector tail estimate in selected-block coordinates: the event
`t √(dims j) ≤ ‖(A + G_j)⁻¹ φ‖`, weighted by a function of `Pφ G_j Pφ`, has mass at most
`C / t` times the total weight, for every `t > 0`. -/
theorem selectedBlock_fixedVector_tail_weighted_all_positive :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A : HermitianMatrix (Fin (dims j)))
      (φ : EuclideanSpace ℂ (Fin (dims j))), ‖φ‖ = 1 →
      ∀ (F : Matrix (Fin (dims j)) (Fin (dims j)) ℂ → ℝ≥0∞), Measurable F →
      ∀ t : ℝ, 0 < t →
      (∫⁻ Gj, Set.indicator
          {Gj : BlockProductDisintegration.SelectedSample dims j |
            t * Real.sqrt (dims j) ≤
              ‖(WithLp.toLp 2
                ((A.1 + (Gj ⟨j, by simp⟩).1)⁻¹ *ᵥ WithLp.ofLp φ) :
                EuclideanSpace ℂ (Fin (dims j)))‖}
          (fun _ => (1 : ℝ≥0∞)) Gj *
            F (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)
        ∂BlockProductDisintegration.selectedMeasure dims hd j) ≤
        ENNReal.ofReal (C / t) *
          ∫⁻ Gj, F (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)
            ∂BlockProductDisintegration.selectedMeasure dims hd j := by
  obtain ⟨C, hC, htail⟩ := fixedVector_tail_weighted_all_positive
  refine ⟨C, hC, ?_⟩
  intro k dims hd j A φ hφ F hF t ht
  let f : HermitianMatrix (Fin (dims j)) → ℝ≥0∞ := fun V =>
    Set.indicator {V : HermitianMatrix (Fin (dims j)) |
        t * Real.sqrt (dims j) ≤
          ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ WithLp.ofLp φ) :
            EuclideanSpace ℂ (Fin (dims j)))‖}
      (fun _ => (1 : ℝ≥0∞)) V * F (orthProj φ * V.1 * orthProj φ)
  let w : HermitianMatrix (Fin (dims j)) → ℝ≥0∞ := fun V =>
    F (orthProj φ * V.1 * orthProj φ)
  have hw : Measurable w := by
    apply hF.comp
    rw [Matrix.measurable_iff]
    intro p q
    fun_prop
  have hevent : MeasurableSet {V : HermitianMatrix (Fin (dims j)) |
      t * Real.sqrt (dims j) ≤
        ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ WithLp.ofLp φ) :
          EuclideanSpace ℂ (Fin (dims j)))‖} := by
    apply measurableSet_le measurable_const
    have hinv : Measurable fun V : HermitianMatrix (Fin (dims j)) =>
        (A.1 + V.1)⁻¹ :=
      PSSSNative.BlockBand.Measurable.matrixNonsingInv
        (continuous_const.add continuous_subtype_val).measurable
    have hmul : Measurable fun V : HermitianMatrix (Fin (dims j)) =>
        (A.1 + V.1)⁻¹ *ᵥ WithLp.ofLp φ := by
      rw [measurable_pi_iff]
      intro p
      unfold Matrix.mulVec dotProduct
      fun_prop
    fun_prop
  have hf : Measurable f := by
    exact (measurable_const.indicator hevent).mul hw
  calc
    _ = ∫⁻ V, f V
        ∂(PSSSNative.BlockBand.GUE (dims j) (1 / (dims j : ℝ)) :
          Measure (HermitianMatrix (Fin (dims j)))) := by
      rw [← lintegral_selectedMeasure_eval dims hd j f hf]
      rfl
    _ ≤ ENNReal.ofReal (C / t) *
        ∫⁻ V, w V
          ∂(PSSSNative.BlockBand.GUE (dims j) (1 / (dims j : ℝ)) :
            Measure (HermitianMatrix (Fin (dims j)))) := by
      exact htail (dims j) (hd j) A φ hφ F hF t ht
    _ = ENNReal.ofReal (C / t) *
        ∫⁻ Gj, F (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)
          ∂BlockProductDisintegration.selectedMeasure dims hd j := by
      rw [lintegral_selectedMeasure_eval dims hd j w hw]

end PSSSNative.BlockBand.PSSS
