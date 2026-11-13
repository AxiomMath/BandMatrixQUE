module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiWeightedSelectedBlock
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVector

/-!
# Uniform-direction weighted selected-block averaging

The selected-block weighted inverse tail is integrated over the
uniform complex-sphere law.  The compression weight may depend on the sampled
direction, as required by the positive rank-one compression step.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators

/-- Weighted inverse-vector averaging jointly over the selected normalized-GUE
block and an independent uniform direction.  The same absolute constant works
for every positive threshold. -/
theorem selectedBlock_uniformSphere_weighted_tail_all_positive :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A : HermitianMatrix (Fin (dims j)))
      (F : EuclideanSpace ℂ (Fin (dims j)) →
        Matrix (Fin (dims j)) (Fin (dims j)) ℂ → ℝ≥0∞),
      (∀ φ, Measurable (F φ)) →
      ∀ t : ℝ, 0 < t →
      (∫⁻ φ, ∫⁻ Gj, Set.indicator
          {Gj : BlockProductDisintegration.SelectedSample dims j |
            t * Real.sqrt (dims j) ≤
              ‖(WithLp.toLp 2
                ((A.1 + (Gj ⟨j, by simp⟩).1)⁻¹ *ᵥ WithLp.ofLp φ) :
                EuclideanSpace ℂ (Fin (dims j)))‖}
          (fun _ => (1 : ℝ≥0∞)) Gj *
            F φ (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)
          ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j)) ≤
        ENNReal.ofReal (C / t) *
          ∫⁻ φ, ∫⁻ Gj,
            F φ (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)
            ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j) := by
  obtain ⟨C, hC, htail⟩ := selectedBlock_fixedVector_tail_weighted_all_positive
  refine ⟨C, hC, ?_⟩
  intro k dims hd j A F hF t ht
  calc
    _ ≤ ∫⁻ φ, ENNReal.ofReal (C / t) *
          (∫⁻ Gj, F φ (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)
            ∂BlockProductDisintegration.selectedMeasure dims hd j)
        ∂uniformSphere (dims j) := by
      apply lintegral_mono_ae
      filter_upwards [uniformSphere_norm_eq_one (hd j)] with φ hφ
      exact htail dims hd j A φ hφ (F φ) (hF φ) t ht
    _ = ENNReal.ofReal (C / t) *
          ∫⁻ φ, ∫⁻ Gj,
            F φ (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)
            ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j) := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top

/-- Cell-width form used in the Minami partition.  A cell of width `δ`
produces the exact inverse-vector threshold `1/(5√d_j δ)` and costs
`5 C d_j δ`. -/
theorem selectedBlock_uniformSphere_weighted_cell :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A : HermitianMatrix (Fin (dims j)))
      (F : EuclideanSpace ℂ (Fin (dims j)) →
        Matrix (Fin (dims j)) (Fin (dims j)) ℂ → ℝ≥0∞),
      (∀ φ, Measurable (F φ)) →
      ∀ δ : ℝ, 0 < δ →
      (∫⁻ φ, ∫⁻ Gj, Set.indicator
          {Gj : BlockProductDisintegration.SelectedSample dims j |
            1 / (5 * Real.sqrt (dims j) * δ) ≤
              ‖(WithLp.toLp 2
                ((A.1 + (Gj ⟨j, by simp⟩).1)⁻¹ *ᵥ WithLp.ofLp φ) :
                EuclideanSpace ℂ (Fin (dims j)))‖}
          (fun _ => (1 : ℝ≥0∞)) Gj *
            F φ (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)
          ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j)) ≤
        ENNReal.ofReal (5 * C * dims j * δ) *
          ∫⁻ φ, ∫⁻ Gj,
            F φ (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)
            ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j) := by
  obtain ⟨C, hC, htail⟩ :=
    selectedBlock_uniformSphere_weighted_tail_all_positive
  refine ⟨C, hC, ?_⟩
  intro k dims hd j A F hF δ hδ
  let t : ℝ := 1 / (5 * (dims j : ℝ) * δ)
  have ht : 0 < t := by
    dsimp [t]
    exact one_div_pos.mpr
      (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hd j)) hδ)
  have hsqrt : 0 < Real.sqrt (dims j : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hd j)
  have hsqrtSq : Real.sqrt (dims j : ℝ) * Real.sqrt (dims j : ℝ) = dims j := by
    rw [Real.mul_self_sqrt]
    positivity
  have hthreshold :
      t * Real.sqrt (dims j) = 1 / (5 * Real.sqrt (dims j) * δ) := by
    dsimp [t]
    calc
      1 / (5 * (dims j : ℝ) * δ) * Real.sqrt (dims j) =
          Real.sqrt (dims j) / (5 * (dims j : ℝ) * δ) := by ring
      _ = Real.sqrt (dims j) /
          (5 * (Real.sqrt (dims j) * Real.sqrt (dims j)) * δ) := by
            rw [hsqrtSq]
      _ = 1 / (5 * Real.sqrt (dims j) * δ) := by
            field_simp [ne_of_gt hsqrt, ne_of_gt hδ]
  have hcoef : C / t = 5 * C * dims j * δ := by
    dsimp [t]
    field_simp
  simpa only [hthreshold, hcoef] using htail dims hd j A F hF t ht

end PSSSNative.BlockBand.PSSS
