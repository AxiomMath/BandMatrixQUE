module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Truncation of locally Lipschitz coefficients

Deterministic coefficient facts for the localization of SDEs with locally Lipschitz
coefficients. `E` is a real normed space; `F` any metric space.

* `radialRetraction R x = (R / max R ‖x‖) • x`: the radial retraction onto the closed ball
  `‖x‖ ≤ R`. It fixes the ball (`radialRetraction_of_norm_le`), maps into it
  (`norm_radialRetraction_le`) and is `2`-Lipschitz for `R > 0`
  (`lipschitzWith_radialRetraction`; any normed space, no inner product needed).
* `lipschitzWith_comp_radialRetraction`: if `E` is a proper space (e.g. finite
  dimensional) and `f : E → F` is locally Lipschitz, then `f ∘ radialRetraction R` is globally
  Lipschitz, and it agrees with `f` on the closed `R`-ball.
-/

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.SDE
open Metric Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial retraction onto the closed ball of radius `R` centred at `0`. -/
def radialRetraction (R : ℝ) (x : E) : E := (R / max R ‖x‖) • x

theorem radialRetraction_of_norm_le {R : ℝ} {x : E} (h : ‖x‖ ≤ R) : radialRetraction R x = x := by
  unfold radialRetraction
  rw [max_eq_left h]
  rcases eq_or_ne R 0 with hR | hR
  · have : x = 0 := norm_le_zero_iff.1 (hR ▸ h)
    simp [this]
  · rw [div_self hR, one_smul]

theorem norm_radialRetraction_le {R : ℝ} (hR : 0 ≤ R) (x : E) : ‖radialRetraction R x‖ ≤ R := by
  unfold radialRetraction
  rcases eq_or_lt_of_le hR with h0 | hpos
  · simp [← h0]
  have hm : 0 < max R ‖x‖ := lt_max_of_lt_left hpos
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg hR hm.le), div_mul_eq_mul_div,
    div_le_iff₀ hm]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hR

theorem mem_closedBall_radialRetraction {R : ℝ} (hR : 0 ≤ R) (x : E) :
    radialRetraction R x ∈ closedBall (0 : E) R := by
  rw [mem_closedBall, dist_zero_right]
  exact norm_radialRetraction_le hR x

/-- One-sided form of the `2`-Lipschitz estimate. -/
theorem norm_radialRetraction_sub_le_aux {R : ℝ} (hR : 0 < R) {x y : E}
    (hxy : max R ‖y‖ ≤ max R ‖x‖) :
    ‖radialRetraction R x - radialRetraction R y‖ ≤ 2 * ‖x - y‖ := by
  unfold radialRetraction
  set mx := max R ‖x‖
  set my := max R ‖y‖
  have hmy : 0 < my := lt_max_of_lt_left hR
  have hmx : 0 < mx := hmy.trans_le hxy
  have hcx : R / mx ≤ 1 := (div_le_one hmx).2 (le_max_left _ _)
  have hcx0 : 0 ≤ R / mx := div_nonneg hR.le hmx.le
  have hc : R / mx ≤ R / my := div_le_div_of_nonneg_left hR.le hmy hxy
  have hdiff : mx - my ≤ ‖x - y‖ := by
    have h1 := abs_max_sub_max_le_abs ‖x‖ ‖y‖ R
    rw [max_comm ‖x‖ R, max_comm ‖y‖ R] at h1
    exact (le_abs_self _).trans (h1.trans (abs_norm_sub_norm_le x y))
  have hy : ‖y‖ ≤ my := le_max_right _ _
  have hsplit : (R / mx) • x - (R / my) • y = (R / mx) • (x - y) + (R / mx - R / my) • y := by
    rw [smul_sub, sub_smul]; abel
  have h2 : (R / my - R / mx) * ‖y‖ ≤ mx - my := by
    calc (R / my - R / mx) * ‖y‖ ≤ (R / my - R / mx) * my :=
          mul_le_mul_of_nonneg_left hy (sub_nonneg.2 hc)
      _ = (R / mx) * (mx - my) := by field_simp
      _ ≤ 1 * (mx - my) := mul_le_mul_of_nonneg_right hcx (sub_nonneg.2 hxy)
      _ = mx - my := one_mul _
  rw [hsplit]
  calc ‖(R / mx) • (x - y) + (R / mx - R / my) • y‖
      ≤ ‖(R / mx) • (x - y)‖ + ‖(R / mx - R / my) • y‖ := norm_add_le _ _
    _ = R / mx * ‖x - y‖ + (R / my - R / mx) * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hcx0, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.2 hc), neg_sub]
    _ ≤ 1 * ‖x - y‖ + ‖x - y‖ := by
        gcongr
        exact h2.trans hdiff
    _ = 2 * ‖x - y‖ := by ring

/-- The radial retraction onto a closed ball of positive radius is `2`-Lipschitz. -/
theorem lipschitzWith_radialRetraction {R : ℝ} (hR : 0 < R) :
    LipschitzWith 2 (radialRetraction (E := E) R) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat]
  rcases le_total (max R ‖y‖) (max R ‖x‖) with h | h
  · exact norm_radialRetraction_sub_le_aux hR h
  · rw [norm_sub_rev, norm_sub_rev x]
    exact norm_radialRetraction_sub_le_aux hR h

/-- **Truncation of a locally Lipschitz coefficient.** On a proper (e.g. finite-dimensional)
normed space, `f ∘ radialRetraction R` is globally Lipschitz and equals `f` on the closed
`R`-ball. -/
theorem lipschitzWith_comp_radialRetraction [ProperSpace E] {F : Type*}
    [PseudoMetricSpace F] {f : E → F} (hf : LocallyLipschitz f) {R : ℝ} (hR : 0 < R) :
    (∃ K, LipschitzWith K (f ∘ radialRetraction R)) ∧
      ∀ x : E, ‖x‖ ≤ R → (f ∘ radialRetraction R) x = f x := by
  refine ⟨?_, fun x hx => by simp [radialRetraction_of_norm_le hx]⟩
  obtain ⟨K, hK⟩ := (hf.locallyLipschitzOn (s := closedBall (0 : E) R)
    ).exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 R)
  refine ⟨K * 2, lipschitzOnWith_univ.1 ?_⟩
  exact hK.comp ((lipschitzWith_radialRetraction hR).lipschitzOnWith)
    fun x _ => mem_closedBall_radialRetraction hR.le x

/-- Finite-dimensional specialization of the truncation lemma. -/
theorem lipschitzWith_comp_radialRetraction_of_finiteDimensional
    [FiniteDimensional ℝ E] {F : Type*} [PseudoMetricSpace F] {f : E → F}
    (hf : LocallyLipschitz f) {R : ℝ} (hR : 0 < R) :
    (∃ K, LipschitzWith K (f ∘ radialRetraction R)) ∧
      ∀ x : E, ‖x‖ ≤ R → (f ∘ radialRetraction R) x = f x :=
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  lipschitzWith_comp_radialRetraction hf hR

end BlockBand.SourceProcess.Stochastic.SDE
