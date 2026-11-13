module

public import BlockBand.Angular.RatioPointwise
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The cutoff in `b₂` for the angular estimate

`stepSixCutoff R₀` is a `C¹` cutoff (`Angular.Ratio.Cutoff`) with `0 ≤ χ ≤ 1`, `χ = 1` on
`(-∞, R₀]` and `χ = 0` on `(R₀ + 1, ∞)`; its data `M₀ = 1`, `R₁ = R₀ + 1`, `M₁` depend on `R₀`
only. Consequently `|1 - χ(x)| ≤ 1{x > R₀}` (`abs_one_sub_le_indicator`), which is the
pointwise form of the cutoff removal.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Assembly

open BlockBand.Angular.Ratio

/-- The profile `x ↦ smoothTransition (R₀ + 1 - x)`. -/
def cutProfile (R₀ : ℝ) (x : ℝ) : ℝ := Real.smoothTransition (R₀ + 1 - x)

theorem contDiff_cutProfile (R₀ : ℝ) : ContDiff ℝ 1 (cutProfile R₀) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem deriv_smoothTransition_eq_zero {y : ℝ} (hy : y < 0 ∨ 1 < y) :
    deriv Real.smoothTransition y = 0 := by
  rcases hy with hy | hy
  · have h : Real.smoothTransition =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
    rw [h.deriv_eq]; simp
  · have h : Real.smoothTransition =ᶠ[nhds y] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact Real.smoothTransition.one_of_one_le (le_of_lt hz)
    rw [h.deriv_eq]; simp

/-- The derivative of the smooth transition is bounded. -/
theorem exists_deriv_smoothTransition_le : ∃ M : ℝ, 0 ≤ M ∧
    ∀ y, |deriv Real.smoothTransition y| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · exact (Real.norm_eq_abs _ ▸ hM y hy).trans (le_max_left _ _)
  · have : y < 0 ∨ 1 < y := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hy; exact hy
    rw [deriv_smoothTransition_eq_zero this, abs_zero]; exact le_max_right _ _

theorem deriv_cutProfile (R₀ x : ℝ) :
    deriv (cutProfile R₀) x = -deriv Real.smoothTransition (R₀ + 1 - x) := by
  have h1 : HasDerivAt (fun x => R₀ + 1 - x) (-1) x := (hasDerivAt_id x).const_sub (R₀ + 1)
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (R₀ + 1 - x))
      (R₀ + 1 - x) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _ |>.hasDerivAt
  have := h2.comp x h1
  unfold cutProfile
  rw [show (fun x => Real.smoothTransition (R₀ + 1 - x)) =
    (Real.smoothTransition ∘ fun x => R₀ + 1 - x) from rfl, this.deriv]; ring

/-- **The cutoff in `b₂`**: `χ = 1` on `b₂ ≤ R₀`, `χ = 0` on `b₂ > R₀ + 1`, `0 ≤ χ ≤ 1`. -/
def stepSixCutoff (R₀ : ℝ) : Cutoff where
  χ := cutProfile R₀
  R₁ := R₀ + 1
  M₀ := 1
  M₁ := Classical.choose exists_deriv_smoothTransition_le
  smooth := contDiff_cutProfile R₀
  nonneg := fun x => Real.smoothTransition.nonneg _
  le := fun x => Real.smoothTransition.le_one _
  deriv_le := fun x => by
    rw [deriv_cutProfile, abs_neg]
    exact (Classical.choose_spec exists_deriv_smoothTransition_le).2 _
  supp := fun x hx => Real.smoothTransition.zero_of_nonpos (by linarith)

theorem stepSixCutoff_R1 (R₀ : ℝ) : (stepSixCutoff R₀).R₁ = R₀ + 1 := rfl

theorem stepSixCutoff_M0 (R₀ : ℝ) : (stepSixCutoff R₀).M₀ = 1 := rfl

theorem stepSixCutoff_eq_one {R₀ x : ℝ} (hx : x ≤ R₀) : (stepSixCutoff R₀).χ x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- `|1 - χ(x)| ≤ 1{x > R₀}`. -/
theorem abs_one_sub_le_indicator (R₀ x : ℝ) :
    |1 - (stepSixCutoff R₀).χ x| ≤ Set.indicator (Set.Ioi R₀) 1 x := by
  by_cases hx : x ≤ R₀
  · rw [stepSixCutoff_eq_one hx, sub_self, abs_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · rw [Set.indicator_of_mem (show x ∈ Set.Ioi R₀ from lt_of_not_ge hx), Pi.one_apply]
    have h0 := (stepSixCutoff R₀).nonneg x
    have h1 : (stepSixCutoff R₀).χ x ≤ 1 := (stepSixCutoff R₀).le x
    exact abs_le.2 ⟨by linarith, by linarith⟩

end BlockBand.Angular.Assembly
