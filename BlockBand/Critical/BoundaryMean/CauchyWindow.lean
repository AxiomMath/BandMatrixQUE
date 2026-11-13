module

public import BlockBand.Critical.Collar.Density.SecondMoment

/-!
# Two-sided Cauchy average of a window estimate

The bridge from the density form of the sharp collar density estimate to the Poisson-regularized
resolvent form `HermitianCollarMeanStatement` in the exact boundary-mean theorem: a window
`|x| ≤ σ` and a Cauchy tail.

Deterministic real analysis on `ℝ` with Lebesgue measure. `lintegral_cauchyKernel_two_sided`:
for a nonnegative `ρ` with `|ρ(x) - c| ≤ A` on `|x| ≤ σ` and `∫P₁ρ ≤ T₁`,
`c - A - ν(1+σ⁻²)c ≤ ∫P_νρ ≤ c + A + ν(1+σ⁻²)T₁` (`P_ν ≤ ν(1+σ⁻²)P₁` off the window,
`Density.cauchyKernel_le_tail`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open MeasureTheory Filter Topology Matrix
open BlockBand.Critical.WeightedDensity BlockBand.Critical.Collar.Density
open scoped ENNReal

/-- **Two-sided Cauchy average of a window estimate.** If `ρ ≥ 0` is continuous with
`|ρ(x) - c| ≤ A` for `|x| ≤ σ` and `∫P₁ρ ≤ T₁`, then for `ν > 0`
`c - A - ν(1+σ⁻²)c ≤ ∫P_ν ρ ≤ c + A + ν(1+σ⁻²)T₁` (lintegral form). -/
theorem lintegral_cauchyKernel_two_sided {ρ : ℝ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    {c A σ T₁ ν : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hT₁ : 0 ≤ T₁) (hσ : 0 < σ) (hν : 0 < ν)
    (hwin : ∀ x, |x| ≤ σ → |ρ x - c| ≤ A)
    (hT : ∫⁻ x, ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x) ≤ ENNReal.ofReal T₁) :
    ENNReal.ofReal (c - A - ν * (1 + σ⁻¹ ^ 2) * c) ≤
        ∫⁻ x, ENNReal.ofReal (cauchyKernel ν (0 - x) * ρ x) ∧
      ∫⁻ x, ENNReal.ofReal (cauchyKernel ν (0 - x) * ρ x) ≤
        ENNReal.ofReal (c + A + ν * (1 + σ⁻¹ ^ 2) * T₁) := by
  have hP0 : ∀ ε' x, 0 < ε' → 0 ≤ cauchyKernel ε' x := fun ε' x h => cauchyKernel_nonneg h.le x
  have hk0 : 0 ≤ ν * (1 + σ⁻¹ ^ 2) := by positivity
  have hmP : ∀ ε', 0 < ε' → Measurable fun x : ℝ => ENNReal.ofReal (cauchyKernel ε' (0 - x)) :=
    fun ε' hε' => (((continuous_cauchyKernel hε').comp
      (continuous_const.sub continuous_id)).measurable).ennreal_ofReal
  constructor
  · have hpt : ∀ x, ENNReal.ofReal (cauchyKernel ν (0 - x)) * ENNReal.ofReal (c - A) ≤
        ENNReal.ofReal (cauchyKernel ν (0 - x) * ρ x) +
          ENNReal.ofReal (cauchyKernel 1 (0 - x)) * ENNReal.ofReal (ν * (1 + σ⁻¹ ^ 2) * c) := by
      intro x
      rw [← ENNReal.ofReal_mul (hP0 ν _ hν)]
      by_cases hx : |x| ≤ σ
      · refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
        have := (abs_le.1 (hwin x hx)).1
        exact mul_le_mul_of_nonneg_left (by linarith) (hP0 ν _ hν)
      · push Not at hx
        have ht := cauchyKernel_le_tail hν hσ (x := 0 - x) (by rw [zero_sub, abs_neg]; exact hx.le)
        refine le_add_left ?_
        rw [← ENNReal.ofReal_mul (hP0 1 _ one_pos)]
        refine ENNReal.ofReal_le_ofReal ?_
        rcases le_or_gt (c - A) 0 with h | h
        · have : cauchyKernel ν (0 - x) * (c - A) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (hP0 ν _ hν) h
          have : 0 ≤ cauchyKernel 1 (0 - x) * (ν * (1 + σ⁻¹ ^ 2) * c) := by
            have := hP0 1 (0 - x) one_pos
            positivity
          linarith
        · calc cauchyKernel ν (0 - x) * (c - A) ≤ cauchyKernel ν (0 - x) * c :=
                mul_le_mul_of_nonneg_left (by linarith) (hP0 ν _ hν)
            _ ≤ ν * (1 + σ⁻¹ ^ 2) * cauchyKernel 1 (0 - x) * c :=
                mul_le_mul_of_nonneg_right ht hc
            _ = _ := by ring
    have hint := lintegral_mono (μ := volume) hpt
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_cauchyKernel hν, one_mul,
      lintegral_add_right _ ((hmP 1 one_pos).mul_const _),
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_cauchyKernel one_pos,
      one_mul] at hint
    rw [show c - A - ν * (1 + σ⁻¹ ^ 2) * c = (c - A) - ν * (1 + σ⁻¹ ^ 2) * c by ring,
      ENNReal.ofReal_sub _ (by positivity)]
    exact tsub_le_iff_right.2 hint
  · have hpt : ∀ x, ENNReal.ofReal (cauchyKernel ν (0 - x) * ρ x) ≤
        ENNReal.ofReal (cauchyKernel ν (0 - x)) * ENNReal.ofReal (c + A) +
          ENNReal.ofReal (ν * (1 + σ⁻¹ ^ 2)) *
            ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x) := by
      intro x
      by_cases hx : |x| ≤ σ
      · refine le_add_right ?_
        rw [← ENNReal.ofReal_mul (hP0 ν _ hν)]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hP0 ν _ hν))
        linarith [(abs_le.1 (hwin x hx)).2]
      · push Not at hx
        have ht := cauchyKernel_le_tail hν hσ (x := 0 - x) (by rw [zero_sub, abs_neg]; exact hx.le)
        refine le_add_left ?_
        rw [← ENNReal.ofReal_mul hk0]
        refine ENNReal.ofReal_le_ofReal ?_
        calc cauchyKernel ν (0 - x) * ρ x ≤ ν * (1 + σ⁻¹ ^ 2) * cauchyKernel 1 (0 - x) * ρ x :=
              mul_le_mul_of_nonneg_right ht (hρ0 x)
          _ = _ := by ring
    have hm1 := (hmP ν hν).mul_const (ENNReal.ofReal (c + A))
    calc ∫⁻ x, ENNReal.ofReal (cauchyKernel ν (0 - x) * ρ x)
        ≤ ∫⁻ x, (ENNReal.ofReal (cauchyKernel ν (0 - x)) * ENNReal.ofReal (c + A) +
            ENNReal.ofReal (ν * (1 + σ⁻¹ ^ 2)) *
              ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x)) := lintegral_mono hpt
      _ = ENNReal.ofReal (c + A) + ENNReal.ofReal (ν * (1 + σ⁻¹ ^ 2)) *
            ∫⁻ x, ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x) := by
          rw [lintegral_add_left hm1, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
            lintegral_ofReal_cauchyKernel hν, one_mul,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (c + A) + ENNReal.ofReal (ν * (1 + σ⁻¹ ^ 2)) * ENNReal.ofReal T₁ := by
          gcongr
      _ ≤ ENNReal.ofReal (c + A + ν * (1 + σ⁻¹ ^ 2) * T₁) := by
          rw [← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_add (by linarith) (by positivity)]

end BlockBand.Critical.BoundaryMean
