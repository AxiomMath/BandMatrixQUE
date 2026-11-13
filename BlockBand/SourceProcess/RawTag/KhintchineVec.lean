module

public import BlockBand.SourceProcess.RawTag.Khintchine
public import Mathlib.Data.Matrix.Mul

/-!
# Gaussian moments of `‖Sg‖²`

`lintegral_normSq_rpow_le`: for a standard circular vector `g` and `r ≥ 1`,
`E_g(Σₓ|(Sg)ₓ|²)^r ≤ 2M_{2r}(Σₓₐ|Sₓₐ|²)^r` (Khintchine), `M_{2r}` the Gaussian moment.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal

theorem enorm_rpow_eq_ofReal {x : ℝ} (hx : 0 ≤ x) {r : ℝ} (hr : 0 ≤ r) :
    ‖x‖ₑ ^ r = ENNReal.ofReal (x ^ r) := by
  rw [Real.enorm_eq_ofReal hx, ENNReal.ofReal_rpow_of_nonneg hx hr]

/-- **Khintchine for `‖Sg‖²`**: `E_g(Σₓ|(Sg)ₓ|²)^r ≤ 2M_{2r}(Σₓₐ|Sₓₐ|²)^r`. -/
theorem lintegral_normSq_rpow_le {W : ℕ} {m : Type*} [Fintype m] (S : Matrix m (Fin W) ℂ)
    {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ g, ENNReal.ofReal ((∑ x, ‖(S *ᵥ g) x‖ ^ 2) ^ r) ∂circularVectorLaw (Fin W) ≤
      ENNReal.ofReal (2 * gaussMoment (2 * r) * (∑ x, ∑ a, ‖S x a‖ ^ 2) ^ r) := by
  have hr0 : 0 < r := by linarith
  set μ := circularVectorLaw (Fin W)
  set M := 2 * gaussMoment (2 * r)
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (gaussMoment_nonneg _)
  set f : m → (Fin W → ℂ) → ℝ := fun x g => ‖(S *ᵥ g) x‖ ^ 2
  have hfm : ∀ x, Measurable (f x) := fun x => by
    simp only [f, mulVec, dotProduct]; fun_prop
  set σ : m → ℝ := fun x => ∑ a, ‖S x a‖ ^ 2
  have hσ : ∀ x, 0 ≤ σ x := fun x => Finset.sum_nonneg fun a _ => by positivity
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by simpa using ENNReal.ofReal_le_ofReal hr
  have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr0
  have hrr : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  have hsum : (fun g => ∑ x, f x g) = ∑ x, f x := by funext g; simp [Finset.sum_apply]
  -- each row
  have hrow : ∀ x, eLpNorm (f x) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (M ^ (1 / r) * σ x) := by
    intro x
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
      (hfm x).aestronglyMeasurable, hrr]
    have h1 : ∫⁻ g, ‖f x g‖ₑ ^ r ∂μ ≤ ENNReal.ofReal (M * σ x ^ r) := by
      have e : ∀ g, ‖f x g‖ₑ ^ r = ENNReal.ofReal (‖∑ a, S x a * g a‖ ^ (2 * r)) := by
        intro g
        rw [enorm_rpow_eq_ofReal (by positivity) hr0.le]
        congr 1
        show (‖(S *ᵥ g) x‖ ^ 2) ^ r = _
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        simp [mulVec, dotProduct]
      simp_rw [e]
      refine (lintegral_linear_circular_le (S x) (s := 2 * r) (by linarith)).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      simp only [M, σ]; congr 2; ring
    calc (∫⁻ g, ‖f x g‖ₑ ^ r ∂μ) ^ (1 / r) ≤ (ENNReal.ofReal (M * σ x ^ r)) ^ (1 / r) :=
          ENNReal.rpow_le_rpow h1 (by positivity)
      _ = ENNReal.ofReal (M ^ (1 / r) * σ x) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hM (Real.rpow_nonneg (hσ x) r))
            (by positivity), Real.mul_rpow hM (Real.rpow_nonneg (hσ x) r),
            ← Real.rpow_mul (hσ x), mul_one_div_cancel hr0.ne', Real.rpow_one]
  have hF : eLpNorm (fun g => ∑ x, f x g) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (M ^ (1 / r) * ∑ x, σ x) := by
    rw [hsum]
    refine (eLpNorm_sum_le (s := Finset.univ) hp1).trans ?_
    refine (Finset.sum_le_sum fun x _ => hrow x).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => mul_nonneg (by positivity) (hσ x),
      Finset.mul_sum]
  have hFm : Measurable fun g => ∑ x, f x g := Finset.measurable_sum _ fun x _ => hfm x
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hFm.aestronglyMeasurable,
    hrr] at hF
  have hF' := ENNReal.rpow_le_rpow hF (show (0 : ℝ) ≤ r by linarith)
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun x _ => hσ x)) hr0.le,
    Real.mul_rpow (by positivity) (Finset.sum_nonneg fun x _ => hσ x), ← Real.rpow_mul hM,
    one_div_mul_cancel hr0.ne', Real.rpow_one] at hF'
  calc ∫⁻ g, ENNReal.ofReal ((∑ x, ‖(S *ᵥ g) x‖ ^ 2) ^ r) ∂μ
      = ∫⁻ g, ‖∑ x, f x g‖ₑ ^ r ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [enorm_rpow_eq_ofReal (Finset.sum_nonneg fun x _ => by positivity) hr0.le]
    _ ≤ _ := hF'

end BlockBand.SourceProcess.RawTag
