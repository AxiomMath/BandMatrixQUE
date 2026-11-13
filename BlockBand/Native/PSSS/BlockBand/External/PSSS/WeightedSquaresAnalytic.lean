module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FiniteContourShift
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.WeightedSquaresEnvelope
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Holomorphy of the continued Gaussian-square factors

The factor `(1 - 2iw)^{-1/2} exp(i w β² / (1 - 2iw))` is holomorphic where `1 - 2iw` has positive
real part, and so are finite products of such factors. Each factor is uniformly bounded on regions
where this real part is bounded below by a positive constant.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex

/-- The principal-branch Gaussian-square transform is analytic wherever its
denominator lies in the open right half-plane. -/
theorem analyticAt_gaussianSquareTransform {w : ℂ} (β : ℝ)
    (hw : 0 < (gaussianSquareDenominator w).re) :
    AnalyticAt ℂ (fun z => gaussianSquareTransform z β) w := by
  have hd : AnalyticAt ℂ gaussianSquareDenominator w := by
    unfold gaussianSquareDenominator
    fun_prop
  have hslit : gaussianSquareDenominator w ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hw)
  have hpow : AnalyticAt ℂ
      (fun z => gaussianSquareDenominator z ^ (-(1 / 2 : ℂ))) w := by
    exact AnalyticAt.cpow hd analyticAt_const hslit
  have hne := gaussianSquareDenominator_ne_zero hw
  have harg : AnalyticAt ℂ
      (fun z => I * z / gaussianSquareDenominator z * (β : ℂ) ^ 2) w := by
    exact ((analyticAt_const.mul analyticAt_id).div hd hne).mul analyticAt_const
  exact hpow.mul harg.cexp'

/-- Holomorphy of a finite product of continued square transforms under the
common positive-real-part condition. -/
theorem analyticAt_gaussianSquareTransform_prod {n : ℕ}
    (w : Fin n → ℂ → ℂ) (β : Fin n → ℝ) (z : ℂ)
    (hw : ∀ j, AnalyticAt ℂ (w j) z)
    (hhalf : ∀ j, 0 < (gaussianSquareDenominator (w j z)).re) :
    AnalyticAt ℂ (fun u => ∏ j, gaussianSquareTransform (w j u) (β j)) z := by
  classical
  suffices ∀ s : Finset (Fin n),
      AnalyticAt ℂ (fun u => ∏ j ∈ s,
        gaussianSquareTransform (w j u) (β j)) z by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z)
  | @insert j s hjs ih =>
      have hj := (analyticAt_gaussianSquareTransform (β j) (hhalf j)).comp (hw j)
      rw [show ((fun q => gaussianSquareTransform q (β j)) ∘ w j) =
          (fun u => gaussianSquareTransform (w j u) (β j)) by rfl] at hj
      have hp := hj.mul ih
      rw [show
          (fun u => gaussianSquareTransform (w j u) (β j)) *
              (fun u => ∏ j ∈ s, gaussianSquareTransform (w j u) (β j)) =
            (fun u => gaussianSquareTransform (w j u) (β j) *
              ∏ j ∈ s, gaussianSquareTransform (w j u) (β j)) by rfl] at hp
      simpa only [Finset.prod_insert hjs] using hp

/-- Algebraic identity which makes the shifted exponential uniformly bounded:
the apparent linear numerator is a bounded rational function of the Gaussian
denominator. -/
theorem I_mul_div_gaussianSquareDenominator (w : ℂ)
    (hw : gaussianSquareDenominator w ≠ 0) :
    I * w / gaussianSquareDenominator w =
      (gaussianSquareDenominator w)⁻¹ / 2 - 1 / 2 := by
  field_simp [hw]
  unfold gaussianSquareDenominator
  ring

/-- A crude but uniform bound for one continued Gaussian-square factor on any
region where the real part of its denominator is bounded below by `c > 0`. -/
theorem norm_gaussianSquareTransform_le_of_re_ge {w : ℂ} (β c : ℝ)
    (hc : 0 < c) (hw : c ≤ (gaussianSquareDenominator w).re) :
    ‖gaussianSquareTransform w β‖ ≤
      c ^ (-(1 / 2 : ℝ)) *
        Real.exp (((c⁻¹ + 1) / 2) * β ^ 2) := by
  have hdpos : 0 < (gaussianSquareDenominator w).re := hc.trans_le hw
  have hdne := gaussianSquareDenominator_ne_zero hdpos
  have hdnorm : c ≤ ‖gaussianSquareDenominator w‖ := by
    calc
      c ≤ (gaussianSquareDenominator w).re := hw
      _ ≤ ‖gaussianSquareDenominator w‖ := Complex.re_le_norm _
  have hpow :
      ‖gaussianSquareDenominator w‖ ^ (-(1 / 2 : ℝ)) ≤
        c ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hc hdnorm (by norm_num)
  have hinv : ‖(gaussianSquareDenominator w)⁻¹‖ ≤ c⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (hc.trans_le hdnorm) hc).2 hdnorm
  have hrat :
      ‖(gaussianSquareDenominator w)⁻¹ / 2 - (1 : ℂ) / 2‖ ≤
        (c⁻¹ + 1) / 2 := by
    calc
      ‖(gaussianSquareDenominator w)⁻¹ / 2 - (1 : ℂ) / 2‖ ≤
          ‖(gaussianSquareDenominator w)⁻¹ / 2‖ + ‖(1 : ℂ) / 2‖ :=
        norm_sub_le _ _
      _ = ‖(gaussianSquareDenominator w)⁻¹‖ / 2 + 1 / 2 := by
        rw [norm_div, norm_div]
        norm_num
      _ ≤ (c⁻¹ + 1) / 2 := by linarith
  have hexponent :
      (I * w / gaussianSquareDenominator w * (β : ℂ) ^ 2).re ≤
        ((c⁻¹ + 1) / 2) * β ^ 2 := by
    rw [I_mul_div_gaussianSquareDenominator w hdne]
    have hbpow : (β : ℂ) ^ 2 = ((β ^ 2 : ℝ) : ℂ) := by norm_cast
    rw [hbpow, mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_right
      (le_trans (Complex.re_le_norm _) hrat) (sq_nonneg β)
  unfold gaussianSquareTransform
  rw [norm_mul]
  rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num]
  rw [Complex.norm_cpow_real, Complex.norm_exp]
  exact mul_le_mul hpow (Real.exp_le_exp.mpr hexponent)
    (Real.exp_pos _).le (Real.rpow_nonneg hc.le _)

end PSSSNative.BlockBand.PSSS
