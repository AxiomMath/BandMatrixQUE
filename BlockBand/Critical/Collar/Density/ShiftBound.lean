module

public import BlockBand.Critical.Collar.Density.SchurAlgebra

/-!
# Bounded complex shifts of a weighted density bound

Deterministic; no measure. Finite index types, Hermitian `F`, any matrix `S`, complex `w`.

* `sum_norm_sq_sub_I_mulVec`: `‖(F - i)u‖² = ‖Fu‖² + ‖u‖²`.
* `quadForm_shift_le`: if `(F + i) S (F - i) ⪯ C I` then for every complex `w`
  `(F - w) S (F - w)* ⪯ 2 max(1,|w|²) C I` (quadratic-form version). This replaces the shift
  `F - c Re a` by the factorization `F - w = [(F - w)(F + i)⁻¹](F + i)`,
  `‖(F - w)(F + i)⁻¹‖² ≤ 2max(1,|w|²)`.
* `quadForm_sandwich_le`: with `H = (F - w)⁻¹` and `L = K T H`,
  `q*KTSTᴴKᴴq ≤ 2max(1,|w|²)C‖L*q‖²` (a sandwich bound of the form `K_XTΣ_F(0)T*K_X* ⪯ C' LL*`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open scoped ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sum_norm_sq_eq_re (u : ι → ℂ) : ∑ a, ‖u a‖ ^ 2 = (star u ⬝ᵥ u).re :=
  (BlockBand.Wegner.re_star_dotProduct_self u).symm

/-- `‖(F - i)u‖² = ‖Fu‖² + ‖u‖²` for Hermitian `F`. -/
theorem sum_norm_sq_sub_I_mulVec {F : Matrix ι ι ℂ} (hF : F.IsHermitian) (u : ι → ℂ) :
    ∑ a, ‖((F - Complex.I • (1 : Matrix ι ι ℂ)) *ᵥ u) a‖ ^ 2 =
      ∑ a, ‖(F *ᵥ u) a‖ ^ 2 + ∑ a, ‖u a‖ ^ 2 := by
  simp only [sum_norm_sq_eq_re]
  have hc : star (F *ᵥ u) ⬝ᵥ u = star u ⬝ᵥ (F *ᵥ u) := by
    rw [star_mulVec, ← dotProduct_mulVec, hF.eq]
  have hr : (star u ⬝ᵥ (F *ᵥ u)).im = 0 := BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian hF u
  rw [sub_mulVec, smul_mulVec, one_mulVec, star_sub, star_smul, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_dotProduct, dotProduct_smul, hc]
  simp only [smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_I,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, hr]
  have h1 : (star u ⬝ᵥ u).im = 0 := by
    have := BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian (isHermitian_one (n := ι)
      (α := ℂ)) u
    rwa [one_mulVec] at this
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, h1]
  ring

theorem norm_sub_sq_le (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y), sq_nonneg (‖x‖ - ‖y‖)]

/-- `‖(F - w)u‖² ≤ 2‖Fu‖² + 2|w|²‖u‖²`. -/
theorem sum_norm_sq_sub_smul_mulVec_le (F : Matrix ι ι ℂ) (w : ℂ) (u : ι → ℂ) :
    ∑ a, ‖((F - w • (1 : Matrix ι ι ℂ)) *ᵥ u) a‖ ^ 2 ≤
      2 * ∑ a, ‖(F *ᵥ u) a‖ ^ 2 + 2 * ‖w‖ ^ 2 * ∑ a, ‖u a‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have := norm_sub_sq_le ((F *ᵥ u) a) (w * u a)
  rw [norm_mul, mul_pow] at this
  linarith

theorem inv_mul_comm_of_commute {A B : Matrix ι ι ℂ} (hA : IsUnit A.det) (h : A * B = B * A) :
    A⁻¹ * B = B * A⁻¹ := by
  calc A⁻¹ * B = A⁻¹ * B * (A * A⁻¹) := by rw [mul_nonsing_inv A hA, Matrix.mul_one]
    _ = A⁻¹ * (A * B) * A⁻¹ := by rw [h]; simp only [Matrix.mul_assoc]
    _ = B * A⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul A hA, Matrix.one_mul]

/-- `‖(F - i)⁻¹(F - w̄)v‖² ≤ 2max(1,|w|²)‖v‖²` for Hermitian `F`. -/
theorem sum_norm_sq_resolvent_shift_le {F : Matrix ι ι ℂ} (hF : F.IsHermitian) (w : ℂ)
    (v : ι → ℂ) :
    ∑ a, ‖(((F - Complex.I • (1 : Matrix ι ι ℂ))⁻¹ * (F - star w • 1)) *ᵥ v) a‖ ^ 2 ≤
      2 * max 1 (‖w‖ ^ 2) * ∑ a, ‖v a‖ ^ 2 := by
  set P := F - Complex.I • (1 : Matrix ι ι ℂ) with hP
  have hPu : IsUnit P.det := isUnit_det_sub_smul_one' hF (z := Complex.I) (by simp)
  have hcomm : P * (F - star w • 1) = (F - star w • 1) * P := by
    simp only [hP, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul, mul_comm]
    abel
  set u := P⁻¹ *ᵥ v with hu
  have hv : v = P *ᵥ u := by rw [hu, mulVec_mulVec, mul_nonsing_inv P hPu, one_mulVec]
  rw [inv_mul_comm_of_commute hPu hcomm, ← mulVec_mulVec, ← hu]
  have h1 := sum_norm_sq_sub_smul_mulVec_le F (star w) u
  have h2 := sum_norm_sq_sub_I_mulVec hF u
  rw [← hP, ← hv] at h2
  rw [norm_star] at h1
  have hFu : 0 ≤ ∑ a, ‖(F *ᵥ u) a‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hu0 : 0 ≤ ∑ a, ‖u a‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm1 : 1 ≤ max 1 (‖w‖ ^ 2) := le_max_left _ _
  have hm2 : ‖w‖ ^ 2 ≤ max 1 (‖w‖ ^ 2) := le_max_right _ _
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_right hm1 hFu, mul_le_mul_of_nonneg_right hm2 hu0]

/-- **Bounded complex shift.** If `(F + i) S (F - i) ⪯ C I` (the `η = 1`, `e = 0` form of
the global weighted-density bound), then `q*(F - w)S(F - w)*q ≤ 2max(1,|w|²) C ‖q‖²`. -/
theorem quadForm_shift_le {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {S : Matrix ι ι ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hS : (((C : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) -
      (F - ((0 : ℂ) - (1 : ℂ) * Complex.I) • 1) * S *
        (F - ((0 : ℂ) + (1 : ℂ) * Complex.I) • 1)).PosSemidef)
    (w : ℂ) (v : ι → ℂ) :
    quadForm ((F - w • 1) * S * (F - w • 1)ᴴ) v ≤
      2 * max 1 (‖w‖ ^ 2) * C * ∑ a, ‖v a‖ ^ 2 := by
  set P := F - Complex.I • (1 : Matrix ι ι ℂ) with hP
  have hPu : IsUnit P.det := isUnit_det_sub_smul_one' hF (z := Complex.I) (by simp)
  have hPH : Pᴴ = F - ((0 : ℂ) - (1 : ℂ) * Complex.I) • 1 := by
    rw [hP, conjTranspose_sub, hF.eq, conjTranspose_smul, conjTranspose_one]
    congr 2; simp
  have hP' : F - ((0 : ℂ) + (1 : ℂ) * Complex.I) • 1 = P := by rw [hP]; congr 2; simp
  rw [← hPH, hP'] at hS
  -- `(F - w) S (F - w)* = Nᴴ* (Pᴴ S P) Nᴴ` with `Nᴴ = P⁻¹ (F - w)ᴴ`.
  set N := P⁻¹ * (F - w • 1)ᴴ with hN
  have hPinvH : (Pᴴ)⁻¹ * Pᴴ = 1 := by
    rw [← conjTranspose_nonsing_inv, ← conjTranspose_mul, mul_nonsing_inv P hPu,
      conjTranspose_one]
  have heq : (F - w • 1) * S * (F - w • 1)ᴴ = Nᴴ * (Pᴴ * S * P) * N := by
    have h1 : Nᴴ * Pᴴ = F - w • 1 := by
      rw [hN, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
        conjTranspose_nonsing_inv, hPinvH, Matrix.mul_one]
    have h2 : P * N = (F - w • 1)ᴴ := by
      rw [hN, ← Matrix.mul_assoc, mul_nonsing_inv P hPu, Matrix.one_mul]
    calc (F - w • 1) * S * (F - w • 1)ᴴ = (Nᴴ * Pᴴ) * S * (P * N) := by rw [h1, h2]
      _ = Nᴴ * (Pᴴ * S * P) * N := by simp only [Matrix.mul_assoc]
  rw [heq, quadForm_conjTranspose_mul_mul]
  have hq := quadForm_nonneg_of_posSemidef hS (N *ᵥ v)
  rw [quadForm_sub, quadForm_real_smul, quadForm_one] at hq
  have hNv : ∑ a, ‖(N *ᵥ v) a‖ ^ 2 ≤ 2 * max 1 (‖w‖ ^ 2) * ∑ a, ‖v a‖ ^ 2 := by
    have : (F - w • (1 : Matrix ι ι ℂ))ᴴ = F - star w • 1 := by
      rw [conjTranspose_sub, hF.eq, conjTranspose_smul, conjTranspose_one]
    rw [hN, this]
    exact sum_norm_sq_resolvent_shift_le hF w v
  nlinarith [mul_le_mul_of_nonneg_left hNv hC]

/-- **Sandwich bound.** With `H = (F - w)⁻¹` and `L = K T H`: if
`(F + i)S(F - i) ⪯ C I` then `q*KTSTᴴKᴴq ≤ 2max(1,|w|²) C ‖L*q‖²`. -/
theorem quadForm_sandwich_le {n : Type} [Fintype n] [DecidableEq n] {F : Matrix ι ι ℂ}
    (hF : F.IsHermitian) {S : Matrix ι ι ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hS : (((C : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) -
      (F - ((0 : ℂ) - (1 : ℂ) * Complex.I) • 1) * S *
        (F - ((0 : ℂ) + (1 : ℂ) * Complex.I) • 1)).PosSemidef)
    {w : ℂ} (hw : IsUnit (F - w • (1 : Matrix ι ι ℂ)).det) (K : Matrix n n ℂ) (T : Matrix n ι ℂ)
    (q : n → ℂ) :
    quadForm (K * T * S * Tᴴ * Kᴴ) q ≤
      2 * max 1 (‖w‖ ^ 2) * C * ∑ a, ‖((K * T * (F - w • 1)⁻¹)ᴴ *ᵥ q) a‖ ^ 2 := by
  set H := (F - w • (1 : Matrix ι ι ℂ))⁻¹ with hH
  have h1 : H * (F - w • 1) = 1 := nonsing_inv_mul _ hw
  have h2 : (F - w • (1 : Matrix ι ι ℂ))ᴴ * Hᴴ = 1 := by
    rw [← conjTranspose_mul, h1, conjTranspose_one]
  have heq : K * T * S * Tᴴ * Kᴴ =
      ((K * T * H)ᴴ)ᴴ * ((F - w • 1) * S * (F - w • 1)ᴴ) * (K * T * H)ᴴ := by
    rw [conjTranspose_conjTranspose]
    simp only [conjTranspose_mul]
    calc K * T * S * Tᴴ * Kᴴ = K * T * (H * (F - w • 1)) * S *
          ((F - w • 1)ᴴ * Hᴴ) * Tᴴ * Kᴴ := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [heq, quadForm_conjTranspose_mul_mul]
  exact quadForm_shift_le hF hC hS w _

end BlockBand.Critical.Collar.Density
