module

public import BlockBand.Critical.WeightedDensity.Global
public import BlockBand.Critical.Collar.Kernel.BoundaryIdentity

/-!
# Middle-only shifted collar mean: quadratic-form toolbox

* `quadForm_sandwich`: `q*(MYM*)q = (M*q)*Y(M*q)`; `quadForm_add_smul`, `two_mul_norm_le_quadForm_add`,
  `abs_quadForm_add_smul_sub_le`: `|(u+cw)*Y(u+cw) - u*Yu| ≤ ‖c‖(u*Yu + w*Yw) + ‖c‖²w*Yw` (`Y ⪰ 0`).
* `abs_quadForm_le_opNorm`: `|q*Mq| ≤ ‖M‖‖q‖²`; `quadForm_one`.
* `sum_norm_sq_inv_conjTranspose_mulVec_le`: `‖Z⁻*q‖ ≤ η⁻¹‖q‖` when `Z - Z* = 2i(η + Y)`, `Y ⪰ 0`.
* `quadForm_inv_mul_mul_le`: `q*Z⁻¹YZ⁻*q ≤ ‖q‖²/(4η)` (scattering defect).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `q*(MYM*)q = (M*q)*Y(M*q)`. -/
theorem quadForm_sandwich (M Y : Matrix ι ι ℂ) (q : ι → ℂ) :
    quadForm (M * Y * Mᴴ) q = quadForm Y (Mᴴ *ᵥ q) := by
  unfold quadForm
  congr 1
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

omit [DecidableEq ι] in
/-- Expansion of a Hermitian form along `u + c w`. -/
theorem quadForm_add_smul {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) (u w : ι → ℂ) (c : ℂ) :
    quadForm Y (u + c • w) = quadForm Y u + 2 * (c * (star u ⬝ᵥ (Y *ᵥ w))).re +
      ‖c‖ ^ 2 * quadForm Y w := by
  have hc : star w ⬝ᵥ (Y *ᵥ u) = star (star u ⬝ᵥ (Y *ᵥ w)) :=
    (hY.star_dotProduct_mulVec_comm u w).symm
  set m := star u ⬝ᵥ (Y *ᵥ w)
  have e : star (u + c • w) ⬝ᵥ (Y *ᵥ (u + c • w)) = star u ⬝ᵥ (Y *ᵥ u) + c * m +
      star (c * m) + (star c * c) * (star w ⬝ᵥ (Y *ᵥ w)) := by
    simp only [mulVec_add, mulVec_smul, star_add, star_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hc, star_mul']
    ring
  have hcc : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  unfold quadForm
  rw [e, hcc]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.star_def, Complex.conj_re]
  ring

omit [DecidableEq ι] in
/-- `2|u*Yw| ≤ u*Yu + w*Yw` for `Y ⪰ 0`. -/
theorem two_mul_norm_le_quadForm_add {Y : Matrix ι ι ℂ} (hY : Y.PosSemidef) (u w : ι → ℂ) :
    2 * ‖star u ⬝ᵥ (Y *ᵥ w)‖ ≤ quadForm Y u + quadForm Y w := by
  set m := star u ⬝ᵥ (Y *ᵥ w)
  rcases eq_or_ne m 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]
    exact add_nonneg (WeightedDensity.quadForm_nonneg_of_posSemidef hY u)
      (WeightedDensity.quadForm_nonneg_of_posSemidef hY w)
  have hm : 0 < ‖m‖ := norm_pos_iff.2 h0
  set μ : ℂ := -(star m / (‖m‖ : ℂ))
  have hμm : μ * m = -(‖m‖ : ℂ) := by
    have hmm : star m * m = ((‖m‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
    have hne : (‖m‖ : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [μ, neg_mul, div_mul_eq_mul_div, hmm]
    field_simp
    push_cast; ring
  have hμ : ‖μ‖ = 1 := by
    simp only [μ, norm_neg, norm_div, Complex.norm_real, norm_norm, norm_star]
    exact div_self hm.ne'
  have h := WeightedDensity.quadForm_nonneg_of_posSemidef hY (u + μ • w)
  rw [quadForm_add_smul hY.isHermitian, hμm, hμ] at h
  simp only [Complex.neg_re, Complex.ofReal_re, one_pow, one_mul] at h
  linarith

omit [DecidableEq ι] in
/-- **Perturbation of a positive form.** For `Y ⪰ 0`:
`|(u+cw)*Y(u+cw) - u*Yu| ≤ ‖c‖(u*Yu + w*Yw) + ‖c‖²w*Yw`. -/
theorem abs_quadForm_add_smul_sub_le {Y : Matrix ι ι ℂ} (hY : Y.PosSemidef) (u w : ι → ℂ)
    (c : ℂ) :
    |quadForm Y (u + c • w) - quadForm Y u| ≤
      ‖c‖ * (quadForm Y u + quadForm Y w) + ‖c‖ ^ 2 * quadForm Y w := by
  rw [quadForm_add_smul hY.isHermitian]
  have hw := WeightedDensity.quadForm_nonneg_of_posSemidef hY w
  have hcm : |2 * (c * (star u ⬝ᵥ (Y *ᵥ w))).re| ≤ ‖c‖ * (quadForm Y u + quadForm Y w) := by
    rw [abs_mul, abs_two]
    have h1 := Complex.abs_re_le_norm (c * (star u ⬝ᵥ (Y *ᵥ w)))
    rw [norm_mul] at h1
    have h2 := two_mul_norm_le_quadForm_add hY u w
    nlinarith [norm_nonneg c]
  have : quadForm Y u + 2 * (c * (star u ⬝ᵥ (Y *ᵥ w))).re + ‖c‖ ^ 2 * quadForm Y w -
      quadForm Y u = 2 * (c * (star u ⬝ᵥ (Y *ᵥ w))).re + ‖c‖ ^ 2 * quadForm Y w := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ ‖c‖ ^ 2 * quadForm Y w)]
  linarith

/-- `|q*Mq| ≤ ‖M‖‖q‖²` (Euclidean operator norm). -/
theorem abs_quadForm_le_opNorm (M : Matrix ι ι ℂ) (q : ι → ℂ) :
    |quadForm M q| ≤ ‖M‖ * ∑ i, ‖q i‖ ^ 2 := by
  have hre : |quadForm M q| ≤ ∑ i, ‖q i‖ * ‖(M *ᵥ q) i‖ := by
    unfold quadForm
    refine (Complex.abs_re_le_norm _).trans ?_
    unfold dotProduct
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖q i‖) (fun i => ‖(M *ᵥ q) i‖)
  have hMq : ∑ i, ‖(M *ᵥ q) i‖ ^ 2 ≤ ‖M‖ ^ 2 * ∑ i, ‖q i‖ ^ 2 := by
    have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 q)
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
    have h0 : 0 ≤ ∑ i, ‖q i‖ ^ 2 := by positivity
    have h1 : 0 ≤ ∑ i, ‖(M *ᵥ q) i‖ ^ 2 := by positivity
    simp at h
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rw [Real.sq_sqrt h1, mul_pow, Real.sq_sqrt h0] at this
    exact this
  set A := ∑ i, ‖q i‖ ^ 2
  set B := ∑ i, ‖(M *ᵥ q) i‖ ^ 2
  have hA : 0 ≤ A := by positivity
  have hS : 0 ≤ ∑ i, ‖q i‖ * ‖(M *ᵥ q) i‖ := by positivity
  have hsq : (∑ i, ‖q i‖ * ‖(M *ᵥ q) i‖) ^ 2 ≤ (‖M‖ * A) ^ 2 := by
    calc _ ≤ A * B := hcs
      _ ≤ A * (‖M‖ ^ 2 * A) := by gcongr
      _ = (‖M‖ * A) ^ 2 := by ring
  exact hre.trans ((pow_le_pow_iff_left₀ hS (by positivity) two_ne_zero).1 hsq)

theorem quadForm_one (q : ι → ℂ) : quadForm (1 : Matrix ι ι ℂ) q = ∑ i, ‖q i‖ ^ 2 := by
  unfold quadForm
  rw [one_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

/-- **Passive resolvent bound.** If `Z - Z* = 2i(ηI + Y)` with `Y ⪰ 0`, `η > 0` and `Z` invertible,
then `‖(Z⁻¹)*q‖² ≤ η⁻²‖q‖²`. -/
theorem sum_norm_sq_inv_conjTranspose_mulVec_le {Z Y : Matrix ι ι ℂ} {η : ℝ} (hη : 0 < η)
    (hY : Y.PosSemidef) (hZ : IsUnit Z.det)
    (hZZ : Z - Zᴴ = (2 * Complex.I) • ((η : ℂ) • (1 : Matrix ι ι ℂ) + Y)) (q : ι → ℂ) :
    ∑ i, ‖((Z⁻¹)ᴴ *ᵥ q) i‖ ^ 2 ≤ (η ^ 2)⁻¹ * ∑ i, ‖q i‖ ^ 2 := by
  have hZh : IsUnit Zᴴ.det := by rw [det_conjTranspose]; exact hZ.star
  have hv : Zᴴ *ᵥ ((Z⁻¹)ᴴ *ᵥ q) = q := by
    rw [mulVec_mulVec, conjTranspose_nonsing_inv, mul_nonsing_inv _ hZh, one_mulVec]
  generalize (Z⁻¹)ᴴ *ᵥ q = v at hv ⊢
  have hconj : star v ⬝ᵥ (Zᴴ *ᵥ v) = star (star v ⬝ᵥ (Z *ᵥ v)) := by
    rw [dotProduct_mulVec, ← star_mulVec, star_dotProduct]
  have hdiff : star v ⬝ᵥ (Z *ᵥ v) - star (star v ⬝ᵥ (Z *ᵥ v)) =
      (2 * Complex.I) * (((η : ℂ) * (star v ⬝ᵥ v)) + star v ⬝ᵥ (Y *ᵥ v)) := by
    rw [← hconj, ← dotProduct_sub, ← sub_mulVec, hZZ, smul_mulVec, add_mulVec, smul_mulVec,
      one_mulVec, dotProduct_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  generalize star v ⬝ᵥ (Z *ᵥ v) = a at hconj hdiff
  have hvv : (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
    have := quadForm_one v
    unfold quadForm at this
    rwa [one_mulVec] at this
  have hvvim : (star v ⬝ᵥ v).im = 0 := by
    simp only [dotProduct, Pi.star_apply, Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  have hYv : 0 ≤ quadForm Y v := WeightedDensity.quadForm_nonneg_of_posSemidef hY v
  have him : a.im = η * ∑ i, ‖v i‖ ^ 2 + quadForm Y v := by
    have h := congrArg Complex.im hdiff
    rw [Complex.star_def, Complex.sub_conj] at h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.add_re, Complex.mul_re, hvvim] at h
    unfold quadForm
    rw [← hvv]
    linarith
  have hnv : 0 ≤ ∑ i, ‖v i‖ ^ 2 := by positivity
  have hnq : 0 ≤ ∑ i, ‖q i‖ ^ 2 := by positivity
  have hcs : ‖a‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) * ∑ i, ‖q i‖ ^ 2 := by
    have h1 : ‖a‖ ≤ ∑ i, ‖v i‖ * ‖q i‖ := by
      have : ‖a‖ = ‖star v ⬝ᵥ q‖ := by rw [← hv, hconj, norm_star]
      rw [this]
      unfold dotProduct
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖v i‖) (fun i => ‖q i‖)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hlow : η * ∑ i, ‖v i‖ ^ 2 ≤ ‖a‖ := by
    have := Complex.abs_im_le_norm a
    rw [him] at this
    linarith [le_abs_self (η * ∑ i, ‖v i‖ ^ 2 + quadForm Y v)]
  have hsq : (η * ∑ i, ‖v i‖ ^ 2) ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) * ∑ i, ‖q i‖ ^ 2 :=
    (pow_le_pow_left₀ (by positivity) hlow 2).trans hcs
  rcases hnv.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith

/-- **Scattering defect bound.** Under the same hypotheses, `q*Z⁻¹YZ⁻*q ≤ ‖q‖²/(4η)`. -/
theorem quadForm_inv_mul_mul_le {Z Y : Matrix ι ι ℂ} {η : ℝ} (hη : 0 < η) (hZ : IsUnit Z.det)
    (hZZ : Z - Zᴴ = (2 * Complex.I) • ((η : ℂ) • (1 : Matrix ι ι ℂ) + Y)) (q : ι → ℂ) :
    quadForm (Z⁻¹ * Y * (Z⁻¹)ᴴ) q ≤ (4 * η)⁻¹ * ∑ i, ‖q i‖ ^ 2 := by
  have h := Collar.Kernel.one_sub_scattering_mul_conjTranspose hZ hZZ
  set r := 1 - Collar.Kernel.twoIEta η • Z⁻¹
  have hpsd : 0 ≤ quadForm (r * rᴴ) q := by
    have := quadForm_sandwich r 1 q
    rw [Matrix.mul_one] at this
    rw [this, quadForm_one]; positivity
  rw [h] at hpsd
  have hlin : quadForm (1 - ((4 * η : ℝ) : ℂ) • (Z⁻¹ * Y * (Z⁻¹)ᴴ)) q =
      ∑ i, ‖q i‖ ^ 2 - 4 * η * quadForm (Z⁻¹ * Y * (Z⁻¹)ᴴ) q := by
    rw [← quadForm_one]
    unfold quadForm
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.sub_re,
      Complex.re_ofReal_mul]
  rw [hlin] at hpsd
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

end BlockBand.Critical.MatrixClosing
