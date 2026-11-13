module

public import BlockBand.Palm.MomentFlow.EventGamma

/-!
# The isotropic control at `x = y = q` along `freshM`

* `quad_imaginaryPart`, `normalizedTrace_imaginaryPart`: `q* (Im M) q = Im q*Mq`, `⟨Im M⟩ = Im⟨M⟩`.
* `gamma_quad_re`: `Re q* Γ_M q = Im(q*Mq)/Im⟨M⟩` for `Γ_M = Im M/⟨Im M⟩`.
* `isotropicControl_freshM_le`: on the regularity window with `η > 0`,
  `isotropicControl (freshM F σ z) z q q ≤ Im(q*M q)/√(π v₀ N η)`.
* `overlap_combined_le`: on the good event of the external isotropic local law at `z = x + iη`
  (loss `N^δ`) and `|λ_i - x| ≤ η`, `X_i ≤ 2Nη · (1 + N^δ/√(π v₀ N η)) · K · q*Γq` with
  `K = gammaCompConst` (through `Im q*Gq` and `Γ(z) ≍ Γ`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.Palm BlockBand.Palm.CoarseRelative
open scoped ComplexConjugate

variable {N : ℕ}

theorem star_quad_conjTranspose (M : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) :
    star q ⬝ᵥ (Mᴴ *ᵥ q) = conj (star q ⬝ᵥ (M *ᵥ q)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply, map_sum,
    map_mul, RCLike.star_def, Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quad_imaginaryPart (M : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) :
    star q ⬝ᵥ (CEH.imaginaryPart M *ᵥ q) = (((star q ⬝ᵥ (M *ᵥ q)).im : ℝ) : ℂ) := by
  unfold CEH.imaginaryPart
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub,
    star_quad_conjTranspose, Complex.sub_conj, smul_eq_mul]
  have h : (2 * Complex.I) ≠ 0 := by simp
  field_simp
  push_cast; ring

theorem normalizedTrace_imaginaryPart (M : Matrix (Fin N) (Fin N) ℂ) :
    CEH.normalizedTrace (CEH.imaginaryPart M) = (((CEH.normalizedTrace M).im : ℝ) : ℂ) := by
  unfold CEH.imaginaryPart CEH.normalizedTrace
  rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, smul_eq_mul]
  have h : (2 * Complex.I) ≠ 0 := by simp
  have hs : M.trace - star M.trace = 2 * (M.trace.im : ℂ) * Complex.I := by
    rw [RCLike.star_def, Complex.sub_conj]; push_cast; ring
  rw [hs]
  apply Complex.ext
  · simp
  · simp only [Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.natCast_re,
      Complex.natCast_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im]
    by_cases hN : (N : ℝ) = 0
    · simp [hN]
    · field_simp; ring

theorem gamma_quad_re (M : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) :
    (CEH.sourceMatrixElement (CEH.gammaMatrix M) q q).re =
      (star q ⬝ᵥ (M *ᵥ q)).im / (CEH.normalizedTrace M).im := by
  unfold CEH.sourceMatrixElement CEH.gammaMatrix
  rw [Matrix.smul_mulVec, dotProduct_smul, quad_imaginaryPart, normalizedTrace_imaginaryPart,
    smul_eq_mul, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- The CEH isotropic control along `freshM` on the regularity window. -/
theorem isotropicControl_freshM_le {F : Matrix (Fin N) (Fin N) ℂ} {A c₀ E r₀ s₀ v₀ σ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    (hσ : σ ∈ Icc (c₀ - s₀) c₀) {z : ℂ} (hx : |z.re - E| ≤ r₀) (hη : 0 < z.im)
    (hη1 : z.im ≤ 1) (hN : 0 < N) (q : Fin N → ℂ) :
    CEH.isotropicControl (freshM F σ z) z q q ≤
      (star q ⬝ᵥ (freshM F σ z *ᵥ q)).im / Real.sqrt (Real.pi * v₀ * N * z.im) := by
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  have hσ0 : 0 < σ := by linarith [hσ.1, hK.2.2.2.2.1, hK.1]
  obtain ⟨hm1, -⟩ := fresh_regular_bounds hC.2.2 hσ hx hη.le hη1
  have hm : 0 < (freshDyson F σ z).im := lt_of_lt_of_le hv0 hm1
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : (freshW F σ z).im ≠ 0 := by rw [freshW_im]; positivity
  have hai : 0 ≤ (star q ⬝ᵥ (freshM F σ z *ᵥ q)).im := by
    rw [freshM_quad_im hC.1 hw q]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  rw [isotropicControl_self, gamma_quad_re, freshM_normalizedTrace hm, CEH.sourceDensity,
    freshM_normalizedTrace hm, abs_of_pos hm, abs_of_pos hη,
    abs_of_nonneg (div_nonneg hai hm.le)]
  set a := (star q ⬝ᵥ (freshM F σ z *ᵥ q)).im
  set m := (freshDyson F σ z).im
  have hsq : Real.sqrt (m / Real.pi / (N * z.im)) * (a / m) =
      a / Real.sqrt (Real.pi * m * N * z.im) := by
    have hpos : 0 < Real.pi * m * N * z.im := by positivity
    rw [show m / Real.pi / (N * z.im) = m ^ 2 / (Real.pi * m * N * z.im) by field_simp,
      Real.sqrt_div (sq_nonneg m), Real.sqrt_sq hm.le]
    field_simp
  rw [hsq]
  refine div_le_div_of_nonneg_left hai (by positivity) (Real.sqrt_le_sqrt ?_)
  have : Real.pi * v₀ ≤ Real.pi * m := mul_le_mul_of_nonneg_left hm1 Real.pi_pos.le
  have h2 : 0 ≤ (N : ℝ) * z.im := by positivity
  nlinarith [this, h2]

/-- **Combined deterministic `X_i` bound** (through `Im q*Gq` and `Γ(z) ≍ Γ`). -/
theorem overlap_combined_le {F : Matrix (Fin N) (Fin N) ℂ} {A c₀ E r₀ s₀ v₀ σ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    (hσ : σ ∈ Icc (c₀ - s₀) c₀) {x η : ℝ} (hx : |x - E| ≤ r₀) (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : 0 < N) (q : Fin N → ℂ) {δ : ℝ} {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H)
    (hgood : ‖star q ⬝ᵥ (((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
      freshM F σ ⟨x, η⟩) *ᵥ q)‖ ≤ (N : ℝ) ^ δ * CEH.isotropicControl (freshM F σ ⟨x, η⟩) ⟨x, η⟩ q q)
    (i : Fin N) (hix : |freshEigenvalue H i - x| ≤ η) :
    (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector H i‖ ^ 2 ≤
      2 * N * η * (1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η)) *
        (gammaCompConst c₀ r₀ s₀ v₀ * quadForm (freshGamma F c₀ E) q) := by
  have hz : (⟨x, η⟩ : ℂ).im = η := rfl
  have hzr : |(⟨x, η⟩ : ℂ).re - E| ≤ r₀ := hx
  have h1 := overlap_le_of_near hH hs hN hη q i hix
  have h2 := im_quad_le ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)
    (freshM F σ ⟨x, η⟩) q
  have hctrl := isotropicControl_freshM_le hK hC hσ hzr hη hη1 hN q
  have hgam := quad_im_le_gamma hN hK hC hσ hzr hη.le hη1 q
  set a := (star q ⬝ᵥ (freshM F σ ⟨x, η⟩ *ᵥ q)).im
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hNδ : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg hNp.le _
  have hsq : 0 < Real.sqrt (Real.pi * v₀ * N * η) := by
    have := hK.2.2.2.2.2; positivity
  have hai : 0 ≤ a := by
    have hv0 := hK.2.2.2.2.2
    obtain ⟨hm1, -⟩ := fresh_regular_bounds hC.2.2 hσ hzr hη.le hη1
    have hw : (freshW F σ ⟨x, η⟩).im ≠ 0 := by
      rw [freshW_im]; have : 0 < σ := by linarith [hσ.1, hK.2.2.2.2.1, hK.1]
      have : 0 < (freshDyson F σ ⟨x, η⟩).im := lt_of_lt_of_le hv0 hm1
      positivity
    simp only [a]
    rw [freshM_quad_im hC.1 hw q]
    exact mul_nonneg (by have : 0 < σ := by linarith [hσ.1, hK.2.2.2.2.1, hK.1]
                         have : 0 ≤ (freshDyson F σ ⟨x, η⟩).im := le_trans hv0.le hm1
                         positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)
  have hG : (star q ⬝ᵥ ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im ≤
      a * (1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η)) := by
    have : (N : ℝ) ^ δ * CEH.isotropicControl (freshM F σ ⟨x, η⟩) ⟨x, η⟩ q q ≤
        (N : ℝ) ^ δ * (a / Real.sqrt (Real.pi * v₀ * N * η)) :=
      mul_le_mul_of_nonneg_left hctrl hNδ
    have e : a * (1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η)) =
        a + (N : ℝ) ^ δ * (a / Real.sqrt (Real.pi * v₀ * N * η)) := by ring
    rw [e]; linarith
  have hfac : 0 ≤ 1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η) := by positivity
  calc (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector H i‖ ^ 2
      ≤ 2 * N * η * (star q ⬝ᵥ ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im :=
        h1
    _ ≤ 2 * N * η * (a * (1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η))) :=
        mul_le_mul_of_nonneg_left hG (by positivity)
    _ ≤ 2 * N * η * ((gammaCompConst c₀ r₀ s₀ v₀ * quadForm (freshGamma F c₀ E) q) *
          (1 + (N : ℝ) ^ δ / Real.sqrt (Real.pi * v₀ * N * η))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgam hfac) (by positivity)
    _ = _ := by ring

end BlockBand.Palm.MomentFlow
