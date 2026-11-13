module

public import BlockBand.Palm.MomentFlow.BridgeRelabel
public import BlockBand.Palm.CoarseRelativeDyson

/-!
# The Palm covariance `Γ` and the spectral resolvent identity

* `freshGamma_quad_eq`: for Hermitian `F`, `q*Γq = c₀ ‖M_{c₀}(E) q‖²` (normality of `F - w`);
* `freshGamma_quad_lower`: on `FreshClass F A c₀ E r₀ s₀ v₀` (`N ≥ 1`),
  `q*Γq ≥ v₀ · lowConst c₀ s₀ v₀ · N^{-2max(A,1)} ‖q‖²` (from the directional lower bound
  `freshM_quad_im_lower` at `z = E`, and `Im(q*Mq) = c₀ Im m ‖Mq‖²`);
* `freshGamma_quad_pos`: `q*Γq > 0` for `q ≠ 0` (`Γ ≻ 0`).

* `resolvent_quad_spectral`: `q*(H - z)⁻¹q = ∑_j |q* u_j|² /(λ_j - z)` for `Im z ≠ 0`;
* `resolvent_im_spectral`: `(1/N) ∑_j η/((λ_j - λ)² + η²) X_j = Im q*(H - λ - iη)⁻¹ q` (`η ≠ 0`,
  `N ≥ 1`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Foundations.Spectral BlockBand.Model.Construction BlockBand.Palm
open BlockBand.Palm.CoarseRelative
open scoped ComplexConjugate

variable {N : ℕ}

/-!
## The Palm covariance
-/

theorem star_dotProduct_self_re (v : Fin N → ℂ) : (star v ⬝ᵥ v).re = nsq v := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, nsq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- `F - w` is normal for Hermitian `F`. -/
theorem shift_normal {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (w : ℂ) :
    (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ * (F - w • (1 : Matrix (Fin N) (Fin N) ℂ)) =
      (F - w • (1 : Matrix (Fin N) (Fin N) ℂ)) * (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ := by
  rw [Matrix.conjTranspose_sub, hF.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]
  module

/-- `q*Γq = c₀ ‖M_{c₀}(E) q‖²` for Hermitian `F`. -/
theorem freshGamma_quad_eq {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (c₀ E : ℝ)
    (q : Fin N → ℂ) :
    quadForm (freshGamma F c₀ E) q = c₀ * nsq (freshM F c₀ E *ᵥ q) := by
  set X : Matrix (Fin N) (Fin N) ℂ := F - ((E : ℂ) + (c₀ : ℂ) * freshDyson F c₀ E) • 1
  have hM : freshM F c₀ E = X⁻¹ := rfl
  have hΓ : freshGamma F c₀ E = (c₀ : ℂ) • (Xᴴ * X)⁻¹ := rfl
  have hinv : (Xᴴ * X)⁻¹ = (X⁻¹)ᴴ * X⁻¹ := by
    rw [shift_normal hF, Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv]
  unfold quadForm
  rw [hΓ, hinv, hM, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, smul_eq_mul, Complex.re_ofReal_mul,
    star_dotProduct_self_re]

/-- `q*Γq ≥ v₀ · lowConst · N^{-2max(A,1)} ‖q‖²` on the fresh class. -/
theorem freshGamma_quad_lower {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    (q : Fin N → ℂ) :
    v₀ * lowConst c₀ s₀ v₀ * (N : ℝ) ^ (-(2 * max A 1)) * nsq q ≤
      quadForm (freshGamma F c₀ E) q := by
  have hc0 : 0 < c₀ := hK.1
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  have hs : c₀ ∈ Set.Icc (c₀ - s₀) c₀ := ⟨by linarith [hK.2.2.2.1], le_rfl⟩
  have hx : |((E : ℂ)).re - E| ≤ r₀ := by simp [hK.2.2.1.le]
  have hlow := freshM_quad_im_lower hN hK hC hs hx (by simp) (by simp) q
  obtain ⟨hm1, hm2⟩ := fresh_regular_bounds hC.2.2 hs hx (by simp) (by simp)
  have hw : (freshW F c₀ (E : ℂ)).im ≠ 0 := by
    rw [freshW_im]; simp only [Complex.ofReal_im, zero_add]
    exact (mul_pos hc0 (lt_of_lt_of_le hv0 hm1)).ne'
  have hid := freshM_quad_im hC.1 hw q
  simp only [Complex.ofReal_im, zero_add] at hid
  rw [freshGamma_quad_eq hC.1]
  have hn : 0 ≤ nsq (freshM F c₀ E *ᵥ q) := Finset.sum_nonneg fun _ _ => by positivity
  have hm0 : 0 < (freshDyson F c₀ E).im := lt_of_lt_of_le hv0 hm1
  have hvm : v₀ * (freshDyson F c₀ E).im ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hm2 hv0.le
    rwa [mul_inv_cancel₀ hv0.ne'] at this
  calc v₀ * lowConst c₀ s₀ v₀ * (N : ℝ) ^ (-(2 * max A 1)) * nsq q
      = v₀ * (lowConst c₀ s₀ v₀ * (N : ℝ) ^ (-(2 * max A 1)) * nsq q) := by ring
    _ ≤ v₀ * (c₀ * (freshDyson F c₀ E).im * nsq (freshM F c₀ E *ᵥ q)) := by
        rw [← hid]; exact mul_le_mul_of_nonneg_left hlow hv0.le
    _ = (v₀ * (freshDyson F c₀ E).im) * (c₀ * nsq (freshM F c₀ E *ᵥ q)) := by ring
    _ ≤ 1 * (c₀ * nsq (freshM F c₀ E *ᵥ q)) :=
        mul_le_mul_of_nonneg_right hvm (mul_nonneg hc0.le hn)
    _ = c₀ * nsq (freshM F c₀ E *ᵥ q) := one_mul _

/-- `Γ ≻ 0` on the fresh class. -/
theorem freshGamma_quad_pos {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    {q : Fin N → ℂ} (hq : q ≠ 0) : 0 < quadForm (freshGamma F c₀ E) q := by
  refine lt_of_lt_of_le ?_ (freshGamma_quad_lower hN hK hC q)
  have hc0 : 0 < c₀ := hK.1
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  have hl : 0 < lowConst c₀ s₀ v₀ := by
    unfold lowConst
    have : 0 < c₀ - s₀ := by linarith [hK.2.2.2.2.1]
    positivity
  have hq' : 0 < nsq q := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hq
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hk) 2) (Finset.single_le_sum
      (f := fun k => ‖q k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k))
  have hNp : (0 : ℝ) < (N : ℝ) ^ (-(2 * max A 1)) := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  positivity

/-!
## The spectral resolvent identity
-/

/-- `q*(H - z)⁻¹q = ∑_k |q* e_k|²/(λ_k - z)` over Mathlib's eigenbasis. -/
theorem resolvent_quad_eigenbasis {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (q : Fin N → ℂ) :
    star q ⬝ᵥ ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q) =
      ∑ k, ((‖star q ⬝ᵥ ⇑(hH.eigenvectorBasis k)‖ ^ 2 : ℝ) : ℂ) *
        (((hH.eigenvalues k : ℝ) : ℂ) - z)⁻¹ := by
  have hR := certificateMatrixResolvent_eq_spectral H hH hz
  unfold certificateMatrixResolvent profileSpectralAut at hR
  rw [hR, Unitary.conjStarAlgAut_apply]
  set U : Matrix (Fin N) (Fin N) ℂ := ↑(hH.eigenvectorUnitary)
  set c : Fin N → ℂ := star U *ᵥ q
  have hstar : star q ᵥ* U = star c := by
    simp only [c, Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  have hc : ∀ k, c k = conj (star q ⬝ᵥ ⇑(hH.eigenvectorBasis k)) := by
    intro k
    simp only [c, U, Matrix.mulVec, dotProduct, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, map_sum, map_mul, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hstar]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, certificateScalarResolvent]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc' : (star U *ᵥ q) k = conj (star q ⬝ᵥ ⇑(hH.eigenvectorBasis k)) := hc k
  rw [hc', hc k]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  set S : ℂ := ∑ x, (starRingEnd ℂ) (q x) * (hH.eigenvectorBasis k) x
  have hS : S * conj S = ((‖S‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  linear_combination ((((hH.eigenvalues k : ℝ) : ℂ) - z)⁻¹) * hS

/-- `q*(H - z)⁻¹q = ∑_j |q* u_j|²/(λ_j - z)` in the increasing labels and
selected eigenvectors, on simple spectrum. -/
theorem resolvent_quad_spectral {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) {z : ℂ} (hz : z.im ≠ 0) (q : Fin N → ℂ) :
    star q ⬝ᵥ ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q) =
      ∑ j, ((‖star q ⬝ᵥ freshEigenvector H j‖ ^ 2 : ℝ) : ℂ) *
        (((freshEigenvalue H j : ℝ) : ℂ) - z)⁻¹ := by
  rw [resolvent_quad_eigenbasis hH hz q]
  set e : Fin N ≃ Fin N := (finCongr (Fintype.card_fin N).symm).trans increasingIndex
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hev : hH.eigenvalues (e j) = freshEigenvalue H j := by
    simp only [e, Equiv.trans_apply, finCongr_apply, eigenvalue_increasingIndex,
      freshEigenvalue, rawIncreasingEigenvalue_eq _ H hH]
  have hvec : ‖star q ⬝ᵥ ⇑(hH.eigenvectorBasis (e j))‖ = ‖star q ⬝ᵥ freshEigenvector H j‖ := by
    obtain ⟨w, hw, he⟩ := orderedColumnSelection_eq_phase (Fin.cast (Fintype.card_fin N).symm j)
      ⟨H, hH⟩ (injective_orderedEigenvalue hH hs)
    have hfe : freshEigenvector H j =
        w • increasingEigenvector hH (Fin.cast (Fintype.card_fin N).symm j) := by
      funext x
      simp only [freshEigenvector]
      rw [rawOrderedColumnSelection_eq _ H hH, he]
    rw [hfe, dotProduct_smul, norm_smul, hw, one_mul]
    unfold increasingEigenvector
    rw [increasingEigenbasis_apply]
    rfl
  rw [hev, hvec]

/-- Imaginary part: `(1/N) ∑_j η/((λ_j - λ)² + η²) X_j = Im q*(H - λ - iη)⁻¹ q` with
`X_j = N|q* u_j|²`. -/
theorem resolvent_im_spectral {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) (hN : 0 < N) (lam : ℝ) {η : ℝ} (hη : η ≠ 0) (q : Fin N → ℂ) :
    (N : ℝ)⁻¹ * ∑ j, η / ((freshEigenvalue H j - lam) ^ 2 + η ^ 2) *
        ((N : ℝ) * ‖star q ⬝ᵥ freshEigenvector H j‖ ^ 2) =
      (star q ⬝ᵥ ((H - (⟨lam, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im := by
  rw [resolvent_quad_spectral hH hs (z := ⟨lam, η⟩) hη q, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set x := freshEigenvalue H j
  set p := ‖star q ⬝ᵥ freshEigenvector H j‖ ^ 2
  have hd : ((x : ℂ) - ⟨lam, η⟩) = ⟨x - lam, -η⟩ := by apply Complex.ext <;> simp
  rw [Complex.im_ofReal_mul, hd, Complex.inv_im]
  simp only [Complex.normSq_mk]
  field_simp

end BlockBand.Palm.MomentFlow
