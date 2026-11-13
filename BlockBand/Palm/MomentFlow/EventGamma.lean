module

public import BlockBand.Palm.MomentFlow.EventLocal

/-!
# `Γ(z) ≍ Γ` and the local-law domain on the bulk window (deterministic)

*Domain:* `N ≥ 1`, `FreshConstants c₀ r₀ s₀ v₀`, `FreshClass F A c₀ E r₀ s₀ v₀`,
`σ ∈ [c₀ - s₀, c₀]`, `z = x + iη` with `|x - E| ≤ r₀`, `0 ≤ η ≤ 1` (the window of the fresh
regularity bounds).

* `freshDyson_norm_le`: `|m_σ(z)| ≤ (Im w)⁻¹`, `w = z + σ m_σ(z)`.
* `resolvent_nsq_compare`: `‖(F - w)⁻¹q‖² ≤ 2(1 + |w - w₀|²/(Im w)²) ‖(F - w₀)⁻¹q‖²`.
* **`quad_im_le_gamma`**: `Im q*M_σ(z)q ≤ gammaCompConst c₀ r₀ s₀ v₀ · q*Γq`, the constant depending
  on the fixed regularity constants only (uniform in `N`, `F`, `E`, `A`, `σ`, `z`, `q`).
* `abs_E_le`: `|E| ≤ N^A + 2/v₀` (the energy is polynomially bounded by `‖F‖`), and `norm_z_le`.
* `sourceDensity_freshM_ge`: `ρ(M_σ(z)) = Im m_σ(z)/π ≥ v₀/π`;
  `inLocalLawDomain_of_bulk` (with `MDEBranchIdentification`): `z` is in the domain of the external
  local law for every branch as soon as `N^ε ≤ N η v₀/π` and `‖z‖ ≤ √σ N^{κ + 1/ε}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.Palm BlockBand.Palm.CoarseRelative
open scoped ComplexConjugate

variable {N : ℕ}

theorem freshDyson_norm_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} {z : ℂ} (hs : 0 < s) (hz : 0 ≤ z.im) (hm : 0 < (freshDyson F s z).im) :
    ‖freshDyson F s z‖ ≤ ((freshW F s z).im)⁻¹ := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hres := freshDyson_residual_eq_zero hF hs hz hm
  have heq := (certificateDysonResidual_eq_zero_iff hF.eigenvalues s z _).mp hres
  have hw : 0 < (freshW F s z).im := by rw [freshW_im]; exact add_pos_of_nonneg_of_pos hz (mul_pos hs hm)
  have hpt : ∀ i, ‖certificateScalarResolvent (hF.eigenvalues i) (freshW F s z)‖ ≤
      ((freshW F s z).im)⁻¹ := by
    intro i
    unfold certificateScalarResolvent
    rw [norm_inv]
    refine inv_anti₀ hw ?_
    have := Complex.abs_im_le_norm (((hF.eigenvalues i : ℝ) : ℂ) - freshW F s z)
    rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hw] at this
    exact this
  rw [heq]
  exact certificateAverage_norm_le_const _ _ hpt

theorem nsq_add_le_two (x y : Fin N → ℂ) : nsq (x + y) ≤ 2 * nsq x + 2 * nsq y := by
  have h := sqrt_nsq_add_le x y
  have hx : 0 ≤ nsq x := Finset.sum_nonneg fun _ _ => by positivity
  have hy : 0 ≤ nsq y := Finset.sum_nonneg fun _ _ => by positivity
  have hxy : 0 ≤ nsq (x + y) := Finset.sum_nonneg fun _ _ => by positivity
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt hxy, add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy] at h2
  nlinarith [Real.sqrt_nonneg (nsq x), Real.sqrt_nonneg (nsq y),
    sq_nonneg (Real.sqrt (nsq x) - Real.sqrt (nsq y)), Real.sq_sqrt hx, Real.sq_sqrt hy]

/-- Comparison of resolvents at two spectral parameters. -/
theorem resolvent_nsq_compare {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {w w₀ : ℂ}
    (hw : 0 < w.im) (hw0 : w₀.im ≠ 0) (q : Fin N → ℂ) :
    nsq ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q) ≤
      2 * (1 + ‖w - w₀‖ ^ 2 / w.im ^ 2) *
        nsq ((F - w₀ • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q) := by
  set R := (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  set R₀ := (F - w₀ • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  have hid := hermitian_resolvent_sub hF hw.ne' hw0
  have hRq : R *ᵥ q = R₀ *ᵥ q + (w - w₀) • (R *ᵥ (R₀ *ᵥ q)) := by
    have : R = R₀ + (w - w₀) • (R * R₀) := by rw [← hid]; abel
    calc R *ᵥ q = (R₀ + (w - w₀) • (R * R₀)) *ᵥ q := by rw [← this]
      _ = _ := by rw [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  have hop := hermitian_resolvent_nsq_le hF hw.ne' (R₀ *ᵥ q)
  have hy : 0 ≤ nsq (R₀ *ᵥ q) := Finset.sum_nonneg fun _ _ => by positivity
  rw [hRq]
  refine (nsq_add_le_two _ _).trans ?_
  rw [nsq_smul]
  have hw2 : 0 < w.im ^ 2 := by positivity
  have : ‖w - w₀‖ ^ 2 * nsq (R *ᵥ (R₀ *ᵥ q)) ≤ ‖w - w₀‖ ^ 2 / w.im ^ 2 * nsq (R₀ *ᵥ q) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hw2]
    have := mul_le_mul_of_nonneg_left hop (sq_nonneg ‖w - w₀‖)
    calc ‖w - w₀‖ ^ 2 * nsq (R *ᵥ (R₀ *ᵥ q)) * w.im ^ 2
        ≤ ‖w - w₀‖ ^ 2 * ((w.im ^ 2)⁻¹ * nsq (R₀ *ᵥ q)) * w.im ^ 2 :=
          mul_le_mul_of_nonneg_right this hw2.le
      _ = ‖w - w₀‖ ^ 2 * nsq (R₀ *ᵥ q) := by field_simp
  nlinarith [this]

/-- The constant of `Γ(z) ≍ Γ`: with `κ = (c₀ - s₀)v₀`, `B = r₀ + 1 + 2c₀/κ`,
`K = (1 + c₀/v₀) · 2(1 + B²/κ²)/c₀`. -/
def gammaCompConst (c₀ r₀ s₀ v₀ : ℝ) : ℝ :=
  let κ := (c₀ - s₀) * v₀
  let B := r₀ + 1 + 2 * c₀ / κ
  (1 + c₀ / v₀) * (2 * (1 + B ^ 2 / κ ^ 2)) / c₀

/-- **`Γ(z) ≍ Γ`**: `Im q*M_σ(z)q ≤ K q*Γq` on the regularity window. -/
theorem quad_im_le_gamma {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c₀ E r₀ s₀ v₀ σ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀)
    (hC : FreshClass F A c₀ E r₀ s₀ v₀) (hσ : σ ∈ Icc (c₀ - s₀) c₀) {z : ℂ}
    (hx : |z.re - E| ≤ r₀) (hη : 0 ≤ z.im) (hη1 : z.im ≤ 1) (q : Fin N → ℂ) :
    (star q ⬝ᵥ (freshM F σ z *ᵥ q)).im ≤
      gammaCompConst c₀ r₀ s₀ v₀ * quadForm (freshGamma F c₀ E) q := by
  obtain ⟨hF, -, hR⟩ := hC
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have hκ : 0 < (c₀ - s₀) * v₀ := mul_pos (by linarith) hv0
  -- bounds on `m_σ(z)` and `m₀ = m_{c₀}(E)`
  obtain ⟨hm1, hm2⟩ := fresh_regular_bounds hR hσ hx hη hη1
  have hσ' : c₀ ∈ Icc (c₀ - s₀) c₀ := ⟨by linarith, le_rfl⟩
  have hxE : |((E : ℂ)).re - E| ≤ r₀ := by simp [hr0.le]
  obtain ⟨hm01, hm02⟩ := fresh_regular_bounds hR hσ' hxE (by simp) (by simp)
  set w := freshW F σ z
  set w₀ := freshW F c₀ (E : ℂ)
  have hwim : w.im = z.im + σ * (freshDyson F σ z).im := freshW_im F σ z
  have hw0im : w₀.im = c₀ * (freshDyson F c₀ E).im := by
    simp [w₀, freshW_im]
  have hκw : (c₀ - s₀) * v₀ ≤ w.im := by
    rw [hwim]; nlinarith [hσ.1, hm1]
  have hκw0 : (c₀ - s₀) * v₀ ≤ w₀.im := by
    rw [hw0im]; nlinarith [hm01]
  have hwpos : 0 < w.im := lt_of_lt_of_le hκ hκw
  have hw0pos : 0 < w₀.im := lt_of_lt_of_le hκ hκw0
  have hmn := freshDyson_norm_le hF hN hσ0 hη (lt_of_lt_of_le hv0 hm1)
  have hm0n := freshDyson_norm_le hF hN hc0 (by simp : (0 : ℝ) ≤ ((E : ℂ)).im)
    (lt_of_lt_of_le hv0 hm01)
  -- `|w - w₀| ≤ B`
  have hB : ‖w - w₀‖ ≤ r₀ + 1 + 2 * c₀ / ((c₀ - s₀) * v₀) := by
    have e : w - w₀ = (z - E) + ((σ : ℂ) * freshDyson F σ z - (c₀ : ℂ) * freshDyson F c₀ E) := by
      simp only [w, w₀, freshW]; ring
    rw [e]
    have hz : ‖z - (E : ℂ)‖ ≤ r₀ + 1 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
      rw [abs_of_nonneg hη]; linarith
    have h1 : ‖(σ : ℂ) * freshDyson F σ z‖ ≤ c₀ / ((c₀ - s₀) * v₀) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ0]
      calc σ * ‖freshDyson F σ z‖ ≤ c₀ * (w.im)⁻¹ :=
            mul_le_mul hσ.2 hmn (norm_nonneg _) hc0.le
        _ ≤ c₀ * ((c₀ - s₀) * v₀)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hκ hκw) hc0.le
        _ = c₀ / ((c₀ - s₀) * v₀) := by rw [div_eq_mul_inv]
    have h2 : ‖(c₀ : ℂ) * freshDyson F c₀ E‖ ≤ c₀ / ((c₀ - s₀) * v₀) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
      calc c₀ * ‖freshDyson F c₀ E‖ ≤ c₀ * (w₀.im)⁻¹ :=
            mul_le_mul_of_nonneg_left hm0n hc0.le
        _ ≤ c₀ * ((c₀ - s₀) * v₀)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hκ hκw0) hc0.le
        _ = c₀ / ((c₀ - s₀) * v₀) := by rw [div_eq_mul_inv]
    calc ‖(z - E) + ((σ : ℂ) * freshDyson F σ z - (c₀ : ℂ) * freshDyson F c₀ E)‖
        ≤ ‖z - (E : ℂ)‖ + (‖(σ : ℂ) * freshDyson F σ z‖ + ‖(c₀ : ℂ) * freshDyson F c₀ E‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
      _ ≤ (r₀ + 1) + (c₀ / ((c₀ - s₀) * v₀) + c₀ / ((c₀ - s₀) * v₀)) :=
          add_le_add hz (add_le_add h1 h2)
      _ = r₀ + 1 + 2 * c₀ / ((c₀ - s₀) * v₀) := by ring
  -- the comparison
  have hcmp := resolvent_nsq_compare hF hwpos hw0pos.ne' q
  have hratio : ‖w - w₀‖ ^ 2 / w.im ^ 2 ≤
      (r₀ + 1 + 2 * c₀ / ((c₀ - s₀) * v₀)) ^ 2 / ((c₀ - s₀) * v₀) ^ 2 := by
    have hBn : 0 ≤ ‖w - w₀‖ := norm_nonneg _
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hBn hB 2) (by positivity)
      (pow_le_pow_left₀ hκ.le hκw 2)
  have hy : 0 ≤ nsq (freshM F c₀ E *ᵥ q) := Finset.sum_nonneg fun _ _ => by positivity
  have hM0 : freshM F c₀ E = (F - w₀ • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl
  have hM : freshM F σ z = (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl
  have hquad := freshM_quad_im hF hwpos.ne' q
  have hfac : z.im + σ * (freshDyson F σ z).im ≤ 1 + c₀ / v₀ := by
    have : σ * (freshDyson F σ z).im ≤ c₀ * v₀⁻¹ :=
      mul_le_mul hσ.2 hm2 (by linarith [hm1]) hc0.le
    rw [div_eq_mul_inv]; linarith
  have hfac0 : 0 ≤ z.im + σ * (freshDyson F σ z).im := by
    have : 0 ≤ (freshDyson F σ z).im := le_trans hv0.le hm1
    positivity
  rw [hquad, freshGamma_quad_eq hF]
  have hn0 : 0 ≤ nsq (freshM F σ z *ᵥ q) := Finset.sum_nonneg fun _ _ => by positivity
  have hcmp' : nsq (freshM F σ z *ᵥ q) ≤ 2 * (1 + (r₀ + 1 + 2 * c₀ / ((c₀ - s₀) * v₀)) ^ 2 /
      ((c₀ - s₀) * v₀) ^ 2) * nsq (freshM F c₀ E *ᵥ q) := by
    rw [hM, hM0]
    refine hcmp.trans (mul_le_mul_of_nonneg_right ?_ (by rw [← hM0]; exact hy))
    linarith
  unfold gammaCompConst
  simp only
  calc (z.im + σ * (freshDyson F σ z).im) * nsq (freshM F σ z *ᵥ q)
      ≤ (1 + c₀ / v₀) * (2 * (1 + (r₀ + 1 + 2 * c₀ / ((c₀ - s₀) * v₀)) ^ 2 /
          ((c₀ - s₀) * v₀) ^ 2) * nsq (freshM F c₀ E *ᵥ q)) :=
        mul_le_mul hfac hcmp' hn0 (by positivity)
    _ = (1 + c₀ / v₀) * (2 * (1 + (r₀ + 1 + 2 * c₀ / ((c₀ - s₀) * v₀)) ^ 2 /
          ((c₀ - s₀) * v₀) ^ 2)) / c₀ * (c₀ * nsq (freshM F c₀ E *ᵥ q)) := by
        field_simp

/-- The energy is polynomially bounded: `|E| ≤ N^A + 2/v₀`. -/
theorem abs_E_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c₀ E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀) :
    |E| ≤ (N : ℝ) ^ A + 2 / v₀ := by
  obtain ⟨hF, hNB, hR⟩ := hC
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hσ' : c₀ ∈ Icc (c₀ - s₀) c₀ := ⟨by linarith, le_rfl⟩
  have hxE : |((E : ℂ)).re - E| ≤ r₀ := by simp [hr0.le]
  obtain ⟨hm01, -⟩ := fresh_regular_bounds hR hσ' hxE (by simp) (by simp)
  have hre := freshW_re_abs_le hF hN hNB hc0 (by simp : (0 : ℝ) ≤ ((E : ℂ)).im) hv0 hm01
  have hm0n := freshDyson_norm_le hF hN hc0 (by simp : (0 : ℝ) ≤ ((E : ℂ)).im)
    (lt_of_lt_of_le hv0 hm01)
  have hw0im : (freshW F c₀ (E : ℂ)).im = c₀ * (freshDyson F c₀ E).im := by
    simp [freshW_im]
  have hwpos : c₀ * v₀ ≤ (freshW F c₀ (E : ℂ)).im := by rw [hw0im]; nlinarith
  have hre_eq : (freshW F c₀ (E : ℂ)).re = E + c₀ * (freshDyson F c₀ E).re := by
    simp [freshW]
  have hmre : |c₀ * (freshDyson F c₀ E).re| ≤ 1 / v₀ := by
    rw [abs_mul, abs_of_pos hc0]
    calc c₀ * |(freshDyson F c₀ E).re| ≤ c₀ * ((freshW F c₀ (E : ℂ)).im)⁻¹ :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hm0n) hc0.le
      _ ≤ c₀ * (c₀ * v₀)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hwpos) hc0.le
      _ = 1 / v₀ := by field_simp
  have : E = (freshW F c₀ (E : ℂ)).re - c₀ * (freshDyson F c₀ E).re := by rw [hre_eq]; ring
  rw [this]
  calc |(freshW F c₀ (E : ℂ)).re - c₀ * (freshDyson F c₀ E).re|
      ≤ |(freshW F c₀ (E : ℂ)).re| + |c₀ * (freshDyson F c₀ E).re| := abs_sub _ _
    _ ≤ ((N : ℝ) ^ A + v₀⁻¹) + 1 / v₀ := add_le_add hre hmre
    _ = (N : ℝ) ^ A + 2 / v₀ := by rw [inv_eq_one_div]; ring

theorem norm_z_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c₀ E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀) {z : ℂ}
    (hx : |z.re - E| ≤ r₀) (hη : 0 ≤ z.im) (hη1 : z.im ≤ 1) :
    ‖z‖ ≤ (N : ℝ) ^ A + 2 / v₀ + r₀ + 1 := by
  have hE := abs_E_le hN hK hC
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  have : |z.re| ≤ |E| + r₀ := by
    have := abs_sub_abs_le_abs_sub z.re E; linarith
  rw [abs_of_nonneg hη]; linarith

/-- `ρ(M_σ(z)) = Im m_σ(z)/π ≥ v₀/π` (with `M = freshM`). -/
theorem sourceDensity_freshM_ge {F : Matrix (Fin N) (Fin N) ℂ} {A c₀ E r₀ s₀ v₀ σ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    (hσ : σ ∈ Icc (c₀ - s₀) c₀) {z : ℂ} (hx : |z.re - E| ≤ r₀) (hη : 0 ≤ z.im) (hη1 : z.im ≤ 1) :
    v₀ / Real.pi ≤ CEH.sourceDensity (freshM F σ z) := by
  obtain ⟨hm1, -⟩ := fresh_regular_bounds hC.2.2 hσ hx hη hη1
  have hm : 0 < (freshDyson F σ z).im := lt_of_lt_of_le hK.2.2.2.2.2 hm1
  unfold CEH.sourceDensity
  rw [freshM_normalizedTrace hm, abs_of_pos hm]
  exact div_le_div_of_nonneg_right hm1 Real.pi_pos.le

/-- **The CEH domain on the bulk window.** -/
theorem inLocalLawDomain_of_bulk (hMDE : MDEBranchIdentification) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} {A c₀ E r₀ s₀ v₀ σ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀)
    (hC : FreshClass F A c₀ E r₀ s₀ v₀) (hσ : σ ∈ Icc (c₀ - s₀) c₀) {z : ℂ}
    (hx : |z.re - E| ≤ r₀) (hη : 0 < z.im) (hη1 : z.im ≤ 1)
    (M : CEH.MDEBranch (Real.sqrt σ) ⟨F, hC.1⟩) {κ ε : ℝ}
    (hdens : (N : ℝ) ^ ε ≤ (N : ℝ) * z.im * (v₀ / Real.pi))
    (hnorm : ‖z‖ ≤ Real.sqrt σ * (N : ℝ) ^ (κ + 1 / ε)) :
    CEH.InLocalLawDomain M κ ε z := by
  have hσ0 : 0 < σ := by linarith [hσ.1, hK.2.2.2.2.1, hK.1]
  obtain ⟨hm1, -⟩ := fresh_regular_bounds hC.2.2 hσ hx hη.le hη1
  have hm : 0 < (freshDyson F σ z).im := lt_of_lt_of_le hK.2.2.2.2.2 hm1
  have hMeq := mdeBranch_matrix_eq_freshM hMDE hN hC.1 hσ0 hη hm M
  refine ⟨hη.ne', ?_, hnorm⟩
  rw [hMeq, abs_of_pos hη]
  have hd := sourceDensity_freshM_ge hK hC hσ hx hη.le hη1
  have : (N : ℝ) * z.im * (v₀ / Real.pi) ≤ (N : ℝ) * z.im * CEH.sourceDensity (freshM F σ z) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  linarith

end BlockBand.Palm.MomentFlow
