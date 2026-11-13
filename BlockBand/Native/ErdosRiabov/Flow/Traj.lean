module

public import BlockBand.Native.ErdosRiabov.Kernel.VSKernel
public import BlockBand.Native.ErdosRiabov.VS.ResolventItoFlow

/-!
# The VS characteristic and its smooth saturation

Properties of the VS characteristic `z_t = z + (1-t)m` and its height, and the identification
with the saturated trajectory.

For `z` with `m = semicircleM z`, the VS trajectory is `z_t = z + (1-t)m` (`vsTraj`). Its height
`η_t = Im z_t` is the Kernel height `vsHeight z t = Im z + (1-t) Im m` (`vsTraj_im`). With `z ∈ 𝒟`
(`Kernel.BulkDomain N δ₀ κ C₀ z`) and the phase lemma `Kernel.semicircleM_phase`:
* (a) `-1/m = z_t + tm`, i.e. `t m² + z_t m + 1 = 0` (`vsFlow_a`);
* (b) `η_t = (ρ⁻¹ - tρ) sin θ`, `η̇_t = -Im m ∈ [-1, -c_m]`, `η ≤ η_t ≤ η_0 = Im m/|m|² ≤ C₀+1`,
  `η_0 ≥ s_κ ≥ c_m`, `η_s - η_t = (t-s) Im m`, `t-s ≤ (η_s-η_t)/c_m ≤ η_s/c_m` (`vsFlow_b`);
* (c) `1 - t|m|² = η_t |m|²/Im m`, `t|m|² < 1` (`vsFlow_c`);
* (d) `z_0 = -1/m`, `z_1 = z`, `z̄_t` is the trajectory of `z̄` (with `m(z̄) = m̄`),
  `Im z̄_t = -η_t`, `z_t - z̄_t = 2iη_t` (`vsFlow_d`);
* (K0) `η_t ≥ (3/4) c_m` for `t ≤ 1/4` (`vsFlow_K0`);
* (e) for `t ∈ (0,1]`, `w_t = z_t/√t` has `m(w_t) = √t m` (`Kernel.semicircleM_vsScale`),
  `Im w_t = η_t/√t`, and `w(σ) = e^{-σ/2} z_{e^σ}` solves the characteristic flow
  `dw/dσ = -w/2 - m(w)` for `σ ≤ 0` (`vsFlow_e`, `hasDerivAt_vsChar`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Flow

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open scoped ComplexConjugate

/-- The VS characteristic `z_t = z + (1-t) m(z)`. -/
def vsTraj (z : ℂ) (t : ℝ) : ℂ := z + (1 - (t : ℂ)) * semicircleM z

/-- The rescaled characteristic `w(σ) = e^{-σ/2} z_{e^σ}` (time `σ = log t`). -/
def vsChar (z : ℂ) (σ : ℝ) : ℂ := (Real.exp (-σ / 2) : ℂ) * vsTraj z (Real.exp σ)

/-- `Im z_t = η_t = vsHeight z t`. -/
theorem vsTraj_im (z : ℂ) (t : ℝ) : (vsTraj z t).im = vsHeight z t := by
  simp [vsTraj, vsHeight, Complex.mul_im]

theorem continuous_vsHeight (z : ℂ) : Continuous (vsHeight z) := by
  unfold vsHeight
  fun_prop

/-- `η_s > 0` for `s ≤ 1` when `Im z > 0`. -/
theorem vsHeight_pos {z : ℂ} (hη : 0 < z.im) {s : ℝ} (hs : s ≤ 1) : 0 < vsHeight z s := by
  have hy := semicircleM_im_pos hη
  unfold vsHeight
  nlinarith

theorem vsHeight_sub (z : ℂ) (s t : ℝ) :
    vsHeight z s - vsHeight z t = (t - s) * (semicircleM z).im := by
  unfold vsHeight
  ring

/-- **(a)** (MDE for the profile `tS`): `-1/m = z_t + tm`, equivalently
`t m² + z_t m + 1 = 0`, for every `z` and real `t`. -/
theorem vsFlow_a (z : ℂ) (t : ℝ) :
    -1 / semicircleM z = vsTraj z t + t * semicircleM z ∧
      (t : ℂ) * semicircleM z ^ 2 + vsTraj z t * semicircleM z + 1 = 0 := by
  have hroot := semicircleM_dyson z
  have hm0 := ne_zero_of_root hroot
  refine ⟨?_, ?_⟩
  · rw [eq_comm, eq_div_iff hm0]
    unfold vsTraj
    linear_combination hroot
  · unfold vsTraj
    linear_combination hroot

/-- `η_t = (ρ⁻¹ - tρ) sin θ` with `m = ρ e^{iθ}` (every `z`, `t`). -/
theorem vsHeight_eq_polar (z : ℂ) (t : ℝ) :
    vsHeight z t = (‖semicircleM z‖⁻¹ - t * ‖semicircleM z‖) *
      ((semicircleM z).im / ‖semicircleM z‖) := by
  have hroot := semicircleM_dyson z
  have h := im_identity_of_root hroot
  set m := semicircleM z
  have hρ : ‖m‖ ≠ 0 := norm_ne_zero_iff.mpr (ne_zero_of_root hroot)
  have e1 : (‖m‖⁻¹ - t * ‖m‖) * (m.im / ‖m‖) = m.im / ‖m‖ ^ 2 - t * m.im := by
    field_simp
  have e2 : z.im = m.im / ‖m‖ ^ 2 - m.im := by
    rw [eq_sub_iff_add_eq, eq_div_iff (pow_ne_zero 2 hρ)]
    linear_combination h
  rw [vsHeight, e1, e2]
  ring

/-- `η_0 = Im m/|m|²` (every `z`). -/
theorem vsHeight_zero_eq (z : ℂ) :
    vsHeight z 0 = (semicircleM z).im / ‖semicircleM z‖ ^ 2 := by
  rw [vsHeight_eq_polar]
  have hρ : ‖semicircleM z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (ne_zero_of_root (semicircleM_dyson z))
  field_simp
  ring

theorem hasDerivAt_vsHeight (z : ℂ) (t : ℝ) :
    HasDerivAt (vsHeight z) (-(semicircleM z).im) t := by
  show HasDerivAt (fun x => z.im + (1 - x) * (semicircleM z).im) _ t
  have h := (((hasDerivAt_id' t).const_sub 1).mul_const (semicircleM z).im).const_add z.im
  simpa using h

/-- Positivity of `c_m` on the bulk. -/
theorem imLower_pos {κ C₀ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hC₀ : 0 ≤ C₀) :
    0 < imLower κ C₀ :=
  div_pos (bulkSin_pos hκ hκ2) (by linarith)

theorem imLower_le_bulkSin {κ C₀ : ℝ} (hC₀ : 0 ≤ C₀) : imLower κ C₀ ≤ bulkSin κ := by
  unfold imLower
  rw [div_le_iff₀ (by linarith)]
  nlinarith [bulkSin_nonneg κ]

theorem kappa_le_two_of_bulk {N : ℕ} {δ₀ κ C₀ : ℝ} {z : ℂ} (hz : BulkDomain N δ₀ κ C₀ z) :
    κ ≤ 2 := by
  linarith [abs_nonneg z.re, hz.1]

/-- For `N ≥ 1`, `0 < κ`, `C₀ ≥ 0` and
`z ∈ 𝒟 = BulkDomain N δ₀ κ C₀ z`, with `m = semicircleM z`, `η_t = vsHeight z t`,
`c_m = imLower κ C₀`, `s_κ = bulkSin κ`:
`η_t = Im z + (1-t) Im m = (ρ⁻¹ - tρ) sin θ`;
`η̇_t = -Im m` with `c_m ≤ Im m ≤ 1`; for `t ∈ [0,1]`, `Im z ≤ η_t ≤ η_0`;
`η_0 = Im m/|m|² ≤ C₀+1`;
`c_m ≤ s_κ ≤ η_0`;
`η_s - η_t = (t-s) Im m`; and for
`0 ≤ s ≤ t ≤ 1`, `t - s ≤ (η_s - η_t)/c_m ≤ η_s/c_m`.
-/
theorem vsFlow_b {N : ℕ} {δ₀ κ C₀ : ℝ} {z : ℂ} (hN : 0 < N) (hκ : 0 < κ) (hC₀ : 0 ≤ C₀)
    (hz : BulkDomain N δ₀ κ C₀ z) :
    (∀ t : ℝ, vsHeight z t = (‖semicircleM z‖⁻¹ - t * ‖semicircleM z‖) *
        ((semicircleM z).im / ‖semicircleM z‖)) ∧
      (∀ t : ℝ, HasDerivAt (vsHeight z) (-(semicircleM z).im) t) ∧
      imLower κ C₀ ≤ (semicircleM z).im ∧ (semicircleM z).im ≤ 1 ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → z.im ≤ vsHeight z t ∧ vsHeight z t ≤ vsHeight z 0) ∧
      vsHeight z 0 = (semicircleM z).im / ‖semicircleM z‖ ^ 2 ∧ vsHeight z 0 ≤ C₀ + 1 ∧
      imLower κ C₀ ≤ bulkSin κ ∧ bulkSin κ ≤ vsHeight z 0 ∧
      (∀ s t : ℝ, vsHeight z s - vsHeight z t = (t - s) * (semicircleM z).im) ∧
      (∀ s t : ℝ, s ≤ t → t ≤ 1 →
        t - s ≤ (vsHeight z s - vsHeight z t) / imLower κ C₀ ∧
          (vsHeight z s - vsHeight z t) / imLower κ C₀ ≤ vsHeight z s / imLower κ C₀) := by
  have hη := hz.im_pos hN
  have hκ2 := kappa_le_two_of_bulk hz
  have hroot := semicircleM_dyson z
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hy := semicircleM_im_pos hη
  have hcm := semicircleM_im_ge hC₀ hz.1 hη hz.2.2
  have hcm0 := imLower_pos hκ hκ2 hC₀
  have hsin := semicircleM_sin_ge hz.1 hη
  set m := semicircleM z with hmdef
  have hρ : 0 < ‖m‖ := norm_pos_iff.mpr (ne_zero_of_root hroot)
  have hyρ : m.im ≤ ‖m‖ := (le_abs_self _).trans (Complex.abs_im_le_norm m)
  have hy1 : m.im ≤ 1 := by linarith
  have h0 : vsHeight z 0 = z.im + m.im := by simp [vsHeight, hmdef]
  refine ⟨vsHeight_eq_polar z, hasDerivAt_vsHeight z, hcm, hy1, fun t ht0 ht1 => ?_,
    vsHeight_zero_eq z, ?_, imLower_le_bulkSin hC₀, ?_, vsHeight_sub z, fun s t hst ht1 => ?_⟩
  · unfold vsHeight
    constructor <;> nlinarith
  · rw [h0]
    have : z.im ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm z)
    linarith [hz.2.2]
  · rw [vsHeight_zero_eq z, ← hmdef]
    calc bulkSin κ ≤ m.im / ‖m‖ := hsin
      _ ≤ m.im / ‖m‖ ^ 2 := by
        apply div_le_div_of_nonneg_left hy.le (by positivity)
        nlinarith
  · rw [vsHeight_sub z s t, ← hmdef]
    have hηt : 0 < vsHeight z t := by unfold vsHeight; nlinarith
    constructor
    · rw [le_div_iff₀ hcm0]
      nlinarith
    · apply div_le_div_of_nonneg_right _ hcm0.le
      rw [← vsHeight_sub z s t]
      linarith

/-- **(c)**: `1 - t|m|² = η_t |m|²/Im m` (every real `t`), and `t|m|² < 1` for `t ≤ 1`;
here only `Im z > 0` is used. -/
theorem vsFlow_c {z : ℂ} (hη : 0 < z.im) (t : ℝ) :
    1 - t * ‖semicircleM z‖ ^ 2 = vsHeight z t * ‖semicircleM z‖ ^ 2 / (semicircleM z).im ∧
      (t ≤ 1 → t * ‖semicircleM z‖ ^ 2 < 1) := by
  have hy := semicircleM_im_pos hη
  have hid := vsHeight_identity z t
  have hroot := semicircleM_dyson z
  have hρ : 0 < ‖semicircleM z‖ := norm_pos_iff.mpr (ne_zero_of_root hroot)
  have heq : 1 - t * ‖semicircleM z‖ ^ 2 =
      vsHeight z t * ‖semicircleM z‖ ^ 2 / (semicircleM z).im := by
    rw [eq_div_iff hy.ne']
    linear_combination (-1 : ℝ) * hid
  refine ⟨heq, fun ht1 => ?_⟩
  have hηt : 0 < vsHeight z t := by unfold vsHeight; nlinarith
  have : 0 < vsHeight z t * ‖semicircleM z‖ ^ 2 / (semicircleM z).im := by positivity
  linarith

/-- **(d)**: `z_0 = -1/m`, `z_1 = z`; for `Im z ≠ 0`, the trajectory of `z̄` is `z̄_t`
(`m(z̄) = m̄`), `Im z̄_t = -η_t`, and `z_t - z̄_t = 2iη_t`. -/
theorem vsFlow_d {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    vsTraj z 0 = -1 / semicircleM z ∧ vsTraj z 1 = z ∧
      semicircleM (conj z) = conj (semicircleM z) ∧
      vsTraj (conj z) t = conj (vsTraj z t) ∧ (vsTraj (conj z) t).im = -vsHeight z t ∧
      vsTraj z t - conj (vsTraj z t) = 2 * (vsHeight z t : ℂ) * Complex.I := by
  have hconj := semicircleM_conj hz
  have htraj : vsTraj (conj z) t = conj (vsTraj z t) := by
    unfold vsTraj
    rw [hconj]
    simp [map_add, map_mul, map_sub]
  refine ⟨?_, by simp [vsTraj], hconj, htraj, ?_, ?_⟩
  · rw [(vsFlow_a z 0).1]
    simp
  · rw [htraj, Complex.conj_im, vsTraj_im]
  · rw [Complex.sub_conj, vsTraj_im]
    push_cast
    ring

/-- **(K0)**: `η_t ≥ (3/4) c_m` for `t ≤ 1/4` (`N ≥ 1`, `C₀ ≥ 0`, `z ∈ 𝒟`). -/
theorem vsFlow_K0 {N : ℕ} {δ₀ κ C₀ : ℝ} {z : ℂ} (hN : 0 < N) (hC₀ : 0 ≤ C₀)
    (hz : BulkDomain N δ₀ κ C₀ z) {t : ℝ} (ht : t ≤ 1 / 4) :
    3 / 4 * imLower κ C₀ ≤ vsHeight z t := by
  have hη := hz.im_pos hN
  have hcm := semicircleM_im_ge hC₀ hz.1 hη hz.2.2
  have hy := semicircleM_im_pos hη
  unfold vsHeight
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - t - 3 / 4 by linarith) hy.le]

/-- **(e)**, rescaled point: for `Im z > 0` and `t ∈ (0,1]`, `w_t = z_t/√t` satisfies
`m(w_t) = √t m`, `ν = √t m` solves `ν² + w_t ν + 1 = 0` with `|ν| < 1`, and
`Im w_t = η_t/√t > 0`. -/
theorem vsFlow_e {z : ℂ} (hη : 0 < z.im) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    semicircleM (vsTraj z t / (Real.sqrt t : ℂ)) = (Real.sqrt t : ℂ) * semicircleM z ∧
      ((Real.sqrt t : ℂ) * semicircleM z) ^ 2 +
          vsTraj z t / (Real.sqrt t : ℂ) * ((Real.sqrt t : ℂ) * semicircleM z) + 1 = 0 ∧
      ‖(Real.sqrt t : ℂ) * semicircleM z‖ < 1 ∧
      (vsTraj z t / (Real.sqrt t : ℂ)).im = vsHeight z t / Real.sqrt t ∧
      0 < vsHeight z t / Real.sqrt t := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hscale := semicircleM_vsScale hη.ne' ht0 ht1
  have hw := semicircleM_dyson (vsTraj z t / (Real.sqrt t : ℂ))
  have hwim : (vsTraj z t / (Real.sqrt t : ℂ)).im = vsHeight z t / Real.sqrt t := by
    rw [Complex.div_ofReal_im, vsTraj_im]
  have hpos : 0 < vsHeight z t / Real.sqrt t := by
    have hy := semicircleM_im_pos hη
    have : 0 < vsHeight z t := by unfold vsHeight; nlinarith
    positivity
  have hscale' : semicircleM (vsTraj z t / (Real.sqrt t : ℂ)) =
      (Real.sqrt t : ℂ) * semicircleM z := hscale
  refine ⟨hscale', ?_, ?_, hwim, hpos⟩
  · rw [← hscale']
    exact hw
  · rw [← hscale']
    apply norm_semicircleM_lt_one
    rw [hwim]
    exact hpos.ne'

/-- `w(σ) = z_t/√t` with `t = e^σ`. -/
theorem vsChar_eq (z : ℂ) (σ : ℝ) :
    vsChar z σ = vsTraj z (Real.exp σ) / (Real.sqrt (Real.exp σ) : ℂ) := by
  have hs : Real.sqrt (Real.exp σ) = Real.exp (σ / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have hinv : Real.exp (-σ / 2) = (Real.exp (σ / 2))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  rw [vsChar, hs, hinv, div_eq_inv_mul]
  push_cast
  ring

/-- **(e)**, the characteristic flow: for `Im z > 0` and `σ ≤ 0`, `dw/dσ = -w/2 - m(w)` for
`w(σ) = e^{-σ/2} z_{e^σ}`. -/
theorem hasDerivAt_vsChar {z : ℂ} (hη : 0 < z.im) {σ : ℝ} (hσ : σ ≤ 0) :
    HasDerivAt (vsChar z) (-vsChar z σ / 2 - semicircleM (vsChar z σ)) σ := by
  set m := semicircleM z with hmdef
  have hfun : vsChar z = fun x => (Real.exp (-x / 2) : ℂ) * z +
      ((Real.exp (-x / 2) : ℂ) - (Real.exp (x / 2) : ℂ)) * m := by
    funext x
    have he : Real.exp (-x / 2) * Real.exp x = Real.exp (x / 2) := by
      rw [← Real.exp_add]
      ring_nf
    have he' : (Real.exp (-x / 2) : ℂ) * (Real.exp x : ℂ) = (Real.exp (x / 2) : ℂ) := by
      exact_mod_cast he
    unfold vsChar vsTraj
    rw [← hmdef]
    linear_combination (-m) * he'
  have hf : HasDerivAt (fun x => Real.exp (-x / 2)) (Real.exp (-σ / 2) * (-1 / 2)) σ := by
    have := ((hasDerivAt_id' σ).neg.div_const 2).exp
    simpa [neg_div] using this
  have hg : HasDerivAt (fun x => Real.exp (x / 2)) (Real.exp (σ / 2) * (1 / 2)) σ := by
    have := ((hasDerivAt_id' σ).div_const 2).exp
    simpa using this
  have hF := hf.ofReal_comp
  have hG := hg.ofReal_comp
  have hD := (hF.mul_const z).add ((hF.sub hG).mul_const m)
  have ht0 : 0 < Real.exp σ := Real.exp_pos σ
  have ht1 : Real.exp σ ≤ 1 := Real.exp_le_one_iff.mpr hσ
  have hm := (vsFlow_e hη ht0 ht1).1
  have hs : Real.sqrt (Real.exp σ) = Real.exp (σ / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  rw [← vsChar_eq, hs] at hm
  have hval := congrFun hfun σ
  rw [hm, hval, hfun]
  convert hD using 1
  push_cast
  ring

/-!
## Bridge to the smooth saturation `vsSat`
-/

/-- `z_t` is `vsSpec z m id t` (`m = semicircleM z`). -/
theorem vsTraj_eq_vsSpec (z : ℂ) (t : ℝ) :
    vsTraj z t = VS.vsSpec z (semicircleM z) id t := by
  simp [vsTraj, VS.vsSpec]

/-- The saturated trajectory is `z_{c(t)}`: `vsSpec z m (vsSat δ) t = z_{vsSat δ t}` for every
real `t` and `δ`. -/
theorem vsSpec_vsSat_eq (z : ℂ) (δ t : ℝ) :
    VS.vsSpec z (semicircleM z) (VS.vsSat δ) t = vsTraj z (VS.vsSat δ t) := by
  simp [vsTraj, VS.vsSpec]

/-- Height of the saturated trajectory: `Im vsSpec z m (vsSat δ) t = η_{vsSat δ t}`. -/
theorem im_vsSpec_vsSat (z : ℂ) (δ t : ℝ) :
    (VS.vsSpec z (semicircleM z) (VS.vsSat δ) t).im = vsHeight z (VS.vsSat δ t) := by
  rw [vsSpec_vsSat_eq, vsTraj_im]

/-- On `t ≤ 1` (`δ ≥ 0`) the saturated trajectory is `z_t` and its height is `η_t`. -/
theorem vsSpec_vsSat_of_le_one (z : ℂ) {δ t : ℝ} (hδ : 0 ≤ δ) (ht : t ≤ 1) :
    VS.vsSpec z (semicircleM z) (VS.vsSat δ) t = vsTraj z t ∧
      (VS.vsSpec z (semicircleM z) (VS.vsSat δ) t).im = vsHeight z t := by
  rw [vsSpec_vsSat_eq, VS.vsSat_of_le_one hδ ht, vsTraj_im]
  exact ⟨rfl, rfl⟩

/-- For `Im z > 0` and `δ = Im z/(2 Im m)` (the level of `VS.half_le_abs_im_vsSpec`), every
point of the saturated trajectory has height in `[Im z/2, ∞)`:
`Im z/2 ≤ η_{vsSat δ t}` for every real `t`. -/
theorem half_le_vsHeight_vsSat {z : ℂ} (hη : 0 < z.im) (t : ℝ) :
    z.im / 2 ≤ vsHeight z (VS.vsSat (z.im / (2 * (semicircleM z).im)) t) := by
  have h := VS.half_le_abs_im_vsSpec hη (semicircleM_im_pos hη) false t
  simp only [VS.patConj, Bool.false_eq_true, ite_false] at h
  rw [im_vsSpec_vsSat] at h
  have hy := semicircleM_im_pos hη
  have hpos : 0 < vsHeight z (VS.vsSat (z.im / (2 * (semicircleM z).im)) t) := by
    have hδ : 0 < z.im / (2 * (semicircleM z).im) := div_pos hη (by linarith)
    have hle := VS.vsSat_le hδ t
    have hδy : z.im / (2 * (semicircleM z).im) * (semicircleM z).im = z.im / 2 := by
      field_simp
    unfold vsHeight
    nlinarith
  rwa [abs_of_pos hpos] at h

/-- For
`N ≥ 1`, `0 < κ`, `C₀ ≥ 0`, `z ∈ 𝒟 = BulkDomain N δ₀ κ C₀ z`, `m = semicircleM z`,
`η_t = vsHeight z t = Im z_t`, `c_m = imLower κ C₀`:
(a) `-1/m = z_t + tm`;
(b) `c_m ≤ Im m ≤ 1`, `η̇_t = -Im m`, `η ≤ η_t ≤ η_0 ≤ C₀+1` on `[0,1]`, `η_0 ≥ s_κ ≥ c_m`;
(c) `t|m|² < 1` for `t ≤ 1`;
(d) `z_0 = -1/m`, `z_1 = z`, `z_t - z̄_t = 2iη_t`;
(K0) `η_t ≥ (3/4)c_m` for `t ≤ 1/4`.
-/
theorem vsFlow_facts {N : ℕ} {δ₀ κ C₀ : ℝ} {z : ℂ} (hN : 0 < N) (hκ : 0 < κ) (hC₀ : 0 ≤ C₀)
    (hz : BulkDomain N δ₀ κ C₀ z) :
    (∀ t : ℝ, -1 / semicircleM z = vsTraj z t + t * semicircleM z) ∧
      (∀ t : ℝ, (vsTraj z t).im = vsHeight z t) ∧
      imLower κ C₀ ≤ (semicircleM z).im ∧ (semicircleM z).im ≤ 1 ∧
      (∀ t : ℝ, HasDerivAt (vsHeight z) (-(semicircleM z).im) t) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → z.im ≤ vsHeight z t ∧ vsHeight z t ≤ vsHeight z 0) ∧
      vsHeight z 0 ≤ C₀ + 1 ∧ imLower κ C₀ ≤ bulkSin κ ∧ bulkSin κ ≤ vsHeight z 0 ∧
      (∀ t : ℝ, t ≤ 1 → t * ‖semicircleM z‖ ^ 2 < 1) ∧
      vsTraj z 0 = -1 / semicircleM z ∧ vsTraj z 1 = z ∧
      (∀ t : ℝ, vsTraj z t - conj (vsTraj z t) = 2 * (vsHeight z t : ℂ) * Complex.I) ∧
      (∀ t : ℝ, t ≤ 1 / 4 → 3 / 4 * imLower κ C₀ ≤ vsHeight z t) := by
  have hη := hz.im_pos hN
  obtain ⟨_, hder, hcm, hy1, hbd, _, hC, hcs, hs0, _, _⟩ := vsFlow_b hN hκ hC₀ hz
  have hd0 := vsFlow_d hη.ne' 0
  exact ⟨fun t => (vsFlow_a z t).1, vsTraj_im z, hcm, hy1, hder, hbd, hC, hcs, hs0,
    fun t ht => (vsFlow_c hη t).2 ht, hd0.1, hd0.2.1, fun t => (vsFlow_d hη.ne' t).2.2.2.2.2,
    fun t ht => vsFlow_K0 hN hC₀ hz ht⟩

end BlockBand.Native.ErdosRiabov.Flow
