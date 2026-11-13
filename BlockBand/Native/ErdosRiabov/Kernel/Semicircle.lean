module

public import BlockBand.External.ErdosRiabov.Semicircle

/-!
# Semicircle facts for the variance-scaling flow

Uniqueness of the root `m(w)`, phase and size bounds for `m(z)` in the bulk, and the rescaling
identity along the variance-scaling flow.

* `semicircleM_eq_of_root`: if `Im w ≠ 0`, `|ν| < 1` and `ν² + wν + 1 = 0` then
  `semicircleM w = ν`. The other root is `1/m` (product of the roots is one), so a second root of
  modulus `< 1` would give `|m ν| = 1` with `|m|, |ν| < 1`. The "no root on the unit circle" fact
  is also recorded (`norm_ne_one_of_root`), although the uniqueness proof does not use it.
* `semicircleM_phase` (the phase lemma (a)-(c)): for `|Re z| ≤ 2 - κ`, `Im z > 0`
  (and `‖z‖ ≤ C₀` for (b), (c)-lower), with `s_κ = bulkSin κ`, `κ' = phaseConst κ`,
  `c_m = imLower κ C₀`:
  (a) `s_κ ≤ Im m/|m|` and `κ' ≤ |(m/|m|)² - 1| = 2 Im m/|m|`;
  (b) `(C₀+1)⁻¹ ≤ |m| < 1`, `c_m ≤ Im m`;
  (c) `η|m| ≤ 1 - |m|² ≤ η/s_κ`, and `η/(C₀+1) ≤ 1 - |m|²`.
* `semicircleM_vsScale`: for `Im z ≠ 0` and `t ∈ (0,1]`,
  `semicircleM ((z + (1-t) m)/√t) = √t m`; proved for every nonreal `z`, in particular for
  `z ∈ 𝒟`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Kernel

open BlockBand.External.ErdosRiabov
open scoped ComplexConjugate

/-!
## Bulk constants
-/

/-- `s_κ = ½ √(κ̂(4-κ̂))`, `κ̂ = min κ 2`: the lower bound for `sin θ`, `m = ρ e^{iθ}`. -/
def bulkSin (κ : ℝ) : ℝ := Real.sqrt (min κ 2 * (4 - min κ 2)) / 2

/-- The phase constant `κ' = min κ 1`. -/
def phaseConst (κ : ℝ) : ℝ := min κ 1

/-- `c_m = s_κ/(C₀+1)`, the lower bound for `Im m`. -/
def imLower (κ C₀ : ℝ) : ℝ := bulkSin κ / (C₀ + 1)

theorem bulkSin_nonneg (κ : ℝ) : 0 ≤ bulkSin κ :=
  div_nonneg (Real.sqrt_nonneg _) zero_le_two

/-- For `0 < κ ≤ 2`, `bulkSin κ = √(κ(4-κ))/2 > 0`. -/
theorem bulkSin_eq {κ : ℝ} (hκ2 : κ ≤ 2) : bulkSin κ = Real.sqrt (κ * (4 - κ)) / 2 := by
  unfold bulkSin
  rw [min_eq_left hκ2]

theorem bulkSin_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < bulkSin κ := by
  rw [bulkSin_eq hκ2]
  have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  positivity

/-- The terminal bulk domain `𝒟 = {|e| ≤ 2-κ, η ≥ N^{-1+δ₀}, |z| ≤ C₀}`. -/
def BulkDomain (N : ℕ) (δ₀ κ C₀ : ℝ) (z : ℂ) : Prop :=
  |z.re| ≤ 2 - κ ∧ (N : ℝ) ^ (-1 + δ₀) ≤ z.im ∧ ‖z‖ ≤ C₀

theorem BulkDomain.im_pos {N : ℕ} {δ₀ κ C₀ : ℝ} {z : ℂ} (hz : BulkDomain N δ₀ κ C₀ z)
    (hN : 0 < N) : 0 < z.im :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hz.2.1

/-!
## Algebra of a root of `μ² + zμ + 1 = 0`
-/

theorem ne_zero_of_root {z m : ℂ} (hroot : m ^ 2 + z * m + 1 = 0) : m ≠ 0 := by
  rintro rfl
  norm_num at hroot

/-- Imaginary part of `z = -m - 1/m`: `Im z |m|² = Im m (1 - |m|²)`. -/
theorem im_identity_of_root {z m : ℂ} (hroot : m ^ 2 + z * m + 1 = 0) :
    z.im * ‖m‖ ^ 2 = m.im * (1 - ‖m‖ ^ 2) := by
  have hm := ne_zero_of_root hroot
  have hz : z = -(m + m⁻¹) := by
    apply mul_right_cancel₀ hm
    field_simp
    linear_combination hroot
  have hns : Complex.normSq m ≠ 0 := (Complex.normSq_pos.mpr hm).ne'
  rw [Complex.sq_norm, hz]
  simp only [Complex.neg_im, Complex.add_im, Complex.inv_im]
  field_simp
  ring

/-- Real part of `z = -m - 1/m`: `Re z |m|² = -Re m (|m|² + 1)`. -/
theorem re_identity_of_root {z m : ℂ} (hroot : m ^ 2 + z * m + 1 = 0) :
    z.re * ‖m‖ ^ 2 = -(m.re * (‖m‖ ^ 2 + 1)) := by
  have hm := ne_zero_of_root hroot
  have hz : z = -(m + m⁻¹) := by
    apply mul_right_cancel₀ hm
    field_simp
    linear_combination hroot
  have hns : Complex.normSq m ≠ 0 := (Complex.normSq_pos.mpr hm).ne'
  rw [Complex.sq_norm, hz]
  simp only [Complex.neg_re, Complex.add_re, Complex.inv_re]
  field_simp

/-- If `Im z ≠ 0`, no root of `μ² + zμ + 1 = 0` lies on the unit circle. -/
theorem norm_ne_one_of_root {z ν : ℂ} (hz : z.im ≠ 0) (hroot : ν ^ 2 + z * ν + 1 = 0) :
    ‖ν‖ ≠ 1 := by
  intro h1
  have h := im_identity_of_root hroot
  rw [h1] at h
  norm_num at h
  exact hz h

/-- **Uniqueness of the root**: the branch `semicircleM` is the unique root of modulus
`< 1` of `ν² + wν + 1 = 0` whenever `Im w ≠ 0`. -/
theorem semicircleM_eq_of_root {w ν : ℂ} (hw : w.im ≠ 0) (hν : ‖ν‖ < 1)
    (hroot : ν ^ 2 + w * ν + 1 = 0) : semicircleM w = ν := by
  have hm := semicircleM_dyson w
  have hm1 := norm_semicircleM_lt_one hw
  set m := semicircleM w with hmdef
  by_contra hne
  have hfac : (ν - m) * (ν + m + w) = 0 := by linear_combination hroot - hm
  have hsum : ν + m + w = 0 :=
    (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  have hprod : m * ν = 1 := by
    have hν' : ν = -m - w := by linear_combination hsum
    rw [hν']
    linear_combination -hm
  have hlt : ‖m * ν‖ < 1 := by
    rw [norm_mul]
    calc ‖m‖ * ‖ν‖ ≤ ‖ν‖ := mul_le_of_le_one_left (norm_nonneg ν) hm1.le
      _ < 1 := hν
  rw [hprod, norm_one] at hlt
  exact lt_irrefl _ hlt

/-!
## Phase and size of `m` in the bulk
-/

/-- `|(m/|m|)² - 1| = 2|Im m|/|m|` for `m ≠ 0` (`u² - 1 = u(u - ū)` for `|u| = 1`). -/
theorem norm_unit_sq_sub_one {m : ℂ} (hm : m ≠ 0) :
    ‖(m / (‖m‖ : ℂ)) ^ 2 - 1‖ = 2 * |m.im| / ‖m‖ := by
  have hn : 0 < ‖m‖ := norm_pos_iff.mpr hm
  set u : ℂ := m / (‖m‖ : ℂ) with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, div_self hn.ne']
  have huc : u * conj u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hun]
    norm_num
  have hfac : u ^ 2 - 1 = u * (u - conj u) := by
    rw [mul_sub, huc]
    ring
  rw [hfac, norm_mul, hun, one_mul, Complex.sub_conj, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, hu, Complex.div_ofReal_im, abs_mul, abs_div,
    abs_of_pos hn]
  norm_num
  ring

theorem semicircleM_im_pos {z : ℂ} (hη : 0 < z.im) : 0 < (semicircleM z).im := by
  have h := semicircleM_same_sign hη.ne'
  exact pos_of_mul_pos_left h hη.le

/-- **(a), sine bound**: `s_κ ≤ Im m/|m|` for `|Re z| ≤ 2 - κ`, `Im z > 0`. -/
theorem semicircleM_sin_ge {κ : ℝ} {z : ℂ} (he : |z.re| ≤ 2 - κ)
    (hη : 0 < z.im) : bulkSin κ ≤ (semicircleM z).im / ‖semicircleM z‖ := by
  have hroot := semicircleM_dyson z
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hy := semicircleM_im_pos hη
  have hre := re_identity_of_root hroot
  set m := semicircleM z with hmdef
  have hn : 0 < ‖m‖ := norm_pos_iff.mpr (ne_zero_of_root hroot)
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg z.re]
  set n := ‖m‖ with hndef
  have hxy : n ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    rw [hndef, Complex.sq_norm, Complex.normSq_apply]
    ring
  -- `|Re m| ≤ (1 - κ/2) n`
  have habs : |m.re| * (n ^ 2 + 1) = |z.re| * n ^ 2 := by
    have := congrArg abs hre
    rw [abs_mul, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n ^ 2 + 1),
      abs_of_pos (by positivity : (0 : ℝ) < n ^ 2)] at this
    linarith
  have hamgm : 2 * n ≤ n ^ 2 + 1 := by nlinarith [sq_nonneg (n - 1)]
  have hx : |m.re| ≤ (1 - κ / 2) * n := by
    have h1 : |m.re| * (2 * n) ≤ (2 - κ) * n ^ 2 := by
      calc |m.re| * (2 * n) ≤ |m.re| * (n ^ 2 + 1) :=
            mul_le_mul_of_nonneg_left hamgm (abs_nonneg _)
        _ = |z.re| * n ^ 2 := habs
        _ ≤ (2 - κ) * n ^ 2 := mul_le_mul_of_nonneg_right he (by positivity)
    nlinarith
  have hx2 : m.re ^ 2 ≤ ((1 - κ / 2) * n) ^ 2 := by
    rw [← sq_abs m.re]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 : κ * (4 - κ) * n ^ 2 ≤ 4 * m.im ^ 2 := by nlinarith
  rw [bulkSin_eq hκ2, div_le_div_iff₀ two_pos hn]
  have hrhs : 0 ≤ m.im * 2 := by linarith
  have hsq : Real.sqrt (κ * (4 - κ)) * n = Real.sqrt (κ * (4 - κ) * n ^ 2) := by
    rw [Real.sqrt_mul' _ (sq_nonneg n), Real.sqrt_sq hn.le]
  rw [hsq, Real.sqrt_le_left hrhs]
  nlinarith

/-- **(a), phase separation**: `κ' ≤ |(m/|m|)² - 1| = 2 Im m/|m|`. -/
theorem semicircleM_phase_ge {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (he : |z.re| ≤ 2 - κ)
    (hη : 0 < z.im) :
    phaseConst κ ≤ ‖(semicircleM z / (‖semicircleM z‖ : ℂ)) ^ 2 - 1‖ := by
  have hroot := semicircleM_dyson z
  have hs := semicircleM_sin_ge he hη
  have hy := semicircleM_im_pos hη
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg z.re]
  rw [norm_unit_sq_sub_one (ne_zero_of_root hroot), abs_of_pos hy, mul_div_assoc]
  have hk : κ ≤ 2 * bulkSin κ := by
    rw [bulkSin_eq hκ2]
    have : κ = Real.sqrt (κ ^ 2) := (Real.sqrt_sq hκ.le).symm
    rw [mul_div_cancel₀ _ two_ne_zero]
    calc κ = Real.sqrt (κ ^ 2) := this
      _ ≤ Real.sqrt (κ * (4 - κ)) := Real.sqrt_le_sqrt (by nlinarith)
  unfold phaseConst
  calc min κ 1 ≤ κ := min_le_left _ _
    _ ≤ 2 * bulkSin κ := hk
    _ ≤ 2 * ((semicircleM z).im / ‖semicircleM z‖) := by linarith

/-- **(b), modulus**: `(C₀+1)⁻¹ ≤ |m|` when `‖z‖ ≤ C₀` and `Im z ≠ 0`. -/
theorem semicircleM_norm_ge {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {z : ℂ} (hz : z.im ≠ 0)
    (hzC : ‖z‖ ≤ C₀) : (C₀ + 1)⁻¹ ≤ ‖semicircleM z‖ := by
  have hroot := semicircleM_dyson z
  have hm1 := norm_semicircleM_lt_one hz
  set m := semicircleM z
  have hprod : m * (z + m) = -1 := by linear_combination hroot
  have hnorm : ‖m‖ * ‖z + m‖ = 1 := by
    rw [← norm_mul, hprod, norm_neg, norm_one]
  have hzm : ‖z + m‖ ≤ C₀ + 1 := (norm_add_le _ _).trans (by linarith)
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  calc (1 : ℝ) = ‖m‖ * ‖z + m‖ := hnorm.symm
    _ ≤ ‖m‖ * (C₀ + 1) := mul_le_mul_of_nonneg_left hzm (norm_nonneg _)

/-- **(b), imaginary part**: `c_m ≤ Im m`. -/
theorem semicircleM_im_ge {κ C₀ : ℝ} (hC₀ : 0 ≤ C₀) {z : ℂ}
    (he : |z.re| ≤ 2 - κ) (hη : 0 < z.im) (hzC : ‖z‖ ≤ C₀) :
    imLower κ C₀ ≤ (semicircleM z).im := by
  have hs := semicircleM_sin_ge he hη
  have hn := semicircleM_norm_ge hC₀ hη.ne' hzC
  have hroot := semicircleM_dyson z
  have hpos : 0 < ‖semicircleM z‖ := norm_pos_iff.mpr (ne_zero_of_root hroot)
  have hsplit : (semicircleM z).im =
      ‖semicircleM z‖ * ((semicircleM z).im / ‖semicircleM z‖) := by
    field_simp
  rw [hsplit, imLower, div_eq_mul_inv, mul_comm (bulkSin κ)]
  exact mul_le_mul hn hs (bulkSin_nonneg κ) hpos.le

/-- **(c)**: `η|m| ≤ 1 - |m|² ≤ η/s_κ`. -/
theorem semicircleM_one_sub_sq {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (he : |z.re| ≤ 2 - κ)
    (hη : 0 < z.im) :
    z.im * ‖semicircleM z‖ ≤ 1 - ‖semicircleM z‖ ^ 2 ∧
      1 - ‖semicircleM z‖ ^ 2 ≤ z.im / bulkSin κ := by
  have hroot := semicircleM_dyson z
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hy := semicircleM_im_pos hη
  have hs := semicircleM_sin_ge he hη
  have hid := im_identity_of_root hroot
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg z.re]
  have hsp := bulkSin_pos hκ hκ2
  set m := semicircleM z
  have hn : 0 < ‖m‖ := norm_pos_iff.mpr (ne_zero_of_root hroot)
  have hyn : m.im ≤ ‖m‖ := (le_abs_self _).trans (Complex.abs_im_le_norm m)
  have hsn : bulkSin κ * ‖m‖ ≤ m.im := by rwa [le_div_iff₀ hn] at hs
  constructor
  · -- `(1 - n² - η n) y = η n (n - y) ≥ 0`
    have h : (1 - ‖m‖ ^ 2 - z.im * ‖m‖) * m.im = z.im * ‖m‖ * (‖m‖ - m.im) := by
      linear_combination -hid
    have h0 : 0 ≤ (1 - ‖m‖ ^ 2 - z.im * ‖m‖) * m.im := by
      rw [h]
      exact mul_nonneg (mul_nonneg hη.le hn.le) (by linarith)
    have := nonneg_of_mul_nonneg_left h0 hy
    linarith
  · rw [le_div_iff₀ hsp]
    have h1 : 0 ≤ 1 - ‖m‖ ^ 2 := by nlinarith
    have h2 : (1 - ‖m‖ ^ 2) * (bulkSin κ * ‖m‖) ≤ z.im * ‖m‖ := by
      calc (1 - ‖m‖ ^ 2) * (bulkSin κ * ‖m‖) ≤ (1 - ‖m‖ ^ 2) * m.im :=
            mul_le_mul_of_nonneg_left hsn h1
        _ = z.im * ‖m‖ ^ 2 := by linarith
        _ ≤ z.im * ‖m‖ := by
            rw [pow_two, ← mul_assoc]
            exact mul_le_of_le_one_right (mul_nonneg hη.le hn.le) hm1.le
    have h3 : (1 - ‖m‖ ^ 2) * bulkSin κ * ‖m‖ ≤ z.im * ‖m‖ := by linarith
    exact le_of_mul_le_mul_right h3 hn

/-- **The phase lemma** (a)-(c). For `0 < κ`, `|Re z| ≤ 2 - κ`,
`Im z > 0`, with `m = semicircleM z`: `Im m > 0`, `|m| < 1`, (a) `s_κ ≤ Im m/|m|` and
`κ' ≤ |(m/|m|)² - 1| = 2 Im m/|m|`; (c) `η|m| ≤ 1 - |m|² ≤ η/s_κ`. If moreover `‖z‖ ≤ C₀`
(`C₀ ≥ 0`): (b) `(C₀+1)⁻¹ ≤ |m|`, `c_m ≤ Im m`, and (c) `η/(C₀+1) ≤ 1 - |m|²`. -/
theorem semicircleM_phase {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (he : |z.re| ≤ 2 - κ)
    (hη : 0 < z.im) :
    0 < (semicircleM z).im ∧ ‖semicircleM z‖ < 1 ∧
      bulkSin κ ≤ (semicircleM z).im / ‖semicircleM z‖ ∧
      ‖(semicircleM z / (‖semicircleM z‖ : ℂ)) ^ 2 - 1‖ =
        2 * ((semicircleM z).im / ‖semicircleM z‖) ∧
      phaseConst κ ≤ ‖(semicircleM z / (‖semicircleM z‖ : ℂ)) ^ 2 - 1‖ ∧
      z.im * ‖semicircleM z‖ ≤ 1 - ‖semicircleM z‖ ^ 2 ∧
      1 - ‖semicircleM z‖ ^ 2 ≤ z.im / bulkSin κ ∧
      ∀ C₀ : ℝ, 0 ≤ C₀ → ‖z‖ ≤ C₀ →
        (C₀ + 1)⁻¹ ≤ ‖semicircleM z‖ ∧ imLower κ C₀ ≤ (semicircleM z).im ∧
          z.im / (C₀ + 1) ≤ 1 - ‖semicircleM z‖ ^ 2 := by
  have hroot := semicircleM_dyson z
  have hy := semicircleM_im_pos hη
  have hc := semicircleM_one_sub_sq hκ he hη
  refine ⟨hy, norm_semicircleM_lt_one hη.ne', semicircleM_sin_ge he hη, ?_,
    semicircleM_phase_ge hκ he hη, hc.1, hc.2, fun C₀ hC₀ hzC => ?_⟩
  · rw [norm_unit_sq_sub_one (ne_zero_of_root hroot), abs_of_pos hy, mul_div_assoc]
  · have hn := semicircleM_norm_ge hC₀ hη.ne' hzC
    refine ⟨hn, semicircleM_im_ge hC₀ he hη hzC, ?_⟩
    calc z.im / (C₀ + 1) = z.im * (C₀ + 1)⁻¹ := div_eq_mul_inv _ _
      _ ≤ z.im * ‖semicircleM z‖ := mul_le_mul_of_nonneg_left hn hη.le
      _ ≤ _ := hc.1

/-!
## The variance-scaling rescaling
-/

/-- Imaginary part of the rescaled VS point `w_t = (z + (1-t)m)/√t`. -/
theorem vsScale_im (z : ℂ) (t : ℝ) :
    ((z + (1 - (t : ℂ)) * semicircleM z) / (Real.sqrt t : ℂ)).im =
      (z.im + (1 - t) * (semicircleM z).im) / Real.sqrt t := by
  rw [Complex.div_ofReal_im]
  congr 1
  simp

/-- **Rescaling identity**: for every nonreal `z`
and `t ∈ (0,1]`, with `m = semicircleM z`, `semicircleM ((z + (1-t)m)/√t) = √t m`. -/
theorem semicircleM_vsScale {z : ℂ} (hz : z.im ≠ 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    semicircleM ((z + (1 - (t : ℂ)) * semicircleM z) / (Real.sqrt t : ℂ)) =
      (Real.sqrt t : ℂ) * semicircleM z := by
  have hm := semicircleM_dyson z
  have hm1 := norm_semicircleM_lt_one hz
  have hsign := semicircleM_same_sign hz
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
  apply semicircleM_eq_of_root
  · rw [vsScale_im]
    apply div_ne_zero _ hst.ne'
    intro h0
    have h1 : (z.im + (1 - t) * (semicircleM z).im) * z.im = 0 := by rw [h0, zero_mul]
    have h2 : 0 < (z.im + (1 - t) * (semicircleM z).im) * z.im := by
      have hz2 : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz
      nlinarith
    linarith
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hst]
    calc Real.sqrt t * ‖semicircleM z‖ ≤ ‖semicircleM z‖ :=
          mul_le_of_le_one_left (norm_nonneg _) hst1
      _ < 1 := hm1
  · set m := semicircleM z
    have hs2 : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = (t : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt ht0.le]
    have hs0 : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hst.ne'
    have hmul : (z + (1 - (t : ℂ)) * m) / ((Real.sqrt t : ℝ) : ℂ) *
        (((Real.sqrt t : ℝ) : ℂ) * m) = (z + (1 - (t : ℂ)) * m) * m := by
      field_simp
    rw [hmul, mul_pow, hs2]
    linear_combination hm

end BlockBand.Native.ErdosRiabov.Kernel
