module

public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Native.CEH.Phase1.Resolvent

/-!
# CEH, Phase 1: the MDE solution and the characteristic

Elementary properties of a solution `M` of the MDE `IsManuscriptMDE s F z M`, `m = ⟨M⟩`, and of
the characteristic `z_t = z + s (1 - t) m` along which `M` stays a solution.

* The solution: `M = (F - ζ)⁻¹` with `ζ = z + s m`; `Im z · Im m ≥ 0` (strict for `N > 0`);
  for `s ≥ 0`, `|Im ζ| = |Im z| + s |Im m|` and `Im ζ` has the sign of `Im z`; the Ward identity
  `Im M = (Im ζ) M Mᴴ`; `|Im m| = π ρ` with `ρ = sourceDensity M`; `⟨Im M⟩ = Im m` and the
  formula for `gammaMatrix M`.
* The characteristic: `z_t + s t m = z + s m`, hence `(F - (z_t + s t m))⁻¹ = M` and
  `IsManuscriptMDE (s t) F z_t M` for `t ≤ 1`; `η_t := |Im z_t| = |Im z| + s π ρ (1 - t)`,
  affine and antitone in `t`, with `η_1 = |Im z|` and `N η_t ρ ≥ N |Im z| ρ`.

Hypotheses are only `s ≥ 0`, `Im z ≠ 0` (where needed) and `t ≤ 1`; no `N > 0` unless stated.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.Phase1

open Matrix
open BlockBand.External.CEH
open BlockBand.Internal.Contracts.Inputs (IsManuscriptMDE)
open scoped ComplexOrder

variable {N : ℕ} {s : ℝ} {F : SourceHermitian N} {z : ℂ} {M : SourceMatrix N}

/-!
## The MDE solution
-/

/-- Real-scalar imaginary part: `Im (z + c m) = Im z + c Im m`. -/
theorem im_add_ofReal_mul (z m : ℂ) (c : ℝ) : (z + (c : ℂ) * m).im = z.im + c * m.im := by
  simp

theorem mde_isUnit_det (h : IsManuscriptMDE s F z M) :
    IsUnit (F.1 - (z + (s : ℂ) * normalizedTrace M) • (1 : SourceMatrix N)).det :=
  isUnit_det_of_right_inverse h.1

/-- `M = (F - ζ)⁻¹`, `ζ = z + s m`. No condition on `z` or `s` is needed. -/
theorem mde_eq_resolvent (h : IsManuscriptMDE s F z M) :
    M = resolvent F.1 (z + (s : ℂ) * normalizedTrace M) :=
  (inv_eq_right_inv h.1).symm

theorem mde_mul_left (h : IsManuscriptMDE s F z M) :
    M * (F.1 - (z + (s : ℂ) * normalizedTrace M) • (1 : SourceMatrix N)) = 1 := by
  have := nonsing_inv_mul _ (mde_isUnit_det h)
  rwa [inv_eq_right_inv h.1] at this

/-- `⟨Im M⟩ = Im m`. -/
theorem mde_normalizedTrace_imaginaryPart (M : SourceMatrix N) :
    normalizedTrace (External.CEH.imaginaryPart M) = (((normalizedTrace M).im : ℝ) : ℂ) :=
  normalizedTrace_imaginaryPart M

/-- `Im z · Im m ≥ 0`, from `(Im z) Im M ≻ 0`. -/
theorem mde_im_mul_im_nonneg (h : IsManuscriptMDE s F z M) :
    0 ≤ z.im * (normalizedTrace M).im := by
  have htr := h.2.posSemidef.trace_nonneg
  have hre : 0 ≤ (((z.im : ℂ) • External.CEH.imaginaryPart M).trace).re :=
    (Complex.nonneg_iff.mp htr).1
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have := mul_nonneg hN hre
  rwa [← re_normalizedTrace, normalizedTrace_smul, mde_normalizedTrace_imaginaryPart,
    ← Complex.ofReal_mul, Complex.ofReal_re] at this

/-- Strict version for `N > 0`: `Im z · Im m > 0`. -/
theorem mde_im_mul_im_pos (hN : 0 < N) (h : IsManuscriptMDE s F z M) :
    0 < z.im * (normalizedTrace M).im := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have htr := h.2.trace_pos
  have hre : 0 < (((z.im : ℂ) • External.CEH.imaginaryPart M).trace).re :=
    (Complex.pos_iff.mp htr).1
  have hN' : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
  have := mul_pos hN' hre
  rwa [← re_normalizedTrace, normalizedTrace_smul, mde_normalizedTrace_imaginaryPart,
    ← Complex.ofReal_mul, Complex.ofReal_re] at this

/-- For `c ≥ 0`: `|Im (z + c m)| = |Im z| + c |Im m|`. -/
theorem mde_abs_im_add (h : IsManuscriptMDE s F z M) {c : ℝ} (hc : 0 ≤ c) :
    |(z + (c : ℂ) * normalizedTrace M).im| = |z.im| + c * |(normalizedTrace M).im| := by
  rw [im_add_ofReal_mul]
  set a := z.im
  set b := (normalizedTrace M).im
  have hab : |a| * |b| = a * b := by rw [← abs_mul, abs_of_nonneg (mde_im_mul_im_nonneg h)]
  rw [← sq_eq_sq₀ (abs_nonneg _) (by positivity), sq_abs]
  linear_combination (-1 : ℝ) * sq_abs a + (-2 * c) * hab + (-c ^ 2) * sq_abs b

/-- For `c ≥ 0` and `Im z ≠ 0`: `Im (z + c m)` has the sign of `Im z`. -/
theorem mde_im_mul_im_add_pos (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) {c : ℝ}
    (hc : 0 ≤ c) : 0 < z.im * (z + (c : ℂ) * normalizedTrace M).im := by
  rw [im_add_ofReal_mul]
  have h1 := mde_im_mul_im_nonneg h
  have h2 : 0 < z.im * z.im := mul_self_pos.mpr hz
  nlinarith [mul_nonneg hc h1]

theorem mde_im_add_ne (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    (z + (c : ℂ) * normalizedTrace M).im ≠ 0 := by
  intro h0
  have := mde_im_mul_im_add_pos h hz hc
  rw [h0, mul_zero] at this
  exact lt_irrefl _ this

/-- `|Im ζ| = |Im z| + s |Im m|`, `ζ = z + s m`. -/
theorem mde_abs_im_spectral (h : IsManuscriptMDE s F z M) (hs : 0 ≤ s) :
    |(z + (s : ℂ) * normalizedTrace M).im| = |z.im| + s * |(normalizedTrace M).im| :=
  mde_abs_im_add h hs

/-- `Im ζ` has the sign of `Im z`. -/
theorem mde_im_mul_im_spectral_pos (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0)
    (hs : 0 ≤ s) : 0 < z.im * (z + (s : ℂ) * normalizedTrace M).im :=
  mde_im_mul_im_add_pos h hz hs

theorem mde_im_spectral_ne (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) (hs : 0 ≤ s) :
    (z + (s : ℂ) * normalizedTrace M).im ≠ 0 :=
  mde_im_add_ne h hz hs

/-- Ward identity for the MDE solution: `Im M = (Im ζ) M Mᴴ`. -/
theorem mde_imaginaryPart_eq (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) (hs : 0 ≤ s) :
    External.CEH.imaginaryPart M =
      ((z + (s : ℂ) * normalizedTrace M).im : ℂ) • (M * Mᴴ) := by
  have hM := mde_eq_resolvent h
  have hζ := mde_im_spectral_ne h hz hs
  conv_lhs => rw [hM]
  rw [imaginaryPart_resolvent F.2 hζ, ← hM]

/-- Ward identity for the MDE solution: `Im M = (Im ζ) Mᴴ M`. -/
theorem mde_imaginaryPart_eq' (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) (hs : 0 ≤ s) :
    External.CEH.imaginaryPart M =
      ((z + (s : ℂ) * normalizedTrace M).im : ℂ) • (Mᴴ * M) := by
  have hM := mde_eq_resolvent h
  have hζ := mde_im_spectral_ne h hz hs
  conv_lhs => rw [hM]
  rw [imaginaryPart_resolvent' F.2 hζ, ← hM]

/-- `|Im m| = π ρ`, `ρ = sourceDensity M` (definition of the source density). -/
theorem abs_im_normalizedTrace_eq_pi_mul_sourceDensity (M : SourceMatrix N) :
    |(normalizedTrace M).im| = Real.pi * sourceDensity M := by
  rw [sourceDensity]
  field_simp

theorem sourceDensity_eq (M : SourceMatrix N) :
    sourceDensity M = |(normalizedTrace M).im| / Real.pi := rfl

/-- `|Im ζ| = |Im z| + s π ρ`. -/
theorem mde_abs_im_spectral_eq_density (h : IsManuscriptMDE s F z M) (hs : 0 ≤ s) :
    |(z + (s : ℂ) * normalizedTrace M).im| = |z.im| + s * Real.pi * sourceDensity M := by
  rw [mde_abs_im_spectral h hs, abs_im_normalizedTrace_eq_pi_mul_sourceDensity, mul_assoc]

/-- `Γ = (Im m)⁻¹ Im M`. -/
theorem gammaMatrix_eq (M : SourceMatrix N) :
    gammaMatrix M = (((normalizedTrace M).im : ℝ) : ℂ)⁻¹ • External.CEH.imaginaryPart M := by
  rw [gammaMatrix, mde_normalizedTrace_imaginaryPart]

/-- `Γ = (Im ζ / Im m) M Mᴴ`. -/
theorem mde_gammaMatrix_eq (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) (hs : 0 ≤ s) :
    gammaMatrix M = ((((z + (s : ℂ) * normalizedTrace M).im / (normalizedTrace M).im : ℝ)) :
      ℂ) • (M * Mᴴ) := by
  rw [gammaMatrix_eq, mde_imaginaryPart_eq h hz hs, smul_smul]
  congr 1
  push_cast
  ring

/-!
## The characteristic
-/

/-- The characteristic `z_t = z + s (1 - t) m`. -/
def characteristicPoint (s : ℝ) (z m : ℂ) (t : ℝ) : ℂ :=
  z + ((s * (1 - t) : ℝ) : ℂ) * m

theorem characteristicPoint_one (s : ℝ) (z m : ℂ) : characteristicPoint s z m 1 = z := by
  simp [characteristicPoint]

theorem characteristicPoint_zero (s : ℝ) (z m : ℂ) :
    characteristicPoint s z m 0 = z + (s : ℂ) * m := by
  simp [characteristicPoint]

/-- `z_t + s t m = z + s m`. -/
theorem characteristicPoint_add (s : ℝ) (z m : ℂ) (t : ℝ) :
    characteristicPoint s z m t + ((s * t : ℝ) : ℂ) * m = z + (s : ℂ) * m := by
  simp only [characteristicPoint]
  push_cast
  ring

/-- `F - (z_t + s t m) = F - (z + s m)`. -/
theorem characteristic_sub_smul (s : ℝ) (F : SourceHermitian N) (z m : ℂ) (t : ℝ) :
    F.1 - (characteristicPoint s z m t + ((s * t : ℝ) : ℂ) * m) • (1 : SourceMatrix N) =
      F.1 - (z + (s : ℂ) * m) • (1 : SourceMatrix N) := by
  rw [characteristicPoint_add]

/-- `(F - (z_t + s t m))⁻¹ = M`. -/
theorem characteristic_resolvent (h : IsManuscriptMDE s F z M) (t : ℝ) :
    resolvent F.1 (characteristicPoint s z (normalizedTrace M) t +
      ((s * t : ℝ) : ℂ) * normalizedTrace M) = M := by
  rw [characteristicPoint_add, ← mde_eq_resolvent h]

theorem characteristic_im (s : ℝ) (z m : ℂ) (t : ℝ) :
    (characteristicPoint s z m t).im = z.im + s * (1 - t) * m.im := by
  rw [characteristicPoint, im_add_ofReal_mul]

/-- `Im z_t` has the sign of `Im z` for `t ≤ 1`. -/
theorem characteristic_im_mul_pos (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) (hs : 0 ≤ s)
    {t : ℝ} (ht : t ≤ 1) : 0 < z.im * (characteristicPoint s z (normalizedTrace M) t).im :=
  mde_im_mul_im_add_pos h hz (mul_nonneg hs (sub_nonneg.mpr ht))

theorem characteristic_im_ne (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) (hs : 0 ≤ s)
    {t : ℝ} (ht : t ≤ 1) : (characteristicPoint s z (normalizedTrace M) t).im ≠ 0 :=
  mde_im_add_ne h hz (mul_nonneg hs (sub_nonneg.mpr ht))

/-- Along the characteristic, `M` solves the MDE with variance `s t` at `z_t`. -/
theorem characteristic_isManuscriptMDE (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0)
    (hs : 0 ≤ s) {t : ℝ} (ht : t ≤ 1) :
    IsManuscriptMDE (s * t) F (characteristicPoint s z (normalizedTrace M) t) M := by
  refine ⟨?_, ?_⟩
  · rw [characteristic_sub_smul]
    exact h.1
  · set q := (characteristicPoint s z (normalizedTrace M) t).im
    have hq : 0 < q / z.im := by
      have h1 := characteristic_im_mul_pos h hz hs ht
      have hz2 : 0 < z.im * z.im := mul_self_pos.mpr hz
      have : q / z.im = (z.im * q) / (z.im * z.im) := by field_simp
      rw [this]
      exact div_pos h1 hz2
    have he : (q : ℂ) • External.CEH.imaginaryPart M =
        (((q / z.im : ℝ)) : ℂ) • ((z.im : ℂ) • External.CEH.imaginaryPart M) := by
      rw [smul_smul]
      congr 1
      push_cast
      field_simp
    rw [he]
    refine h.2.smul ?_
    exact_mod_cast hq

/-- `η_t := |Im z_t| = |Im z| + s π ρ (1 - t)` for `t ≤ 1`. -/
theorem characteristic_abs_im (h : IsManuscriptMDE s F z M) (hs : 0 ≤ s) {t : ℝ}
    (ht : t ≤ 1) :
    |(characteristicPoint s z (normalizedTrace M) t).im| =
      |z.im| + s * Real.pi * sourceDensity M * (1 - t) := by
  rw [characteristicPoint, mde_abs_im_add h (mul_nonneg hs (sub_nonneg.mpr ht)),
    abs_im_normalizedTrace_eq_pi_mul_sourceDensity]
  ring

/-- `η_1 = |Im z|`. -/
theorem characteristic_abs_im_one (s : ℝ) (z m : ℂ) :
    |(characteristicPoint s z m 1).im| = |z.im| := by
  rw [characteristicPoint_one]

/-- `η_t ≥ |Im z|` for `t ≤ 1`. -/
theorem abs_im_le_characteristic_abs_im (h : IsManuscriptMDE s F z M) (hs : 0 ≤ s) {t : ℝ}
    (ht : t ≤ 1) : |z.im| ≤ |(characteristicPoint s z (normalizedTrace M) t).im| := by
  rw [characteristic_abs_im h hs ht]
  have := sourceDensity_nonneg M
  have := Real.pi_pos
  have : 0 ≤ s * Real.pi * sourceDensity M * (1 - t) := by
    have := sub_nonneg.mpr ht
    positivity
  linarith

/-- `t ↦ η_t` is antitone on `t ≤ 1`. -/
theorem characteristic_abs_im_antitone (h : IsManuscriptMDE s F z M) (hs : 0 ≤ s)
    {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) (ht₂ : t₂ ≤ 1) :
    |(characteristicPoint s z (normalizedTrace M) t₂).im| ≤
      |(characteristicPoint s z (normalizedTrace M) t₁).im| := by
  rw [characteristic_abs_im h hs ht₂, characteristic_abs_im h hs (h12.trans ht₂)]
  have : 0 ≤ s * Real.pi * sourceDensity M := by
    have := sourceDensity_nonneg M
    have := Real.pi_pos
    positivity
  nlinarith

/-- `N η_t ρ ≥ N |Im z| ρ` for `t ≤ 1`. -/
theorem characteristic_N_eta_rho_ge (h : IsManuscriptMDE s F z M) (hs : 0 ≤ s) {t : ℝ}
    (ht : t ≤ 1) :
    (N : ℝ) * |z.im| * sourceDensity M ≤
      (N : ℝ) * |(characteristicPoint s z (normalizedTrace M) t).im| * sourceDensity M := by
  have h1 := abs_im_le_characteristic_abs_im h hs ht
  have h2 := sourceDensity_nonneg M
  have h3 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  gcongr

end BlockBand.Native.CEH.Phase1
