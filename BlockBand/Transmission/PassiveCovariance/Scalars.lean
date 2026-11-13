module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# Scalar facts for the passive covariance

Elementary identities and bounds for the jet scalars `a`, `η`, `k₋`, `c₀`, `σ₊` on the bulk:

* `|a| = 1`, `Im a < 0`, `a⁻¹ = ā`;
* `η = Im z_∂ = -(1-b) Im a > 0`;
* `|k₋| < (1-b)²` (strict, since `a² ≠ 1` in the bulk), `k₋ = c + b²a²`;
* `c₀ = (2iη)⁻¹` has `conj c₀ = -c₀` and `c₀² = -1/(4η²)`;
* `σ₊ = 2η²D₀`, i.e. `σ₊/(2η²) = D₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexConjugate

theorem matchedA_re (E : ℝ) : (matchedA E).re = -E / 2 := rfl

theorem matchedA_im (E : ℝ) : (matchedA E).im = -Real.sqrt (4 - E ^ 2) / 2 := rfl

theorem sqrt_four_sub_sq (E : ℝ) (h1 : -2 < E) (h2 : E < 2) :
    Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 :=
  Real.sq_sqrt (by nlinarith)

theorem sqrt_four_sub_pos (E : ℝ) (h1 : -2 < E) (h2 : E < 2) : 0 < Real.sqrt (4 - E ^ 2) :=
  Real.sqrt_pos.mpr (by nlinarith)

theorem matchedA_im_neg (E : ℝ) (h1 : -2 < E) (h2 : E < 2) : (matchedA E).im < 0 := by
  rw [matchedA_im]; have := sqrt_four_sub_pos E h1 h2; linarith

/-- `|a|² = 1`. -/
theorem normSq_matchedA (E : ℝ) (h1 : -2 < E) (h2 : E < 2) : Complex.normSq (matchedA E) = 1 := by
  rw [Complex.normSq_apply, matchedA_re, matchedA_im]
  have := sqrt_four_sub_sq E h1 h2
  nlinarith

theorem norm_matchedA (E : ℝ) (h1 : -2 < E) (h2 : E < 2) : ‖matchedA E‖ = 1 := by
  rw [Complex.norm_def, normSq_matchedA E h1 h2, Real.sqrt_one]

theorem matchedA_ne_zero (E : ℝ) (h1 : -2 < E) (h2 : E < 2) : matchedA E ≠ 0 := by
  intro h; have := norm_matchedA E h1 h2; rw [h, norm_zero] at this; exact zero_ne_one this

theorem matchedA_mul_conj (E : ℝ) (h1 : -2 < E) (h2 : E < 2) :
    matchedA E * conj (matchedA E) = 1 := by
  rw [Complex.mul_conj, normSq_matchedA E h1 h2, Complex.ofReal_one]

theorem matchedA_inv (E : ℝ) (h1 : -2 < E) (h2 : E < 2) : (matchedA E)⁻¹ = conj (matchedA E) :=
  inv_eq_of_mul_eq_one_right (matchedA_mul_conj E h1 h2)

/-- `η = Im z_∂ = -(1-b) Im a`. -/
theorem etaZ_eq (b E : ℝ) (h1 : -2 < E) (h2 : E < 2) :
    etaZ b E = -(1 - b) * (matchedA E).im := by
  rw [etaZ, boundaryZ, matchedA_inv E h1 h2]
  simp only [Complex.add_im, Complex.conj_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  ring

theorem etaZ_pos (b E : ℝ) (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) : 0 < etaZ b E := by
  rw [etaZ_eq b E h1 h2]
  have := matchedA_im_neg E h1 h2
  nlinarith

/-- `|k₋|² = (c+b²)² - 4cb²(Im a)²`, `c = 1-2b`. -/
theorem normSq_kMinus (b E : ℝ) (h1 : -2 < E) (h2 : E < 2) :
    Complex.normSq (kMinus b E) =
      ((1 - 2 * b) + b ^ 2) ^ 2 - 4 * (1 - 2 * b) * b ^ 2 * (matchedA E).im ^ 2 := by
  have hn := normSq_matchedA E h1 h2
  rw [Complex.normSq_apply] at hn
  set x := (matchedA E).re
  set y := (matchedA E).im
  have hre : (kMinus b E).re = (1 - 2 * b) + b ^ 2 * (x ^ 2 - y ^ 2) := by
    simp only [kMinus, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      pow_two, Complex.ofReal_im, x, y]
    ring
  have him : (kMinus b E).im = b ^ 2 * (2 * x * y) := by
    simp only [kMinus, Complex.add_im, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      pow_two, Complex.ofReal_im, x, y]
    ring
  rw [Complex.normSq_apply, hre, him]
  linear_combination (2 * (1 - 2 * b) * b ^ 2 + b ^ 4 * (x ^ 2 + y ^ 2 + 1)) * hn

/-- `|k₋| < (1-b)²` strictly in the bulk. -/
theorem norm_kMinus_lt (b E : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ‖kMinus b E‖ < (1 - b) ^ 2 := by
  have hy := matchedA_im_neg E h1 h2
  have hsq : ‖kMinus b E‖ ^ 2 < ((1 - b) ^ 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_kMinus b E h1 h2]
    have : 0 < 4 * (1 - 2 * b) * b ^ 2 * (matchedA E).im ^ 2 := by
      have h3 : 0 < (matchedA E).im ^ 2 := by nlinarith
      have h4 : 0 < 1 - 2 * b := by linarith
      have h5 : 0 < b ^ 2 := by positivity
      have := mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) h4) h5) h3
      linarith
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

/-- `c₀ = (2iη)⁻¹` is purely imaginary. -/
theorem conj_cZero (b E : ℝ) : conj (cZero b E) = -cZero b E := by
  rw [cZero, map_inv₀, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [map_ofNat]
  rw [← inv_neg]; ring_nf

/-- `c₀² = -1/(4η²)`. -/
theorem cZero_sq (b E : ℝ) (hη : etaZ b E ≠ 0) :
    cZero b E ^ 2 = -((4 * (etaZ b E) ^ 2 : ℝ) : ℂ)⁻¹ := by
  have hη' : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hη
  rw [cZero]
  push_cast
  field_simp
  rw [Complex.I_sq]
  norm_num

/-- `σ₊ = 2η²D₀`, from `η = (1-b)√(4-E²)/2`. -/
theorem sigmaPlus_eq (b E : ℝ) (hb0 : 0 < b) (h1 : -2 < E) (h2 : E < 2) :
    sigmaPlus b = 2 * etaZ b E ^ 2 * transportD0 b E := by
  rw [sigmaPlus, kPlus, transportD0, etaZ_eq b E h1 h2, matchedA_im]
  have hs := sqrt_four_sub_sq E h1 h2
  have h4 : 4 - E ^ 2 ≠ 0 := by nlinarith
  field_simp
  rw [hs]
  ring

end BlockBand.Transmission.PassiveCovariance
