module

public import BlockBand.Transmission.SourceMixing.MassMeanStrict

/-!
# Algebra of the refined (`Ω`-linear) mass mean

The crude mass mean `SourceMixing.massMean_strict` bounds every first-order `Ω = z - ζ` term by
`Cδ₀q`, which sums to `O(T)` over `TW` layers. The refined mean keeps the linear term
`2 Re(Ω Tr Qf)` (as in the passive cancelled-mean bound): the linear term from `1 - Im Ω/η`
cancels the `-c₀` in `f = R - c₀`. This file has the three pure algebra steps:
* `rf_re_s_two`: two-sided version of `SourceMixing.mm_re_s`;
* `rf_u_expand`: `u = Tr(MᴴYM) = q + 2Re(ωTr Qf) + q Im ω/η + O(|ω|²q)` from `KM = 1 + ωM`,
  `M = R·KM`;
* `rf_ratio`: `|N/A - q/B| ≤ |N - q| + q|A - B|` for `A, B ≥ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open Matrix
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Two-sided `Re s`: `|Re(s)D - cι| ≤ |ι|ε₂ + C_s|E₁|` from `|sL - c| ≤ ε₂`, `ιL = D + E₁`,
`|s| ≤ C_s`. -/
theorem rf_re_s_two {s : ℂ} {L D E₁ ι c ε₂ Cs : ℝ} (hsL : ‖s * L - c‖ ≤ ε₂)
    (hιL : ι * L = D + E₁) (hs : ‖s‖ ≤ Cs) :
    |s.re * D - c * ι| ≤ |ι| * ε₂ + Cs * |E₁| := by
  have e : s * D - c * ι = ι * (s * L - c) - s * E₁ := by
    have : (D : ℂ) = ι * L - E₁ := by exact_mod_cast (by linarith : D = ι * L - E₁)
    rw [this]; ring
  have hn : ‖s * D - c * ι‖ ≤ |ι| * ε₂ + Cs * |E₁| := by
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hsL (abs_nonneg _)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  have hre : (s * D - c * ι).re = s.re * D - c * ι := by simp [Complex.mul_re]
  rw [← hre]
  exact (Complex.abs_re_le_norm _).trans hn

/-- `c₀ = (2iη)⁻¹` has `Re(ω c₀) = Im ω/(2η)`. -/
theorem rf_re_mul_cZero {η : ℝ} (hη : 0 < η) (ω : ℂ) :
    (ω * (2 * Complex.I * (η : ℂ))⁻¹).re = ω.im / (2 * η) := by
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have e : (2 * Complex.I * (η : ℂ))⁻¹ = (((2 * η)⁻¹ : ℝ) : ℂ) * (-Complex.I) := by
    push_cast
    field_simp
    simp [Complex.I_sq]
  rw [e]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- **Second-order expansion of `u = Tr(MᴴYM)`** with `Q = RᴴYR`, `M = R·KM`, `KM = 1 + ωM`:
`|u - q - 2Re(ωTr(Q(R - c₀))) - q Im ω/η| ≤ |ω|²q(2‖R‖‖M‖ + ‖M‖²)`, `c₀ = (2iη)⁻¹`. -/
theorem rf_u_expand {Q R M KM Y : Matrix (Fin W) (Fin W) ℂ} {ω : ℂ} {η : ℝ} (hη : 0 < η)
    (hY : Y.PosSemidef) (hQ : Q = Rᴴ * Y * R) (hRKM : R * KM = M) (hKM : KM = 1 + ω • M) :
    |(Mᴴ * Y * M).trace.re - Q.trace.re -
        2 * (ω * (Q * (R - (2 * Complex.I * (η : ℂ))⁻¹ • 1)).trace).re -
        Q.trace.re * ω.im / η| ≤
      ‖ω‖ ^ 2 * Q.trace.re * (2 * ‖R‖ * ‖M‖ + ‖M‖ ^ 2) := by
  set c₀ : ℂ := (2 * Complex.I * (η : ℂ))⁻¹
  have hQp : Q.PosSemidef := by rw [hQ]; exact hY.conjTranspose_mul_mul_same _
  set q := Q.trace.re
  have hq0 : 0 ≤ q := (mm_trace_posSemidef hQp).1
  have hTrQ : Q.trace = (q : ℂ) := (mm_trace_posSemidef hQp).2
  have hMYM : Mᴴ * Y * M = KMᴴ * Q * KM := by
    rw [← hRKM, conjTranspose_mul, hQ]; simp only [Matrix.mul_assoc]
  set τ := (Q * M).trace
  set σ := (Q * (M * Mᴴ)).trace
  set ρ := (Q * (R * M)).trace
  have hstar : (Q * Mᴴ).trace = star τ := by
    rw [← trace_conjTranspose, conjTranspose_mul, hQp.1.eq, trace_mul_comm]
  have hexp : (Mᴴ * Y * M).trace = (q : ℂ) + ω * τ + star (ω * τ) + (ω * star ω) * σ := by
    rw [hMYM, trace_mul_comm, ← Matrix.mul_assoc, trace_mul_comm, hKM]
    simp only [conjTranspose_add, conjTranspose_one, conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      trace_add, trace_smul, smul_eq_mul]
    rw [hTrQ, hstar, star_mul', ← Matrix.mul_assoc Q M Mᴴ]
    simp only [σ]
    rw [Matrix.mul_assoc]
    ring
  have hM : M = R + ω • (R * M) := by
    conv_lhs => rw [← hRKM, hKM]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hτ : τ = (Q * (R - c₀ • 1)).trace + c₀ * q + ω * ρ := by
    simp only [τ]
    conv_lhs => rw [hM]
    rw [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, Matrix.mul_sub, trace_sub,
      Matrix.mul_smul, Matrix.mul_one, trace_smul, hTrQ, smul_eq_mul, smul_eq_mul]
    ring
  have hu : (Mᴴ * Y * M).trace.re = q + 2 * (ω * τ).re + ((ω * star ω) * σ).re := by
    rw [hexp]; simp only [Complex.add_re, Complex.ofReal_re, Complex.star_def, Complex.conj_re]
    ring
  have hτre : (ω * τ).re = (ω * (Q * (R - c₀ • 1)).trace).re + q * ω.im / (2 * η) +
      (ω * ω * ρ).re := by
    rw [hτ, mul_add, mul_add, Complex.add_re, Complex.add_re, ← mul_assoc ω ω ρ]
    have : (ω * (c₀ * q)).re = (ω * c₀).re * q := by
      rw [← mul_assoc]; simp [Complex.mul_re]
    rw [this, rf_re_mul_cZero hη]; ring
  have hρ : ‖ρ‖ ≤ ‖R‖ * ‖M‖ * q := by
    simp only [ρ]; rw [trace_mul_comm]
    exact (norm_trace_mul_posSemidef_le hQp _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) hq0)
  have hσ : ‖σ‖ ≤ ‖M‖ ^ 2 * q := by
    simp only [σ]; rw [trace_mul_comm]
    refine (norm_trace_mul_posSemidef_le hQp _).trans (mul_le_mul_of_nonneg_right ?_ hq0)
    refine (Matrix.l2_opNorm_mul _ _).trans (le_of_eq ?_)
    rw [Matrix.l2_opNorm_conjTranspose, sq]
  have e : (Mᴴ * Y * M).trace.re - q - 2 * (ω * (Q * (R - c₀ • 1)).trace).re - q * ω.im / η =
      2 * (ω * ω * ρ).re + ((ω * star ω) * σ).re := by
    rw [hu, hτre]; field_simp; ring
  rw [e]
  have n1 : |2 * (ω * ω * ρ).re| ≤ 2 * (‖ω‖ ^ 2 * (‖R‖ * ‖M‖ * q)) := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
    rw [norm_mul, norm_mul, ← sq]
    exact mul_le_mul_of_nonneg_left hρ (by positivity)
  have n2 : |((ω * star ω) * σ).re| ≤ ‖ω‖ ^ 2 * (‖M‖ ^ 2 * q) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, Complex.star_def, Complex.norm_conj, ← sq]
    exact mul_le_mul_of_nonneg_left hσ (by positivity)
  calc |2 * (ω * ω * ρ).re + ((ω * star ω) * σ).re|
      ≤ |2 * (ω * ω * ρ).re| + |((ω * star ω) * σ).re| := abs_add_le _ _
    _ ≤ 2 * (‖ω‖ ^ 2 * (‖R‖ * ‖M‖ * q)) + ‖ω‖ ^ 2 * (‖M‖ ^ 2 * q) := add_le_add n1 n2
    _ = _ := by ring

/-- `|N/A - q/B| ≤ |N - q| + q|A - B|` for `A, B ≥ 1`, `q ≥ 0`. -/
theorem rf_ratio {N q A B : ℝ} (hq : 0 ≤ q) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    |N / A - q / B| ≤ |N - q| + q * |A - B| := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have e : N / A - q / B = (N - q) / A + q * (B - A) / (A * B) := by field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hA0]; exact div_le_self (abs_nonneg _) hA
  · rw [abs_div, abs_mul, abs_of_nonneg hq, abs_of_pos (mul_pos hA0 hB0), abs_sub_comm]
    refine div_le_self (by positivity) ?_
    nlinarith

/-- `k_h/(bhη) ≤ 4L_i/b` for `1/2 ≤ h ≤ 3/2`, `η⁻¹ ≤ L_i`. -/
theorem rf_kappa_le {η b h Li : ℝ} (hη : 0 < η) (hLi : η⁻¹ ≤ Li) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hh1 : 1 / 2 ≤ h) (hh2 : h ≤ 3 / 2) :
    ((1 - 2 * b) + b ^ 2 * h) / (b * h * η) ≤ 4 * Li / b := by
  have hk : (1 - 2 * b) + b ^ 2 * h ≤ 2 := by nlinarith
  have h1 : ((1 - 2 * b) + b ^ 2 * h) / (b * h * η) ≤ 2 / (b * (1 / 2) * η) :=
    div_le_div₀ (by norm_num) hk (by positivity)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh1 hb0.le) hη.le)
  have h2 : 2 / (b * (1 / 2) * η) = 4 / b * η⁻¹ := by field_simp; ring
  rw [h2] at h1
  refine h1.trans ?_
  calc 4 / b * η⁻¹ ≤ 4 / b * Li := mul_le_mul_of_nonneg_left hLi (by positivity)
    _ = 4 * Li / b := by ring

/-- `|k_h/(bhη) - α| ≤ 2L_i|h - 1|/b`, `α = (1-b)²/(bη)`. -/
theorem rf_kappa_sub {η b h Li : ℝ} (hη : 0 < η) (hLi : η⁻¹ ≤ Li) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hh1 : 1 / 2 ≤ h) :
    |((1 - 2 * b) + b ^ 2 * h) / (b * h * η) - (1 - b) ^ 2 / (b * η)| ≤ 2 * Li / b * |h - 1| := by
  have hh0 : 0 < h := by linarith
  have e1 : ((1 - 2 * b) + b ^ 2 * h) / (b * h * η) - (1 - b) ^ 2 / (b * η) =
      (1 - 2 * b) * (1 - h) / (b * h * η) := by field_simp; ring
  rw [e1, abs_div, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * b),
    abs_of_pos (by positivity : 0 < b * h * η), abs_sub_comm]
  have h1 : (1 - 2 * b) * |h - 1| / (b * h * η) ≤ |h - 1| / (b * (1 / 2) * η) :=
    div_le_div₀ (abs_nonneg _) (by nlinarith [abs_nonneg (h - 1)]) (by positivity)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh1 hb0.le) hη.le)
  have h2 : |h - 1| / (b * (1 / 2) * η) = 2 / b * |h - 1| * η⁻¹ := by field_simp
  rw [h2] at h1
  refine h1.trans ?_
  have : 2 / b * |h - 1| * η⁻¹ ≤ 2 / b * |h - 1| * Li :=
    mul_le_mul_of_nonneg_left hLi (by positivity)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The numerator step: `N = ιu/η` with `ι = η - ω_i`, `u = q + t + qω_i/η + r'`. -/
theorem rf_numer {η q u ωi t r' x : ℝ} (hη : 0 < η) (hx : |ωi / η| ≤ x) (hx1 : x ≤ 1)
    (hq : 0 ≤ q) (hu : u = q + t + q * ωi / η + r') :
    |(η - ωi) * u / η - q| ≤ q * x ^ 2 + 2 * (|t| + |r'|) := by
  have e : (η - ωi) * u / η - q = -(q * (ωi / η) ^ 2) + (1 - ωi / η) * (t + r') := by
    rw [hu]; field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_neg, abs_mul, abs_of_nonneg hq, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx 2) hq
  · rw [abs_mul]
    have h1 : |1 - ωi / η| ≤ 2 := by
      have := abs_sub (1 : ℝ) (ωi / η); rw [abs_one] at this; linarith
    exact mul_le_mul h1 (abs_add_le _ _) (abs_nonneg _) (by norm_num)

/-- **Scalar step of the refined mean**. With `ι = η - Im ω`,
`u = q + t + q Im ω/η + O(ρ)`, `|t| ≤ 2C_m e τ`, `τ ≤ (3/2)L_i q`, `|h - 1|, |Im ω| ≤ C_m e`,
`C_m e L_i ≤ 1`, `ρ ≤ C_m e·K_R e q`:
`|bhιu/(bhη + k_h u/W) - q/(1+αq/W)| ≤ 4C_m eτ + K₂e²q + K₃eq²/W`. -/
theorem rf_scalar {η b h u q W ωi t ρ Li Cm e τ KR : ℝ} (hη : 0 < η) (hLi : η⁻¹ ≤ Li)
    (hb0 : 0 < b) (hb : b < 1 / 2) (hCm : 0 ≤ Cm) (he : 0 ≤ e) (hCme : Cm * e * Li ≤ 1)
    (hCme2 : Cm * e ≤ 1 / 2)
    (hh : |h - 1| ≤ Cm * e) (hq : 0 ≤ q) (hu : 0 ≤ u) (hW : 0 < W)
    (hωi : |ωi| ≤ Cm * e) (huexp : |u - q - t - q * ωi / η| ≤ ρ) (hρ : ρ ≤ Cm * e * (KR * (e * q)))
    (hKR : 0 ≤ KR) (ht : |t| ≤ 2 * Cm * e * τ) (hτ : τ ≤ 3 / 2 * Li * q) :
    |b * h * (η - ωi) * u / (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W)) -
        q / (1 + (1 - b) ^ 2 / (b * η) * q / W)| ≤
      4 * Cm * (e * τ) + (Cm ^ 2 * Li ^ 2 + 2 * Cm * KR) * (e ^ 2 * q) +
        (4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b) * (e * q ^ 2 / W) := by
  have hLi0 : 0 < Li := lt_of_lt_of_le (inv_pos.mpr hη) hLi
  have hh1 : 1 / 2 ≤ h := by have := neg_abs_le (h - 1); linarith
  have hh2 : h ≤ 3 / 2 := by have := le_abs_self (h - 1); linarith
  have hh0 : 0 < h := by linarith
  have hc : 0 ≤ 1 - 2 * b := by linarith
  have hbhη : 0 < b * h * η := by positivity
  obtain ⟨κ', hκdef⟩ : ∃ x, x = ((1 - 2 * b) + b ^ 2 * h) / (b * h * η) := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ x, x = (1 - b) ^ 2 / (b * η) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ' := by rw [hκdef]; positivity
  have hα0 : 0 ≤ α := by rw [hαdef]; positivity
  have hκle : κ' ≤ 4 * Li / b := by rw [hκdef]; exact rf_kappa_le hη hLi hb0 hb hh1 hh2
  have hκα : |κ' - α| ≤ 2 * Li / b * |h - 1| := by
    rw [hκdef, hαdef]; exact rf_kappa_sub hη hLi hb0 hb hh1
  have hratio : b * h * (η - ωi) * u / (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W)) =
      ((η - ωi) * u / η) / (1 + κ' * u / W) := by
    rw [hκdef]; field_simp
  rw [hratio, ← hαdef]
  have hA : 1 ≤ 1 + κ' * u / W := by have : 0 ≤ κ' * u / W := by positivity
                                     linarith
  have hB : 1 ≤ 1 + α * q / W := by have : 0 ≤ α * q / W := by positivity
                                    linarith
  refine (rf_ratio hq hA hB).trans ?_
  obtain ⟨r', hr'⟩ : ∃ x, x = u - q - t - q * ωi / η := ⟨_, rfl⟩
  have hu' : u = q + t + q * ωi / η + r' := by rw [hr']; ring
  have hr'ρ : |r'| ≤ ρ := by rw [hr']; exact huexp
  have hωη : |ωi / η| ≤ Cm * e * Li := by
    rw [abs_div, abs_of_pos hη, div_eq_mul_inv]
    exact mul_le_mul hωi hLi (inv_pos.mpr hη).le (by positivity)
  have hN := rf_numer hη hωη hCme hq hu'
  have hτq : τ ≤ 3 / 2 * Li * q := hτ
  have ht' : |t| ≤ 3 * Cm * Li * (e * q) := by
    refine ht.trans ?_
    have : 2 * Cm * e * τ ≤ 2 * Cm * e * (3 / 2 * Li * q) :=
      mul_le_mul_of_nonneg_left hτq (by positivity)
    linarith
  have hρ' : ρ ≤ KR / 2 * (e * q) := by
    refine hρ.trans ?_
    calc Cm * e * (KR * (e * q)) ≤ 1 / 2 * (KR * (e * q)) :=
          mul_le_mul_of_nonneg_right hCme2 (by positivity)
      _ = _ := by ring
  have huq : |u - q| ≤ (4 * Cm * Li + KR) * (e * q) := by
    have e1 : u - q = t + q * (ωi / η) + r' := by rw [hu']; ring
    have h2 : |q * (ωi / η)| ≤ Cm * Li * (e * q) := by
      rw [abs_mul, abs_of_nonneg hq]
      calc q * |ωi / η| ≤ q * (Cm * e * Li) := mul_le_mul_of_nonneg_left hωη hq
        _ = _ := by ring
    rw [e1]
    have h3 : |t + q * (ωi / η) + r'| ≤ |t| + |q * (ωi / η)| + |r'| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have h4 : 0 ≤ KR / 2 * (e * q) := by positivity
    have h5 : (4 * Cm * Li + KR) * (e * q) = 3 * Cm * Li * (e * q) + Cm * Li * (e * q) +
        KR / 2 * (e * q) + KR / 2 * (e * q) := by ring
    linarith
  have hAB : q * |1 + κ' * u / W - (1 + α * q / W)| ≤
      (4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b) * (e * q ^ 2 / W) := by
    have e1 : 1 + κ' * u / W - (1 + α * q / W) = (κ' * (u - q) + (κ' - α) * q) / W := by
      field_simp; ring
    rw [e1, abs_div, abs_of_pos hW]
    have a1 : κ' * |u - q| ≤ 4 * Li / b * ((4 * Cm * Li + KR) * (e * q)) :=
      mul_le_mul hκle huq (abs_nonneg _) (by positivity)
    have a2 : |κ' - α| * q ≤ 2 * Li / b * (Cm * e) * q :=
      mul_le_mul_of_nonneg_right (hκα.trans (mul_le_mul_of_nonneg_left hh (by positivity))) hq
    have h1 : |κ' * (u - q) + (κ' - α) * q| ≤
        (4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b) * (e * q) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hκ0, abs_of_nonneg hq]
      have h6 : 2 * Li / b * (Cm * e) * q = 2 * Cm * Li / b * (e * q) := by ring
      have h7 : (4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b) * (e * q) =
          4 * Li / b * ((4 * Cm * Li + KR) * (e * q)) + 2 * Cm * Li / b * (e * q) := by ring
      linarith
    calc q * (|κ' * (u - q) + (κ' - α) * q| / W)
        ≤ q * ((4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b) * (e * q) / W) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 hW.le) hq
      _ = _ := by ring
  have hN' : |(η - ωi) * u / η - q| ≤ 4 * Cm * (e * τ) + (Cm ^ 2 * Li ^ 2 + 2 * Cm * KR) *
      (e ^ 2 * q) := by
    refine hN.trans ?_
    have h1 : q * (Cm * e * Li) ^ 2 = Cm ^ 2 * Li ^ 2 * (e ^ 2 * q) := by ring
    have h2 : 2 * ρ ≤ 2 * Cm * KR * (e ^ 2 * q) := by
      have : Cm * e * (KR * (e * q)) = Cm * KR * (e ^ 2 * q) := by ring
      linarith
    have h3 : 2 * |t| ≤ 4 * Cm * (e * τ) := by linarith
    linarith
  linarith

end BlockBand.Transmission.Generator
