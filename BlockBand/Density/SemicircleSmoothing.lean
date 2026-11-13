module

public import BlockBand.External.ErdosRiabov.Semicircle
public import BlockBand.Model.Observables

/-!
# Semicircle smoothing error: `|π⁻¹ Im m_sc(e+iη) - ρ(e)| ≤ η/(π·√(4-e²)/2)`

The semicircle smoothing error is `O_κ(η)`. Deterministic, for every bulk `|e| < 2` and every
`η > 0`, with `m_sc = ErdosRiabov.semicircleM` (Dyson equation `m² + zm + 1 = 0`, `Im m > 0`) and
`ρ = Parameters.semicircleDensity`. Proof: with `m₀ = (-e + i√(4-e²))/2` (`|m₀| = 1`),
`(m - m₀)(m + m₀ + z) = -iη m₀` and `Im(m + m₀ + z) ≥ Im m₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open BlockBand.External

/-- **Semicircle smoothing.** -/
theorem abs_im_semicircleM_div_pi_sub_le {e η : ℝ} (he : |e| < 2) (hη : 0 < η) :
    |(ErdosRiabov.semicircleM ((e : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi -
        Parameters.semicircleDensity e| ≤
      η / (Real.pi * (Real.sqrt (4 - e ^ 2) / 2)) := by
  set z : ℂ := (e : ℂ) + (η : ℂ) * Complex.I with hz
  set m := ErdosRiabov.semicircleM z
  set s := Real.sqrt (4 - e ^ 2) with hs
  have he2 : 0 < 4 - e ^ 2 := by
    have : e ^ 2 < 4 := by
      have := sq_abs e
      nlinarith [abs_nonneg e]
    linarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr he2
  have hss : s ^ 2 = 4 - e ^ 2 := Real.sq_sqrt he2.le
  set m₀ : ℂ := ((-e : ℝ) : ℂ) / 2 + ((s / 2 : ℝ) : ℂ) * Complex.I with hm₀
  have hzim : z.im = η := by simp [hz]
  have hzre : z.re = e := by simp [hz]
  have hmim : 0 < m.im := by
    have := ErdosRiabov.semicircleM_same_sign (z := z) (by rw [hzim]; exact hη.ne')
    rw [hzim] at this
    exact pos_of_mul_pos_left this hη.le
  have hdy : m ^ 2 + z * m + 1 = 0 := ErdosRiabov.semicircleM_dyson z
  have hdy0 : m₀ ^ 2 + (e : ℂ) * m₀ + 1 = 0 := by
    apply Complex.ext
    · simp [hm₀, sq, Complex.mul_re]
      nlinarith [hss]
    · simp [hm₀, sq, Complex.mul_im]
      ring
  have hid : (m - m₀) * (m + m₀ + z) = -((η : ℂ) * Complex.I) * m₀ := by
    have : z = (e : ℂ) + (η : ℂ) * Complex.I := hz
    linear_combination hdy - hdy0 + (m₀) * (this)
  have hm₀n : ‖m₀‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [hm₀, Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    rw [Real.sqrt_eq_one]
    nlinarith [hss]
  have hm₀im : m₀.im = s / 2 := by simp [hm₀]
  have hden : s / 2 ≤ ‖m + m₀ + z‖ := by
    have h1 : (m + m₀ + z).im = m.im + s / 2 + η := by
      rw [Complex.add_im, Complex.add_im, hm₀im, hzim]
    have h2 := Complex.abs_im_le_norm (m + m₀ + z)
    rw [h1, abs_of_pos (by linarith)] at h2
    linarith
  have hdiff : ‖m - m₀‖ ≤ η / (s / 2) := by
    have hn := congrArg norm hid
    rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hη, hm₀n, mul_one] at hn
    rw [le_div_iff₀ (by positivity)]
    calc ‖m - m₀‖ * (s / 2) ≤ ‖m - m₀‖ * ‖m + m₀ + z‖ :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ = η := hn
  have him : |m.im - s / 2| ≤ η / (s / 2) := by
    have h := (Complex.abs_im_le_norm (m - m₀)).trans hdiff
    rwa [Complex.sub_im, hm₀im] at h
  have hρ : Parameters.semicircleDensity e = (s / 2) / Real.pi := by
    unfold Parameters.semicircleDensity
    rw [← hs]
    field_simp
  rw [hρ, ← sub_div, abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
  calc |m.im - s / 2| ≤ η / (s / 2) := him
    _ = η / (Real.pi * (s / 2)) * Real.pi := by field_simp

end BlockBand.Density
