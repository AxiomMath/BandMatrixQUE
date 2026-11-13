module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Scalar integrals for the fractional Hessian

* `integrableOn_rpow_div_pow`: `s^q/(m+s)^k` is integrable on `(0,∞)` if `q > -1`, `q - k < -1`,
  `m > 0`;
* `integral_rpow_div_one_add`: `∫_0^∞ u^{p-1}/(1+u) du = π/sin(πp)`, from
  `B(p, 1-p) = Γ(p)Γ(1-p)` and the substitution `x = u/(1+u)`;
* `integral_rpow_mul_div_add`: `∫_0^∞ s^{p-1} λ/(λ+s) ds = λ^p π/sin(πp)` for `λ > 0`
  (substitution `s = λu`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open MeasureTheory Set Real

/-- `s^q/(m+s)^k` is integrable on `(0,∞)` for `q > -1`, `q - k < -1`, `m > 0`. -/
theorem integrableOn_rpow_div_pow {q m : ℝ} {k : ℕ} (hq : -1 < q) (hk : q - k < -1)
    (hm : 0 < m) : IntegrableOn (fun s : ℝ => s ^ q / (m + s) ^ k) (Ioi 0) := by
  have hcont : ContinuousOn (fun s : ℝ => s ^ q / (m + s) ^ k) (Ioi 0) := by
    refine ContinuousOn.div ?_ (by fun_prop) fun s hs => by
      have : 0 < m + s := by have := mem_Ioi.mp hs; linarith
      positivity
    exact fun s hs => (continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hs))).continuousWithinAt
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h0 : IntegrableOn (fun s : ℝ => s ^ q / m ^ k) (Ioc 0 1) := by
      have := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hq)
      exact this.div_const _
    refine h0.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hm.le (by linarith) k)
  · have h1 : IntegrableOn (fun s : ℝ => s ^ (q - k)) (Ioi 1) := integrableOn_Ioi_rpow_of_lt hk one_pos
    refine h1.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs1 : 1 < s := hs
    have hs0 : 0 < s := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), rpow_sub hs0, rpow_natCast]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hs0.le (by linarith) k)

/-- The Beta integral `B(p, 1-p) = π/sin(πp)` as a real integral over `(0,1)`. -/
theorem integral_Ioo_beta {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∫ x in Ioo (0 : ℝ) 1, x ^ (p - 1) * (1 - x) ^ (-p) = π / Real.sin (π * p) := by
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (p : ℂ)) (t := 1 - (p : ℂ))
    (by simpa using hp0) (by simpa using hp1)
  rw [add_sub_cancel, Complex.Gamma_one, one_mul, Complex.Gamma_mul_Gamma_one_sub] at hB
  have hreal : Complex.betaIntegral (p : ℂ) (1 - (p : ℂ)) =
      ((∫ x in (0 : ℝ)..1, x ^ (p - 1) * (1 - x) ^ (-p) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (by linarith [hx.2])]
    push_cast; ring_nf
  rw [hreal] at hB
  have hc : ((π / Real.sin (π * p) : ℝ) : ℂ) = (π : ℂ) / Complex.sin (π * p) := by
    push_cast; rfl
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  exact_mod_cast hB.symm.trans hc.symm

/-- **`∫_0^∞ u^{p-1}/(1+u) du = π/sin(πp)`**, `0 < p < 1`. -/
theorem integral_rpow_div_one_add {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∫ u in Ioi (0 : ℝ), u ^ (p - 1) / (1 + u) = π / Real.sin (π * p) := by
  set f : ℝ → ℝ := fun u => u / (1 + u)
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt f (1 / (1 + u) ^ 2) (Ioi 0) u := by
    intro u hu
    have hu0 : (1 + u) ≠ 0 := by have := mem_Ioi.mp hu; linarith
    have h := ((hasDerivAt_id u).div ((hasDerivAt_id u).const_add 1) hu0)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [id]; field_simp; ring
  have hinj : InjOn f (Ioi 0) := by
    intro x hx y hy hxy
    have hx0 : 0 < 1 + x := by have := mem_Ioi.mp hx; linarith
    have hy0 : 0 < 1 + y := by have := mem_Ioi.mp hy; linarith
    simp only [f] at hxy
    rw [div_eq_div_iff hx0.ne' hy0.ne'] at hxy
    linarith
  have himage : f '' Ioi 0 = Ioo 0 1 := by
    ext x; constructor
    · rintro ⟨u, hu, rfl⟩
      have hu0 : 0 < u := hu
      simp only [f, mem_Ioo]
      exact ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩
    · rintro ⟨hx0, hx1⟩
      refine ⟨x / (1 - x), div_pos hx0 (by linarith), ?_⟩
      have : (1 - x) ≠ 0 := by linarith
      simp only [f]; field_simp; ring
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun x => x ^ (p - 1) * (1 - x) ^ (-p))
  rw [himage, integral_Ioo_beta hp0 hp1] at hcv
  rw [hcv]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 < u := hu
  have h1u : 0 < 1 + u := by linarith
  simp only [f, smul_eq_mul]
  have e1 : 1 - u / (1 + u) = (1 + u)⁻¹ := by field_simp; ring
  rw [e1, abs_of_pos (by positivity), div_rpow hu0.le h1u.le, inv_rpow h1u.le, ← rpow_neg h1u.le,
    neg_neg]
  have e2 : (1 + u) ^ p = (1 + u) ^ (p - 1) * (1 + u) := by
    rw [← rpow_add_one h1u.ne']; ring_nf
  rw [e2]
  have : 0 < (1 + u) ^ (p - 1) := rpow_pos_of_pos h1u _
  field_simp

/-- **`∫_0^∞ s^{p-1} λ/(λ+s) ds = λ^p π/sin(πp)`** for `λ > 0`, `0 < p < 1`. -/
theorem integral_rpow_mul_div_add {p l : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hl : 0 < l) :
    ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * (l / (l + s)) = l ^ p * (π / Real.sin (π * p)) := by
  have h := integral_comp_mul_left_Ioi (fun s => s ^ (p - 1) * (l / (l + s))) 0 hl
  rw [mul_zero] at h
  have hc : ∫ x in Ioi (0 : ℝ), (l * x) ^ (p - 1) * (l / (l + l * x)) =
      l ^ (p - 1) * ∫ x in Ioi (0 : ℝ), x ^ (p - 1) / (1 + x) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    rw [mul_rpow hl.le hx0.le]
    have : l + l * x = l * (1 + x) := by ring
    rw [this]
    have : (0 : ℝ) < 1 + x := by linarith
    field_simp
  rw [hc, integral_rpow_div_one_add hp0 hp1, smul_eq_mul] at h
  have hl' : l ^ p = l * l ^ (p - 1) := by
    rw [← rpow_one_add' hl.le (by linarith)]; ring_nf
  rw [hl', mul_assoc, h, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul]

end BlockBand.Transmission.LawClauses
