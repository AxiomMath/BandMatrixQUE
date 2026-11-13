module

public import BlockBand.Endpoints.Response.FractionalTraceIntegral

/-!
# Scalar inputs of the fractional trace Jensen gap

* `ftj_resolventConst p = ∫_0^∞ s^{p-1}/(1+s) ds` (`= π / sin(πp)`; only `0 < K_p < ∞` is
  used, `ftj_resolventConst_pos`);
* `ftj_integral_resolvent`: `∫_0^∞ s^{p-1}/(x+s) ds = K_p x^{p-1}` for `x > 0` (scaling);
* `ftj_divided_difference`: `(p x^{p-1} - p y^{p-1})(y - x) = (p/K_p)(y-x)² ∫ k_p(x,y)` with
  `k_p = concavityKernel p`;
* `ftj_rpow_tangent`: the tangent inequality `y^p ≤ x^p + p x^{p-1}(y - x)` (`x > 0`, `y ≥ 0`);
* `ftj_integral_concavityKernel_zero_left/right`: `k_p(0,b)` is not integrable at `0`, so its
  Bochner integral is `0`;
* `ftj_integral_concavityKernel_shift_ge`: `∫ k_p(a,b) ≤ 4 ∫ k_p(a+ε,b+ε)` for `0 ≤ ε ≤ a, b`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set

/-- The resolvent constant `K_p = ∫_0^∞ s^{p-1}/(1+s) ds` (`= π / sin(πp)` for `0 < p < 1`). -/
def ftj_resolventConst (p : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), s ^ (p - 1) / (1 + s)

/-- `s ↦ s^{p-1}/(x+s)` is integrable on `(0, ∞)` for `0 < p < 1`, `x > 0`. -/
theorem ftj_integrableOn_resolvent {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => s ^ (p - 1) / (x + s)) (Ioi 0) := by
  have hcont : ContinuousOn (fun s : ℝ => s ^ (p - 1) / (x + s)) (Ioi 0) := by
    intro s hs
    have hs : 0 < s := hs
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div ?_ (by fun_prop) (by positivity)
    exact Real.continuousAt_rpow_const _ _ (Or.inl hs.ne')
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hg : IntegrableOn (fun s : ℝ => x⁻¹ * s ^ (p - 1)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (r := p - 1) (by linarith)).1
      exact (this.const_mul _)
    refine hg.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    rw [Real.norm_of_nonneg (by positivity), div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hx (by linarith)) (Real.rpow_nonneg hs0.le _)
  · have hg : IntegrableOn (fun s : ℝ => s ^ (p - 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hg.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs1 : 1 < s := hs
    have hs0 : 0 < s := by linarith
    rw [Real.norm_of_nonneg (by positivity)]
    have hsplit : s ^ (p - 1) = s ^ (p - 2) * s := by
      rw [← Real.rpow_add_one hs0.ne']; congr 1; ring
    rw [hsplit, div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hs0.le _)

/-- `K_p > 0`. -/
theorem ftj_resolventConst_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < ftj_resolventConst p := by
  have hint := ftj_integrableOn_resolvent hp0 hp1 (x := 1) one_pos
  unfold ftj_resolventConst
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun s : ℝ => s ^ (p - 1) / (1 + s)) ∩ Ioi 0 :=
      fun s hs => ⟨by
        have hs0 : 0 < s := hs
        exact (div_pos (Real.rpow_pos_of_pos hs0 _) (by linarith)).ne', hs⟩
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    exact div_nonneg (Real.rpow_nonneg hs0.le _) (by linarith)

/-- Scaling: `∫_0^∞ s^{p-1}/(x+s) ds = K_p x^{p-1}` for `x > 0`. -/
theorem ftj_integral_resolvent {p x : ℝ} (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), s ^ (p - 1) / (x + s) = ftj_resolventConst p * x ^ (p - 1) := by
  have h := integral_comp_mul_left_Ioi (fun s : ℝ => s ^ (p - 1) / (x + s)) 0 hx
  rw [mul_zero, smul_eq_mul] at h
  have hcongr : ∫ t in Ioi (0 : ℝ), (x * t) ^ (p - 1) / (x + x * t) =
      ∫ t in Ioi (0 : ℝ), x ^ (p - 1) / x * (t ^ (p - 1) / (1 + t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    rw [Real.mul_rpow hx.le ht0.le]
    field_simp
  rw [hcongr, integral_const_mul] at h
  unfold ftj_resolventConst
  have hx0 : x ≠ 0 := hx.ne'
  calc ∫ s in Ioi (0 : ℝ), s ^ (p - 1) / (x + s)
      = x * (x⁻¹ * ∫ s in Ioi (0 : ℝ), s ^ (p - 1) / (x + s)) := by field_simp
    _ = x * (x ^ (p - 1) / x * ∫ t in Ioi (0 : ℝ), t ^ (p - 1) / (1 + t)) := by rw [h]
    _ = (∫ s in Ioi (0 : ℝ), s ^ (p - 1) / (1 + s)) * x ^ (p - 1) := by field_simp

/-- The divided difference of `p x^{p-1}` through the concavity kernel:
`(p x^{p-1} - p y^{p-1})(y - x) = (p / K_p) (y - x)² ∫_0^∞ s^{p-1}/((x+s)(y+s)) ds`. -/
theorem ftj_divided_difference {p x y : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hx : 0 < x)
    (hy : 0 < y) :
    (p * x ^ (p - 1) - p * y ^ (p - 1)) * (y - x) =
      p / ftj_resolventConst p *
        ((y - x) ^ 2 * ∫ s in Ioi (0 : ℝ), concavityKernel p x y s) := by
  have hK := (ftj_resolventConst_pos hp0 hp1).ne'
  have hpt : ∀ s ∈ Ioi (0 : ℝ), (y - x) ^ 2 * concavityKernel p x y s =
      (y - x) * (s ^ (p - 1) / (x + s)) - (y - x) * (s ^ (p - 1) / (y + s)) := by
    intro s hs
    have hs0 : 0 < s := hs
    unfold concavityKernel
    have h1 : x + s ≠ 0 := by positivity
    have h2 : y + s ≠ 0 := by positivity
    field_simp
    ring
  have hint := (ftj_integrableOn_resolvent hp0 hp1 hx).const_mul (y - x)
  have hint' := (ftj_integrableOn_resolvent hp0 hp1 hy).const_mul (y - x)
  rw [← integral_const_mul, setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_sub hint hint', integral_const_mul, integral_const_mul,
    ftj_integral_resolvent hx, ftj_integral_resolvent hy]
  field_simp

/-- Tangent inequality for `x ↦ x^p`, `0 ≤ p ≤ 1`: `y^p ≤ x^p + p x^{p-1}(y - x)`. -/
theorem ftj_rpow_tangent {p x y : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx : 0 < x) (hy : 0 ≤ y) :
    y ^ p ≤ x ^ p + p * x ^ (p - 1) * (y - x) := by
  have hs : -1 ≤ (y - x) / x := by
    rw [le_div_iff₀ hx]; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hp0 hp1
  have hyx : y = x * (1 + (y - x) / x) := by field_simp; ring
  have hx0 : x ≠ 0 := hx.ne'
  calc y ^ p = x ^ p * (1 + (y - x) / x) ^ p := by
        conv_lhs => rw [hyx]
        exact Real.mul_rpow hx.le (by linarith)
    _ ≤ x ^ p * (1 + p * ((y - x) / x)) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx.le _)
    _ = x ^ p + p * (x ^ p / x) * (y - x) := by field_simp
    _ = x ^ p + p * x ^ (p - 1) * (y - x) := by rw [Real.rpow_sub_one hx0]

/-- The concavity kernel is symmetric. -/
theorem ftj_concavityKernel_comm (p a b s : ℝ) :
    concavityKernel p a b s = concavityKernel p b a s := by
  unfold concavityKernel; rw [mul_comm (a + s)]

/-- For `p < 1` and `b ≥ 0`, `k_p(0, b)` is not integrable at `0`: its Bochner integral is `0`. -/
theorem ftj_integral_concavityKernel_zero_left {p b : ℝ} (hp1 : p < 1) (hb : 0 ≤ b) :
    ∫ s in Ioi (0 : ℝ), concavityKernel p 0 b s = 0 := by
  refine integral_undef fun h => ?_
  have h' : IntegrableOn (concavityKernel p 0 b) (Ioi 0) := h
  have h01 : IntegrableOn (concavityKernel p 0 b) (Ioo 0 1) := h'.mono_set Ioo_subset_Ioi_self
  have hpow : IntegrableOn (fun s : ℝ => s ^ (p - 2)) (Ioo 0 1) := by
    refine (h01.const_mul (b + 1)).mono' ((measurable_id.pow_const _).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have hs1 : s < 1 := hs.2
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hs0.le _)]
    unfold concavityKernel
    have hsplit : s ^ (p - 1) = s ^ (p - 2) * s := by
      rw [← Real.rpow_add_one hs0.ne']; congr 1; ring
    rw [hsplit, zero_add, show s ^ (p - 2) * s / (s * (b + s)) = s ^ (p - 2) / (b + s) by
      field_simp]
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    have hr := Real.rpow_nonneg hs0.le (p - 2)
    nlinarith
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one] at hpow
  linarith

/-- For `p < 1` and `a ≥ 0`, the Bochner integral of `k_p(a, 0)` is `0`. -/
theorem ftj_integral_concavityKernel_zero_right {p a : ℝ} (hp1 : p < 1) (ha : 0 ≤ a) :
    ∫ s in Ioi (0 : ℝ), concavityKernel p a 0 s = 0 := by
  simp_rw [ftj_concavityKernel_comm p a 0]
  exact ftj_integral_concavityKernel_zero_left hp1 ha

/-- Shift comparison: for `a, b > 0` and `0 ≤ ε ≤ a, b`,
`∫ k_p(a,b) ≤ 4 ∫ k_p(a+ε, b+ε)`. -/
theorem ftj_integral_concavityKernel_shift_ge {p a b ε : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 ≤ ε) (hεa : ε ≤ a) (hεb : ε ≤ b) :
    ∫ s in Ioi (0 : ℝ), concavityKernel p a b s ≤
      4 * ∫ s in Ioi (0 : ℝ), concavityKernel p (a + ε) (b + ε) s := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_concavityKernel hp0 hp1 ha hb)
    ((integrableOn_concavityKernel hp0 hp1 (by linarith) (by linarith)).const_mul 4)
    measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  unfold concavityKernel
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hr := Real.rpow_nonneg hs0.le (p - 1)
  have h1 : (a + ε + s) * (b + ε + s) ≤ 4 * ((a + s) * (b + s)) := by nlinarith
  nlinarith

end BlockBand.Endpoints
