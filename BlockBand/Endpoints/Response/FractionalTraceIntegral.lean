module

public import BlockBand.Prelude
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The divided-difference lower bound of the fractional concavity gap

- `concavityKernel p a b s = s^(p-1) / ((a+s)(b+s))`, the integrand;
- `integrableOn_concavityKernel`: integrable on `Ioi 0` for `0 < p < 1`, `a, b > 0`;
- `pair_concavity_integral_ge`: for `0 < p < 1`, `K > 0`, `0 ≤ x, y ≤ γ`,
  `K^(p-2)/(4(2-p)) · x^p y^p / γ^p ≤ x y ∫_{Ioi 0} s^(p-1)/((Kx+s)(Ky+s)) ds`;
- `sum_concavity_integral_ge`: the summed form, with constant `c_{p,K} = K^(p-2)/(4(2-p))`.

The constant differs from the one obtained by evaluating the integral exactly (as `π/sin(πp)`
times a divided difference of `x^{1-p}`); here the integral is only bounded below on
`s > min(Kx, Ky)`, where the integrand dominates `min(Kx,Ky)²/(4 K²xy) s^{p-3}`. Zero
eigenvalues need no regularization: both sides vanish.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set

/-- The concavity-gap integrand `s^(p-1) / ((a+s)(b+s))`. -/
def concavityKernel (p a b s : ℝ) : ℝ := s ^ (p - 1) / ((a + s) * (b + s))

/-- The integrand is nonnegative for `a, b, s ≥ 0`. -/
theorem concavityKernel_nonneg {p a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    0 ≤ concavityKernel p a b s :=
  div_nonneg (Real.rpow_nonneg hs _) (mul_nonneg (add_nonneg ha hs) (add_nonneg hb hs))

/-- The integrand is continuous on `(0, ∞)` for `a, b ≥ 0`. -/
theorem continuousOn_concavityKernel {p a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ContinuousOn (concavityKernel p a b) (Ioi 0) := by
  intro s hs
  have hs : 0 < s := hs
  refine ContinuousAt.continuousWithinAt ?_
  unfold concavityKernel
  refine ContinuousAt.div ?_ (by fun_prop) (by positivity)
  exact Real.continuousAt_rpow_const _ _ (Or.inl hs.ne')

/-- The concavity-gap integrand is integrable on `(0, ∞)` for `0 < p < 1` and `a, b > 0`. -/
theorem integrableOn_concavityKernel {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a)
    (hb : 0 < b) : IntegrableOn (concavityKernel p a b) (Ioi 0) := by
  have hcont := continuousOn_concavityKernel (p := p) ha.le hb.le
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · -- near zero: `≤ s^(p-1) / (ab)`
    have hg : IntegrableOn (fun s : ℝ => (a * b)⁻¹ * s ^ (p - 1)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (r := p - 1) (by linarith)).1
      exact (this.const_mul _)
    refine hg.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    rw [Real.norm_of_nonneg (concavityKernel_nonneg ha.le hb.le hs0.le)]
    unfold concavityKernel
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hs0.le _)
    exact inv_anti₀ (mul_pos ha hb)
      (mul_le_mul (by linarith) (by linarith) hb.le (by linarith))
  · -- near infinity: `≤ s^(p-3)`
    have hg : IntegrableOn (fun s : ℝ => s ^ (p - 3)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hg.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs1 : 1 < s := hs
    have hs0 : 0 < s := by linarith
    rw [Real.norm_of_nonneg (concavityKernel_nonneg ha.le hb.le hs0.le)]
    unfold concavityKernel
    have hsplit : s ^ (p - 1) = s ^ (p - 3) * s ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hs0]; congr 1; push_cast; ring
    rw [hsplit, div_le_iff₀ (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hs0.le _)
    nlinarith

/-- Pointwise domination on `s ≥ m = min(a, b)`:
`m²/(4ab) · s^(p-3) ≤ s^(p-1)/((a+s)(b+s))`. -/
theorem concavityKernel_ge_of_min_le {p a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : min a b ≤ s) :
    (min a b) ^ 2 / (4 * (a * b)) * s ^ (p - 3) ≤ concavityKernel p a b s := by
  set m := min a b with hm
  have hm0 : 0 < m := lt_min ha hb
  have hma : m ≤ a := min_le_left a b
  have hmb : m ≤ b := min_le_right a b
  have hs0 : 0 < s := hm0.trans_le hs
  unfold concavityKernel
  have hsplit : s ^ (p - 1) = s ^ (p - 3) * s ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs0]; congr 1; push_cast; ring
  rw [hsplit, le_div_iff₀ (by positivity)]
  have h1 : m * (a + s) ≤ 2 * a * s := by nlinarith
  have h2 : m * (b + s) ≤ 2 * b * s := by nlinarith
  have h3 : m ^ 2 * ((a + s) * (b + s)) ≤ 4 * (a * b) * s ^ 2 := by
    have := mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith
  have ht : 0 < s ^ (p - 3) := Real.rpow_pos_of_pos hs0 _
  rw [show m ^ 2 / (4 * (a * b)) * s ^ (p - 3) * ((a + s) * (b + s)) =
      s ^ (p - 3) * ((m ^ 2 * ((a + s) * (b + s))) / (4 * (a * b))) by ring]
  refine mul_le_mul_of_nonneg_left ?_ ht.le
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Lower bound by the minimum: for `0 < p < 1` and `a, b > 0`,
`min(a,b)^p / (4(2-p)) ≤ a b ∫_{Ioi 0} s^(p-1)/((a+s)(b+s)) ds`. -/
theorem mul_integral_concavityKernel_ge {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a)
    (hb : 0 < b) :
    (min a b) ^ p / (4 * (2 - p)) ≤ a * b * ∫ s in Ioi 0, concavityKernel p a b s := by
  set m := min a b with hm
  have hm0 : 0 < m := lt_min ha hb
  have hint := integrableOn_concavityKernel hp0 hp1 ha hb
  have hpow : IntegrableOn (fun s : ℝ => m ^ 2 / (4 * (a * b)) * s ^ (p - 3)) (Ioi m) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hm0).const_mul _
  have hstep1 : ∫ s in Ioi m, m ^ 2 / (4 * (a * b)) * s ^ (p - 3) ≤
      ∫ s in Ioi m, concavityKernel p a b s :=
    setIntegral_mono_on hpow (hint.mono_set (Ioi_subset_Ioi hm0.le)) measurableSet_Ioi
      fun s hs => concavityKernel_ge_of_min_le ha hb (le_of_lt hs)
  have hstep2 : ∫ s in Ioi m, concavityKernel p a b s ≤ ∫ s in Ioi 0, concavityKernel p a b s :=
    setIntegral_mono_set hint
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs =>
        concavityKernel_nonneg ha.le hb.le (le_of_lt hs)))
      (Filter.Eventually.of_forall (Ioi_subset_Ioi hm0.le))
  have hval : ∫ s in Ioi m, m ^ 2 / (4 * (a * b)) * s ^ (p - 3) =
      m ^ 2 / (4 * (a * b)) * (m ^ (p - 2) / (2 - p)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hm0]
    congr 1
    rw [show p - 3 + 1 = p - 2 by ring, neg_div, ← div_neg, neg_sub]
  have hmp : m ^ 2 * m ^ (p - 2) = m ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hm0]; norm_num
  have hab : 0 < a * b := mul_pos ha hb
  have h2p : 0 < 2 - p := by linarith
  calc m ^ p / (4 * (2 - p))
      = a * b * (m ^ 2 / (4 * (a * b)) * (m ^ (p - 2) / (2 - p))) := by
        rw [← hmp]; field_simp
    _ ≤ a * b * ∫ s in Ioi 0, concavityKernel p a b s := by
        rw [← hval]
        exact mul_le_mul_of_nonneg_left (hstep1.trans hstep2) hab.le

/-- Pair form of the concavity-gap lower bound: for `0 < p < 1`, `K > 0` and `0 ≤ x, y ≤ γ`,
`K^(p-2)/(4(2-p)) · x^p y^p / γ^p ≤ x y ∫_0^∞ s^(p-1) / ((Kx+s)(Ky+s)) ds`. -/
theorem pair_concavity_integral_ge {p K γ x y : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hK : 0 < K)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxγ : x ≤ γ) (hyγ : y ≤ γ) :
    K ^ (p - 2) / (4 * (2 - p)) * (x ^ p * y ^ p / γ ^ p) ≤
      x * y * ∫ s in Ioi 0, s ^ (p - 1) / ((K * x + s) * (K * y + s)) := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp [Real.zero_rpow hp0.ne']
  rcases hy.eq_or_lt with rfl | hy0
  · simp [Real.zero_rpow hp0.ne']
  have hγ : 0 < γ := hx0.trans_le hxγ
  have hKx : 0 < K * x := mul_pos hK hx0
  have hKy : 0 < K * y := mul_pos hK hy0
  have hmain := mul_integral_concavityKernel_ge hp0 hp1 hKx hKy
  simp only [concavityKernel] at hmain
  have hmin : min (K * x) (K * y) = K * min x y := (mul_min_of_nonneg x y hK.le).symm
  rw [hmin, Real.mul_rpow hK.le (le_min hx hy)] at hmain
  -- `x y ∫ = K^{-2} (Kx)(Ky) ∫`
  have hK2 : x * y = K ^ (-2 : ℝ) * (K * x * (K * y)) := by
    rw [show K * x * (K * y) = K ^ (2 : ℝ) * (x * y) by
      rw [Real.rpow_two]; ring, ← mul_assoc, ← Real.rpow_add hK]; norm_num
  rw [hK2, mul_assoc]
  have hKp : K ^ (p - 2) = K ^ (-2 : ℝ) * K ^ p := by
    rw [← Real.rpow_add hK]; ring_nf
  -- `min(x,y)^p ≥ x^p y^p / γ^p`
  have hminγ : x ^ p * y ^ p / γ ^ p ≤ (min x y) ^ p := by
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hγ _), ← Real.mul_rpow hx hy,
      ← Real.mul_rpow (le_min hx hy) hγ.le]
    refine Real.rpow_le_rpow (mul_nonneg hx hy) ?_ hp0.le
    rcases le_total x y with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have h2p : 0 < 2 - p := by linarith
  calc K ^ (p - 2) / (4 * (2 - p)) * (x ^ p * y ^ p / γ ^ p)
      ≤ K ^ (p - 2) / (4 * (2 - p)) * (min x y) ^ p :=
        mul_le_mul_of_nonneg_left hminγ (by positivity)
    _ = K ^ (-2 : ℝ) * (K ^ p * (min x y) ^ p / (4 * (2 - p))) := by rw [hKp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (by positivity)

/-- Summed concavity-gap lower bound: for `0 < p < 1`, `K > 0` and `0 ≤ λ_i ≤ γ` on a finite set
`S` of retained indices,
`c_{p,K}/γ^p · (Σ_{i∈S} λ_i^p)² ≤ Σ_{i,j∈S} λ_i λ_j ∫_0^∞ s^(p-1)/((Kλ_i+s)(Kλ_j+s)) ds`,
`c_{p,K} = K^(p-2)/(4(2-p))`. -/
theorem sum_concavity_integral_ge {ι : Type*} (S : Finset ι) (lam : ι → ℝ) {p K γ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hK : 0 < K) (hlam : ∀ i ∈ S, 0 ≤ lam i)
    (hlamγ : ∀ i ∈ S, lam i ≤ γ) :
    K ^ (p - 2) / (4 * (2 - p)) / γ ^ p * (∑ i ∈ S, lam i ^ p) ^ 2 ≤
      ∑ i ∈ S, ∑ j ∈ S, lam i * lam j *
        ∫ s in Ioi 0, s ^ (p - 1) / ((K * lam i + s) * (K * lam j + s)) := by
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have := pair_concavity_integral_ge hp0 hp1 hK (hlam i hi) (hlam j hj) (hlamγ i hi)
    (hlamγ j hj)
  calc K ^ (p - 2) / (4 * (2 - p)) / γ ^ p * (lam i ^ p * lam j ^ p)
      = K ^ (p - 2) / (4 * (2 - p)) * (lam i ^ p * lam j ^ p / γ ^ p) := by ring
    _ ≤ _ := this

end BlockBand.Endpoints
