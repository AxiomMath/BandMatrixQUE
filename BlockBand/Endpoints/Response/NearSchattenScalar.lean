module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Scalar kernels of the regularized fractional decay

A clock trace measure `μ = Σ_i λ_i δ_{λ_i}` integrates `k(x)` to `Σ_i λ_i k(λ_i)`, so a trace
functional `Tr f(A)` with `f(0) = 0` is `∫ f(x)/x dμ`. The kernels below are the quotients by
`x` of the functions used in the decay proof:

* `nsRegKernel p ε x = f_ε(x)/x`, `f_ε(x) = (x+ε)^p - ε^p`, continuously extended by
  `f_ε'(0) = p ε^{p-1}` at `x ≤ 0` (as `dslope`);
* `nsDissKernel p ε x = x (x+ε)^{p-2}`, the quotient of the dissipation `x²(x+ε)^{p-2}` of the
  first two generator terms;
* `nsCutKernel a r x = (max x a)^r`, `r < 0`: bounded continuous minorants of `x^r` (`x > 0`).

## Main results

* `ns_regKernel_le_dissKernel_add`: the power regularization bound divided by `x`,
  `f_ε(x)/x ≤ x(x+ε)^{p-2} + 2ε^{p-p₀} x^{p₀-1}` for `x > 0`, `0 < p₀ < p < 1` (the constant
  `C_{p,p₀}` is `2`), by the case split `x ≤ ε` / `x ≥ ε`;
* `ns_ennreal_regKernel_le`: the same in `ℝ≥0∞` for every real `x` (`0^{p₀-1} = ∞`);
* the bound `f_ε(x)/x ≤ x^{p-1}` (`ns_regKernel_le_rpow`) and the pointwise limit `ε ↓ 0` in
  `ℝ≥0∞` along `ε_n = 1/(n+1)` (`ns_tendsto_regKernel`: `f_{ε_n}(x)/x → x^{p-1}`, `→ ∞` at
  `x ≤ 0`);
* the same pointwise limit for the cut kernels (`ns_tendsto_cutKernel`);
* continuity of the three kernels (`ns_continuous_regKernel`, `ns_continuous_dissKernel`,
  `ns_continuous_cutKernel`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Filter Topology Set
open scoped ENNReal

/-!
## Definitions
-/

/-- The regularized power `x ↦ (x + ε)^p` whose difference quotient at `0` is the kernel. -/
def nsShiftPow (p ε : ℝ) (x : ℝ) : ℝ := (x + ε) ^ p

/-- `f_ε(x)/x` with `f_ε(x) = (x+ε)^p - ε^p`, extended by `f_ε'(0) = pε^{p-1}` at `x ≤ 0`
(through `max x 0`). -/
def nsRegKernel (p ε : ℝ) (x : ℝ) : ℝ := dslope (nsShiftPow p ε) 0 (max x 0)

/-- `x (x+ε)^{p-2}` (`x ≥ 0`), the quotient by `x` of the dissipation `x²(x+ε)^{p-2}`. -/
def nsDissKernel (p ε : ℝ) (x : ℝ) : ℝ := max x 0 * (max x 0 + ε) ^ (p - 2)

/-- `(max x a)^r`: for `a > 0`, `r < 0` a bounded continuous minorant of `x^r` on `x > 0`. -/
def nsCutKernel (a r : ℝ) (x : ℝ) : ℝ := (max x a) ^ r

/-!
## Values of the regularized kernel
-/

theorem ns_hasDerivAt_shiftPow {p ε : ℝ} {x : ℝ} (hx : -ε < x) :
    HasDerivAt (nsShiftPow p ε) (p * (x + ε) ^ (p - 1)) x := by
  have hne : x + ε ≠ 0 := ne_of_gt (by linarith)
  have h := ((hasDerivAt_id' x).add_const ε).rpow_const (p := p) (Or.inl hne)
  show HasDerivAt (fun y => (y + ε) ^ p) _ x
  simpa using h

theorem ns_regKernel_of_pos {p ε x : ℝ} (hx : 0 < x) :
    nsRegKernel p ε x = ((x + ε) ^ p - ε ^ p) / x := by
  rw [nsRegKernel, max_eq_left hx.le, dslope_of_ne _ hx.ne', slope_def_field]
  simp [nsShiftPow]

theorem ns_regKernel_of_nonpos {p ε x : ℝ} (hε : 0 < ε) (hx : x ≤ 0) :
    nsRegKernel p ε x = p * ε ^ (p - 1) := by
  rw [nsRegKernel, max_eq_right hx, dslope_same, (ns_hasDerivAt_shiftPow (neg_lt_zero.2 hε)).deriv,
    zero_add]

theorem ns_regKernel_nonneg {p ε : ℝ} (hp : 0 ≤ p) (hε : 0 < ε) (x : ℝ) :
    0 ≤ nsRegKernel p ε x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [ns_regKernel_of_nonpos hε hx]; exact mul_nonneg hp (Real.rpow_nonneg hε.le _)
  · rw [ns_regKernel_of_pos hx]
    refine div_nonneg (sub_nonneg.2 ?_) hx.le
    exact Real.rpow_le_rpow hε.le (by linarith) hp

theorem ns_continuous_regKernel {p ε : ℝ} (hε : 0 < ε) : Continuous (nsRegKernel p ε) := by
  have hs : Ioi (-ε) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (neg_lt_zero.2 hε)
  have hc : ContinuousOn (dslope (nsShiftPow p ε) 0) (Ioi (-ε)) := by
    refine (continuousOn_dslope hs).2 ⟨fun x hx => ?_, ?_⟩
    · exact (ns_hasDerivAt_shiftPow (mem_Ioi.1 hx)).continuousAt.continuousWithinAt
    · exact (ns_hasDerivAt_shiftPow (neg_lt_zero.2 hε)).differentiableAt
  have hm : Continuous fun x : ℝ => max x 0 := continuous_id.max continuous_const
  refine hc.comp_continuous hm fun x => ?_
  exact mem_Ioi.2 (lt_of_lt_of_le (neg_lt_zero.2 hε) (le_max_right _ _))

theorem ns_continuous_dissKernel {p ε : ℝ} (hε : 0 < ε) : Continuous (nsDissKernel p ε) := by
  have hm : Continuous fun x : ℝ => max x 0 := continuous_id.max continuous_const
  refine hm.mul (Continuous.rpow_const (hm.add continuous_const) fun x => Or.inl ?_)
  have := le_max_right x 0
  linarith

theorem ns_dissKernel_nonneg {p ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ nsDissKernel p ε x :=
  mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by linarith [le_max_right x 0]) _)

theorem ns_continuous_cutKernel {a r : ℝ} (ha : 0 < a) : Continuous (nsCutKernel a r) := by
  refine Continuous.rpow_const (continuous_id.max continuous_const) fun x => Or.inl ?_
  exact (lt_of_lt_of_le ha (le_max_right _ _)).ne'

theorem ns_cutKernel_nonneg {a r : ℝ} (ha : 0 < a) (x : ℝ) : 0 ≤ nsCutKernel a r x :=
  Real.rpow_nonneg (ha.le.trans (le_max_right _ _)) _

theorem ns_cutKernel_le {a r : ℝ} (ha : 0 < a) (hr : r ≤ 0) (x : ℝ) : nsCutKernel a r x ≤ a ^ r :=
  Real.rpow_le_rpow_of_nonpos ha (le_max_right _ _) hr

/-- For `x > 0` and `r ≤ 0`, `(max x a)^r ≤ x^r`. -/
theorem ns_cutKernel_le_rpow {a r x : ℝ} (hx : 0 < x) (hr : r ≤ 0) : nsCutKernel a r x ≤ x ^ r :=
  Real.rpow_le_rpow_of_nonpos hx (le_max_left _ _) hr

/-!
## The power regularization bound
-/

/-- Tangent-line bound of the concave power: `(x+ε)^p - ε^p ≤ p ε^{p-1} x` (`x ≥ 0`). -/
theorem ns_shiftPow_sub_le {p ε x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hx : 0 ≤ x) :
    (x + ε) ^ p - ε ^ p ≤ p * ε ^ (p - 1) * x := by
  have hb := rpow_one_add_le_one_add_mul_self (s := x / ε) (by
    have : 0 ≤ x / ε := div_nonneg hx hε.le
    linarith) hp0 hp1
  have hxe : x + ε = ε * (1 + x / ε) := by field_simp; ring
  rw [hxe, Real.mul_rpow hε.le (by positivity)]
  have hpow : ε ^ (p - 1) = ε ^ p * ε⁻¹ := by
    rw [Real.rpow_sub_one hε.ne', div_eq_mul_inv]
  have hεp : 0 ≤ ε ^ p := Real.rpow_nonneg hε.le _
  calc ε ^ p * (1 + x / ε) ^ p - ε ^ p ≤ ε ^ p * (1 + p * (x / ε)) - ε ^ p := by
        gcongr
    _ = p * ε ^ (p - 1) * x := by rw [hpow]; field_simp; ring

/-- The power regularization bound, multiplied form: for `x ≥ 0`, `0 < p₀ < p < 1`, `ε > 0`,
`f_ε(x) - x²(x+ε)^{p-2} ≤ 2 ε^{p-p₀} x^{p₀}` (`C_{p,p₀} = 2`; case split `x ≤ ε` / `x ≥ ε`). -/
theorem ns_clock_power_regularization {p p₀ ε x : ℝ} (hp₀ : 0 < p₀) (hp₀p : p₀ < p)
    (hp1 : p < 1) (hε : 0 < ε) (hx : 0 ≤ x) :
    (x + ε) ^ p - ε ^ p - x ^ 2 * (x + ε) ^ (p - 2) ≤ 2 * ε ^ (p - p₀) * x ^ p₀ := by
  have hxε : 0 < x + ε := by linarith
  have hdiss : 0 ≤ x ^ 2 * (x + ε) ^ (p - 2) := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hxε.le _)
  rcases le_total x ε with hle | hge
  · -- `x ≤ ε`: `f_ε(x) ≤ p ε^{p-1} x ≤ ε^{p-p₀} x^{p₀}`
    have h1 := ns_shiftPow_sub_le (by linarith : (0 : ℝ) ≤ p) hp1.le hε hx
    rcases hx.eq_or_lt with rfl | hx0
    · simp only [zero_add, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_mul, Real.zero_rpow hp₀.ne', mul_zero, le_refl]
    have hsplit : x = x ^ (1 - p₀) * x ^ p₀ := by
      rw [← Real.rpow_add hx0]; simp
    have hx1 : x ^ (1 - p₀) ≤ ε ^ (1 - p₀) :=
      Real.rpow_le_rpow hx hle (by linarith)
    have hεe : ε ^ (p - 1) * ε ^ (1 - p₀) = ε ^ (p - p₀) := by
      rw [← Real.rpow_add hε]; ring_nf
    have hxp : 0 ≤ x ^ p₀ := Real.rpow_nonneg hx _
    have hεp1 : 0 ≤ ε ^ (p - 1) := Real.rpow_nonneg hε.le _
    have hεpp : 0 ≤ ε ^ (p - p₀) := Real.rpow_nonneg hε.le _
    calc (x + ε) ^ p - ε ^ p - x ^ 2 * (x + ε) ^ (p - 2) ≤ p * ε ^ (p - 1) * x := by linarith
      _ = p * (ε ^ (p - 1) * x ^ (1 - p₀)) * x ^ p₀ := by
          conv_lhs => rw [hsplit]
          ring
      _ ≤ 1 * (ε ^ (p - 1) * ε ^ (1 - p₀)) * x ^ p₀ := by
          gcongr
      _ ≤ 2 * ε ^ (p - p₀) * x ^ p₀ := by
          rw [hεe, one_mul]
          nlinarith
  · -- `x ≥ ε`: the difference is at most `2ε(x+ε)^{p-1} ≤ 2ε x^{p-1} ≤ 2ε^{p-p₀} x^{p₀}`
    have hx0 : 0 < x := lt_of_lt_of_le hε hge
    have hsplit : (x + ε) ^ p = (x + ε) ^ (p - 2) * (x + ε) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hxε]; norm_num
    have hsplit1 : (x + ε) ^ (p - 1) = (x + ε) ^ (p - 2) * (x + ε) := by
      rw [← Real.rpow_add_one hxε.ne']; ring_nf
    have hq : 0 ≤ (x + ε) ^ (p - 2) := Real.rpow_nonneg hxε.le _
    have hstep1 : (x + ε) ^ p - ε ^ p - x ^ 2 * (x + ε) ^ (p - 2) ≤ 2 * ε * (x + ε) ^ (p - 1) := by
      rw [hsplit, hsplit1]
      have : 0 ≤ ε ^ p := Real.rpow_nonneg hε.le _
      have hsq : (x + ε) ^ (p - 2) * (x + ε) ^ 2 - x ^ 2 * (x + ε) ^ (p - 2) =
          (x + ε) ^ (p - 2) * (2 * x * ε + ε ^ 2) := by ring
      have hle : (x + ε) ^ (p - 2) * (2 * x * ε + ε ^ 2) ≤ 2 * ε * ((x + ε) ^ (p - 2) * (x + ε)) := by
        have : (x + ε) ^ (p - 2) * ε ^ 2 ≥ 0 := mul_nonneg hq (sq_nonneg _)
        nlinarith
      linarith
    have hstep2 : (x + ε) ^ (p - 1) ≤ x ^ (p - 1) :=
      Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
    have hsplit2 : x ^ (p - 1) = x ^ (p - 1 - p₀) * x ^ p₀ := by
      rw [← Real.rpow_add hx0]; ring_nf
    have hstep3 : x ^ (p - 1 - p₀) ≤ ε ^ (p - 1 - p₀) :=
      Real.rpow_le_rpow_of_nonpos hε hge (by linarith)
    have hεe : ε * ε ^ (p - 1 - p₀) = ε ^ (p - p₀) := by
      rw [← Real.rpow_one_add' hε.le (by linarith)]; ring_nf
    have hxp : 0 ≤ x ^ p₀ := Real.rpow_nonneg hx _
    calc (x + ε) ^ p - ε ^ p - x ^ 2 * (x + ε) ^ (p - 2) ≤ 2 * ε * (x + ε) ^ (p - 1) := hstep1
      _ ≤ 2 * ε * (x ^ (p - 1 - p₀) * x ^ p₀) := by
          rw [← hsplit2]; gcongr
      _ ≤ 2 * ε * (ε ^ (p - 1 - p₀) * x ^ p₀) := by gcongr
      _ = 2 * ε ^ (p - p₀) * x ^ p₀ := by rw [← hεe]; ring

/-- The power regularization bound divided by `x` (kernel form, `x > 0`):
`f_ε(x)/x ≤ x(x+ε)^{p-2} + 2ε^{p-p₀} x^{p₀-1}`. -/
theorem ns_regKernel_le_dissKernel_add {p p₀ ε x : ℝ} (hp₀ : 0 < p₀) (hp₀p : p₀ < p)
    (hp1 : p < 1) (hε : 0 < ε) (hx : 0 < x) :
    nsRegKernel p ε x ≤ nsDissKernel p ε x + 2 * ε ^ (p - p₀) * x ^ (p₀ - 1) := by
  have h := ns_clock_power_regularization hp₀ hp₀p hp1 hε hx.le
  rw [ns_regKernel_of_pos hx, nsDissKernel, max_eq_left hx.le, div_le_iff₀ hx]
  have hxp : x ^ (p₀ - 1) * x = x ^ p₀ := by
    rw [← Real.rpow_add_one hx.ne']; ring_nf
  have : x * (x + ε) ^ (p - 2) * x = x ^ 2 * (x + ε) ^ (p - 2) := by ring
  calc (x + ε) ^ p - ε ^ p ≤ x ^ 2 * (x + ε) ^ (p - 2) + 2 * ε ^ (p - p₀) * x ^ p₀ := by linarith
    _ = (x * (x + ε) ^ (p - 2) + 2 * ε ^ (p - p₀) * x ^ (p₀ - 1)) * x := by
        rw [add_mul, this, mul_assoc (2 * ε ^ (p - p₀)), hxp]

/-- The kernel bound in `ℝ≥0∞`, for every real `x` (`(ofReal x)^{p₀-1} = ∞` at `x ≤ 0`). -/
theorem ns_ennreal_regKernel_le {p p₀ ε : ℝ} (hp₀ : 0 < p₀) (hp₀p : p₀ < p) (hp1 : p < 1)
    (hε : 0 < ε) (x : ℝ) :
    ENNReal.ofReal (nsRegKernel p ε x) ≤ ENNReal.ofReal (nsDissKernel p ε x) +
      ENNReal.ofReal (2 * ε ^ (p - p₀)) * ENNReal.ofReal x ^ (p₀ - 1) := by
  have hc : 0 < 2 * ε ^ (p - p₀) := by positivity
  rcases le_or_gt x 0 with hx | hx
  · rw [ENNReal.ofReal_of_nonpos hx, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne', add_top]
    exact le_top
  · rw [ENNReal.ofReal_rpow_of_pos hx, ← ENNReal.ofReal_mul hc.le,
      ← ENNReal.ofReal_add (ns_dissKernel_nonneg hε x) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by
      have := ns_regKernel_le_dissKernel_add hp₀ hp₀p hp1 hε hx
      linarith [mul_assoc 2 (ε ^ (p - p₀)) (x ^ (p₀ - 1))])

/-!
## The limit `ε ↓ 0`
-/

/-- `f_ε(x)/x ≤ x^{p-1}` for `x > 0` (subadditivity `(x+ε)^p ≤ x^p + ε^p`, `0 ≤ p ≤ 1`). -/
theorem ns_regKernel_le_rpow {p ε x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hx : 0 < x) :
    nsRegKernel p ε x ≤ x ^ (p - 1) := by
  have h := NNReal.coe_le_coe.2 (NNReal.rpow_add_le_add_rpow x.toNNReal ε.toNNReal hp0 hp1)
  push_cast [NNReal.coe_rpow, Real.coe_toNNReal _ hx.le, Real.coe_toNNReal _ hε.le] at h
  rw [ns_regKernel_of_pos hx, div_le_iff₀ hx, ← Real.rpow_add_one hx.ne']
  simp only [sub_add_cancel]
  linarith

/-- The regularization parameters `ε_n = 1/(n+1) ↓ 0`. -/
def nsEps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem ns_eps_pos (n : ℕ) : 0 < nsEps n := by unfold nsEps; positivity

theorem ns_tendsto_eps : Tendsto nsEps atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall ns_eps_pos⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- `p ε_n^{p-1} → ∞` in `ℝ≥0∞` (`0 < p < 1`). -/
theorem ns_tendsto_eps_rpow_top {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => ENNReal.ofReal (p * nsEps n ^ (p - 1))) atTop (𝓝 ⊤) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (1 - p)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h2 := (h.const_mul_atTop hp0)
  refine (ENNReal.tendsto_ofReal_atTop.comp h2).congr fun n => ?_
  simp only [Function.comp_apply, nsEps]
  congr 2
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  ring_nf

/-- Pointwise limit `ε ↓ 0` of the regularized kernel in `ℝ≥0∞`:
`f_{ε_n}(x)/x → x^{p-1}` (`x > 0`) and `→ ∞` (`x ≤ 0`), i.e. `→ (ofReal x)^{p-1}`. -/
theorem ns_tendsto_regKernel {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) :
    Tendsto (fun n => ENNReal.ofReal (nsRegKernel p (nsEps n) x)) atTop
      (𝓝 (ENNReal.ofReal x ^ (p - 1))) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [ENNReal.ofReal_of_nonpos hx, ENNReal.zero_rpow_of_neg (by linarith)]
    refine (ns_tendsto_eps_rpow_top hp0 hp1).congr fun n => ?_
    rw [ns_regKernel_of_nonpos (ns_eps_pos n) hx]
  · rw [ENNReal.ofReal_rpow_of_pos hx]
    refine ENNReal.tendsto_ofReal ?_
    have hc : ContinuousWithinAt (fun e : ℝ => ((x + e) ^ p - e ^ p) / x) (Ioi 0) 0 := by
      refine ContinuousAt.continuousWithinAt ?_
      refine ((Real.continuousAt_rpow_const _ _ (Or.inl (by simpa using hx.ne'))).comp
        (continuousAt_const.add continuousAt_id)).sub
        (Real.continuousAt_rpow_const _ _ (Or.inr hp0.le)) |>.div_const _
    have hlim := hc.tendsto.comp ns_tendsto_eps
    have hval : ((x + 0) ^ p - (0 : ℝ) ^ p) / x = x ^ (p - 1) := by
      rw [add_zero, Real.zero_rpow hp0.ne', sub_zero, Real.rpow_sub_one hx.ne']
    rw [hval] at hlim
    refine hlim.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [ns_regKernel_of_pos hx]

/-- Pointwise limit of the cut kernels in `ℝ≥0∞` (`r < 0`, `a_m = ε_m ↓ 0`):
`(max x ε_m)^r → (ofReal x)^r` (`= ∞` at `x ≤ 0`). -/
theorem ns_tendsto_cutKernel {r : ℝ} (hr : r < 0) (x : ℝ) :
    Tendsto (fun m => ENNReal.ofReal (nsCutKernel (nsEps m) r x)) atTop
      (𝓝 (ENNReal.ofReal x ^ r)) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [ENNReal.ofReal_of_nonpos hx, ENNReal.zero_rpow_of_neg hr]
    have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-r)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    refine (ENNReal.tendsto_ofReal_atTop.comp h).congr fun n => ?_
    simp only [Function.comp_apply, nsCutKernel]
    rw [max_eq_right (hx.trans (ns_eps_pos n).le), nsEps, one_div,
      Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  · rw [ENNReal.ofReal_rpow_of_pos hx]
    refine tendsto_const_nhds.congr' ?_
    have hev : ∀ᶠ m in atTop, nsEps m < x :=
      (tendsto_nhdsWithin_iff.1 ns_tendsto_eps).1.eventually (gt_mem_nhds hx)
    filter_upwards [hev] with m hm
    rw [nsCutKernel, max_eq_left hm.le]

end BlockBand.Endpoints
