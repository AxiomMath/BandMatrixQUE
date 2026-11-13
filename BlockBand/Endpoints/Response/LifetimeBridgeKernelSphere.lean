module

public import BlockBand.Endpoints.Response.LifetimeBridgeDefs
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

/-!
# The spherical radial factor `pY` of the base heat kernel

In the variable `y = (1 - cos θ)/2 ∈ [0, 1]` the radial generator is
`𝒟_Y = (D₀/2)[y(1-y)∂²_y + (1-2y)∂_y] = (D₀/2)∂_y[y(1-y)∂_y]`, symmetric for `dy` on `[0,1]`.
Its eigenfunctions are the Legendre polynomials `P_n(cos θ) = P_n(1 - 2y)`, i.e. the shifted
Legendre polynomials `P̃_n(y)` (Mathlib `Polynomial.shiftedLegendre`, `P̃_n(0) = 1`), with
`𝒟_Y P̃_n = -(D₀/2) n(n+1) P̃_n` (`lbk_leg_ode`) and `∫_0^1 P̃_n P̃_m dy = δ_{nm}/(2n+1)`.
Hence the transition density of `Y` relative to `dy'` is the Legendre series
`pY_t(y, y') = Σ_n (2n+1) e^{-(D₀/2) n(n+1) t} P̃_n(y) P̃_n(y')` (`lbkSphereSeries`), i.e. the
angle-averaged heat kernel of `(D₀/2)Δ_{S²}` times the area factor `4π` (`dA = 2π sin θ dθ =
4π dy`). `lbkKernelY` is its version with indicators of `t > 0`, `y, y' ∈ [0,1]`.

## Main results

For `D₀ > 0`, `t > 0`, `y, y' ∈ [0,1]`:
* `lbk_leg_ode`: the Legendre equation `(y(1-y)P̃_n')' = -n(n+1)P̃_n` as a polynomial identity;
* `lbk_integral_leg`: `∫_0^1 P̃_n = 0` for `n ≠ 0`;
* `lbk_leg_bound`: `|P̃_n(y)| ≤ 8ⁿ` on `[0,1]` (crude, enough for every series bound);
* `lbk_summable_bound`: the termwise majorant `(2n+1)e^{-(D₀/2)n(n+1)t}64ⁿ` is summable;
* `lbk_sphereSeries_continuousOn`, `lbk_kernelY_continuousOn`: continuity in `y'` on `[0,1]`;
* `lbk_kernelY_measurable`: joint measurability in `(t, y, y')`;
* `lbk_integral_kernelY`: the normalisation `∫ pY_t(y, y') dy' = 1`;
* `lbk_term_eigen`: each series term solves the backward equation
  `∂_t u = (D₀/2)[y(1-y)∂²_y u + (1-2y)∂_y u]` (pointwise derivatives).

Strict positivity `pY_t(y, y') > 0` on `[0,1]²` is the statement `LbkSphereKernelPos`, proved
separately (`lbkSphereKernelPos_holds`). The termwise differentiation of the full series (the
backward equation for `pY` itself, not only its terms) is not done here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Polynomial
open scoped ENNReal

/-!
### Shifted Legendre polynomials over `ℝ`
-/

/-- The shifted Legendre polynomial over `ℝ`: `(lbkLeg n).eval y = P_n(1 - 2y)`. -/
def lbkLeg (n : ℕ) : ℝ[X] := (shiftedLegendre n).map (Int.castRingHom ℝ)

/-- The coefficients `(-1)^k C(n,k) C(n+k,n)` of `lbkLeg n`. -/
def lbkLegCoeff (n k : ℕ) : ℝ := (-1) ^ k * (n.choose k : ℝ) * ((n + k).choose n : ℝ)

theorem lbk_leg_coeff (n k : ℕ) : (lbkLeg n).coeff k = lbkLegCoeff n k := by
  simp [lbkLeg, coeff_shiftedLegendre, lbkLegCoeff]

theorem lbk_legCoeff_rec (n k : ℕ) :
    ((k : ℝ) + 1) ^ 2 * lbkLegCoeff n (k + 1) =
      ((k : ℝ) * (k + 1) - n * (n + 1)) * lbkLegCoeff n k := by
  rcases le_or_gt k n with hk | hk
  · have h1 : (n.choose (k + 1) : ℝ) * (k + 1) = n.choose k * ((n : ℝ) - k) := by
      have := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_succ_right_eq n k)
      push_cast [Nat.cast_sub hk] at this
      exact this
    have h2 : ((n + k).choose n : ℝ) * ((n : ℝ) + k + 1) = (n + k + 1).choose n * ((k : ℝ) + 1) := by
      have := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_mul_succ_eq (n + k) n)
      rw [show n + k + 1 - n = k + 1 by omega] at this
      push_cast at this
      exact this
    have key : ((k : ℝ) + 1) ^ 2 * ((n.choose (k + 1) : ℝ) * ((n + k + 1).choose n : ℝ)) =
        ((n : ℝ) - k) * (n + k + 1) * ((n.choose k : ℝ) * ((n + k).choose n : ℝ)) := by
      calc _ = ((n.choose (k + 1) : ℝ) * (k + 1)) * (((n + k + 1).choose n : ℝ) * (k + 1)) := by
            ring
        _ = _ := by rw [h1, ← h2]; ring
    simp only [lbkLegCoeff, ← add_assoc]
    linear_combination (-(-1 : ℝ) ^ k) * key
  · have h0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt hk
    have h0' : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [lbkLegCoeff, h0, h0']

/-- The Legendre equation for the shifted Legendre polynomials (polynomial identity):
`(y(1-y) P̃_n')' = -n(n+1) P̃_n`, i.e. `y(1-y)P̃_n'' + (1-2y)P̃_n' + n(n+1)P̃_n = 0`. -/
theorem lbk_leg_ode (n : ℕ) :
    derivative ((X - X ^ 2) * derivative (lbkLeg n)) = -(C ((n : ℝ) * (n + 1)) * lbkLeg n) := by
  ext k
  rw [coeff_derivative, coeff_neg, coeff_C_mul, sub_mul, coeff_sub, coeff_X_mul, coeff_X_pow_mul']
  rcases k with _ | j
  · have h2 : ¬ (2 ≤ 0 + 1) := by omega
    simp only [h2, ↓reduceIte, coeff_derivative, lbk_leg_coeff]
    have := lbk_legCoeff_rec n 0
    push_cast at this ⊢
    linear_combination this
  · have h2 : 2 ≤ j + 1 + 1 := by omega
    simp only [h2, ↓reduceIte, show j + 1 + 1 - 2 = j by omega, coeff_derivative, lbk_leg_coeff]
    have := lbk_legCoeff_rec n (j + 1)
    push_cast at this ⊢
    linear_combination this

/-- `∫_0^1 P̃_n = 0` for `n ≠ 0` (orthogonality to the constants), from the Legendre equation. -/
theorem lbk_integral_leg {n : ℕ} (hn : n ≠ 0) : ∫ y in (0 : ℝ)..1, (lbkLeg n).eval y = 0 := by
  set R := (X - X ^ 2) * derivative (lbkLeg n) with hRdef
  have hR : ∫ y in (0 : ℝ)..1, (derivative R).eval y = R.eval 1 - R.eval 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => R.hasDerivAt y)
      ((derivative R).continuous.intervalIntegrable _ _)
  have h0 : R.eval 1 - R.eval 0 = 0 := by simp [hRdef]
  rw [h0, hRdef, lbk_leg_ode] at hR
  simp only [eval_neg, eval_mul, eval_C] at hR
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hR
  have hpos : ((n : ℝ) * (n + 1)) ≠ 0 := by positivity
  have := neg_eq_zero.1 hR
  exact (mul_eq_zero.1 this).resolve_left hpos

theorem lbk_leg_zero (y : ℝ) : (lbkLeg 0).eval y = 1 := by
  simp [lbkLeg, shiftedLegendre]

theorem lbk_leg_bound (n : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : |(lbkLeg n).eval y| ≤ 8 ^ n := by
  have hdeg : (lbkLeg n).natDegree < n + 1 :=
    Nat.lt_succ_of_le ((natDegree_map_le).trans (natDegree_shiftedLegendre n).le)
  have hy1 : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  calc |(lbkLeg n).eval y| = |∑ i ∈ Finset.range (n + 1), (lbkLeg n).coeff i * y ^ i| := by
        rw [eval_eq_sum_range' hdeg]
    _ ≤ ∑ i ∈ Finset.range (n + 1), |(lbkLeg n).coeff i * y ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * 4 ^ n := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [lbk_leg_coeff, lbkLegCoeff, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
          one_pow, one_mul, Nat.abs_cast, Nat.abs_cast, abs_pow]
        have hy' : |y| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg y) hy1
        have hc : ((n + i).choose n : ℝ) ≤ 4 ^ n := by
          have h1 := Nat.choose_le_two_pow (n + i) n
          have h2 : 2 ^ (n + i) ≤ 4 ^ n := by
            rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
            exact Nat.pow_le_pow_right (by norm_num) (by have := Finset.mem_range.1 hi; omega)
          exact_mod_cast h1.trans h2
        calc (n.choose i : ℝ) * ((n + i).choose n) * |y| ^ i
            ≤ (n.choose i : ℝ) * ((n + i).choose n) * 1 := by gcongr
          _ ≤ _ := by rw [mul_one]; gcongr
    _ = 8 ^ n := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this, ← mul_pow]
        norm_num

/-!
### The Legendre series
-/

/-- The `n`-th term `(2n+1) e^{-(D₀/2)n(n+1)t} P̃_n(y) P̃_n(y')` of the spherical kernel. -/
def lbkYTerm (D0 t y y' : ℝ) (n : ℕ) : ℝ :=
  (2 * n + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * (lbkLeg n).eval y *
    (lbkLeg n).eval y'

/-- The termwise majorant on `[0,1]²`. -/
def lbkYBound (D0 t : ℝ) (n : ℕ) : ℝ :=
  (2 * n + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * 64 ^ n

/-- The spherical radial heat kernel `pY_t(y, y') = Σ_n (2n+1)e^{-(D₀/2)n(n+1)t}P̃_n(y)P̃_n(y')`
(density relative to `dy'` of `Y_t` started at `y`). -/
def lbkSphereSeries (D0 t y y' : ℝ) : ℝ := ∑' n, lbkYTerm D0 t y y' n

/-- The version of `pY` used in the product kernel: the series for `t > 0`, `y, y' ∈ [0,1]`,
and `0` otherwise. -/
def lbkKernelY (D0 : ℝ) (t y y' : ℝ) : ℝ :=
  if 0 < t ∧ y ∈ Icc (0 : ℝ) 1 ∧ y' ∈ Icc (0 : ℝ) 1 then lbkSphereSeries D0 t y y' else 0

theorem lbk_term_le {D0 t y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    ‖lbkYTerm D0 t y y' n‖ ≤ lbkYBound D0 t n := by
  have h1 := lbk_leg_bound n hy
  have h2 := lbk_leg_bound n hy'
  have hc : 0 ≤ (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) := by positivity
  rw [Real.norm_eq_abs, lbkYTerm, abs_mul, abs_mul, abs_of_nonneg hc, lbkYBound, mul_assoc,
    show (64 : ℝ) ^ n = 8 ^ n * 8 ^ n by rw [← mul_pow]; norm_num]
  gcongr

theorem lbk_summable_bound {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) :
    Summable (lbkYBound D0 t) := by
  have hg : Summable fun n : ℕ => (2 * (n : ℝ) + 1) * (1 / 2 : ℝ) ^ n := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
    have h0 := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    convert (h1.mul_left 2).add h0 using 1
    funext n
    simp
    ring
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  have hlim : Tendsto (fun n : ℕ => 64 * Real.exp (-(D0 / 2 * ((n : ℝ) + 1) * t))) atTop (𝓝 0) := by
    have hc : 0 < D0 / 2 * t := by positivity
    have : Tendsto (fun n : ℕ => -(D0 / 2 * ((n : ℝ) + 1) * t)) atTop atBot := by
      have h := Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
      have h' := h.const_mul_atTop hc
      refine (tendsto_neg_atTop_atBot.comp h').congr fun n => ?_
      simp only [Function.comp]
      ring
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul 64
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
  have hexp : Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * 64 ^ n =
      (64 * Real.exp (-(D0 / 2 * ((n : ℝ) + 1) * t))) ^ n := by
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm]
    congr 2
    ring
  have hb : 0 ≤ lbkYBound D0 t n := by unfold lbkYBound; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hb, lbkYBound, mul_assoc, hexp]
  gcongr

theorem lbk_summable_term {D0 t y y' : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hy : y ∈ Icc (0 : ℝ) 1)
    (hy' : y' ∈ Icc (0 : ℝ) 1) : Summable (lbkYTerm D0 t y y') :=
  Summable.of_norm_bounded (lbk_summable_bound hD0 ht) (lbk_term_le hy hy')

theorem lbk_term_continuous (D0 : ℝ) (n : ℕ) :
    Continuous fun w : ℝ × ℝ × ℝ => lbkYTerm D0 w.1 w.2.1 w.2.2 n := by
  unfold lbkYTerm
  have h1 : Continuous fun w : ℝ × ℝ × ℝ => (lbkLeg n).eval w.2.1 :=
    (lbkLeg n).continuous.comp (by fun_prop)
  have h2 : Continuous fun w : ℝ × ℝ × ℝ => (lbkLeg n).eval w.2.2 :=
    (lbkLeg n).continuous.comp (by fun_prop)
  have h0 : Continuous fun w : ℝ × ℝ × ℝ => Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * w.1)) := by
    fun_prop
  exact ((continuous_const.mul h0).mul h1).mul h2

theorem lbk_sphereSeries_continuousOn {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) : ContinuousOn (lbkSphereSeries D0 t y) (Icc 0 1) := by
  refine continuousOn_tsum (fun n => ?_) (lbk_summable_bound hD0 ht)
    (fun n y' hy' => lbk_term_le hy hy' n)
  exact ((lbk_term_continuous D0 n).comp (continuous_const.prodMk
    (continuous_const.prodMk continuous_id) : Continuous fun y' : ℝ => (t, y, y'))).continuousOn

theorem lbk_kernelY_eq {D0 t y y' : ℝ} (ht : 0 < t) (hy : y ∈ Icc (0 : ℝ) 1)
    (hy' : y' ∈ Icc (0 : ℝ) 1) : lbkKernelY D0 t y y' = lbkSphereSeries D0 t y y' := by
  simp [lbkKernelY, ht, hy, hy']

theorem lbk_kernelY_eq_indicator {D0 t y : ℝ} (ht : 0 < t) (hy : y ∈ Icc (0 : ℝ) 1) :
    lbkKernelY D0 t y = (Icc (0 : ℝ) 1).indicator (lbkSphereSeries D0 t y) := by
  funext y'
  by_cases hy' : y' ∈ Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hy', lbk_kernelY_eq ht hy hy']
  · rw [Set.indicator_of_notMem hy']
    simp [lbkKernelY, hy']

theorem lbk_kernelY_continuousOn {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) : ContinuousOn (lbkKernelY D0 t y) (Icc 0 1) :=
  (lbk_sphereSeries_continuousOn hD0 ht hy).congr fun _ hy' => lbk_kernelY_eq ht hy hy'

theorem lbk_kernelY_measurable {D0 : ℝ} (hD0 : 0 < D0) :
    Measurable fun w : ℝ × ℝ × ℝ => lbkKernelY D0 w.1 w.2.1 w.2.2 := by
  classical
  set S : Set (ℝ × ℝ × ℝ) := {w | 0 < w.1 ∧ w.2.1 ∈ Icc (0 : ℝ) 1 ∧ w.2.2 ∈ Icc (0 : ℝ) 1}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_Icc.preimage (measurable_fst.comp measurable_snd)).inter
        (measurableSet_Icc.preimage (measurable_snd.comp measurable_snd)))
  refine measurable_of_tendsto_metrizable (f := fun N w => if w ∈ S then
    ∑ n ∈ Finset.range N, lbkYTerm D0 w.1 w.2.1 w.2.2 n else 0) (fun N => ?_) ?_
  · exact Measurable.ite hS (Finset.measurable_sum _ fun n _ =>
      (lbk_term_continuous D0 n).measurable) measurable_const
  · refine tendsto_pi_nhds.2 fun w => ?_
    by_cases hw : w ∈ S
    · have hw' : 0 < w.1 ∧ w.2.1 ∈ Icc (0 : ℝ) 1 ∧ w.2.2 ∈ Icc (0 : ℝ) 1 := hw
      simp only [hw, lbkKernelY, hw', and_self, ↓reduceIte]
      exact (lbk_summable_term hD0 hw.1 hw.2.1 hw.2.2).hasSum.tendsto_sum_nat
    · have hw' : ¬ (0 < w.1 ∧ w.2.1 ∈ Icc (0 : ℝ) 1 ∧ w.2.2 ∈ Icc (0 : ℝ) 1) := hw
      simp only [hw, lbkKernelY, hw', ↓reduceIte]
      exact tendsto_const_nhds

/-- Normalisation: `∫ pY_t(y, y') dy' = 1` for `t > 0`, `y ∈ [0, 1]`. -/
theorem lbk_integral_kernelY {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hy : y ∈ Icc (0 : ℝ) 1) :
    ∫ y', lbkKernelY D0 t y y' = 1 := by
  rw [lbk_kernelY_eq_indicator ht hy, integral_indicator measurableSet_Icc]
  have hint : ∀ n, Integrable (fun y' => lbkYTerm D0 t y y' n) (volume.restrict (Icc 0 1)) :=
    fun n => ((lbk_term_continuous D0 n).comp (continuous_const.prodMk
      (continuous_const.prodMk continuous_id) : Continuous fun y' : ℝ => (t, y, y'))).integrableOn_Icc
  have hsum : Summable fun n => ∫ y' in Icc (0 : ℝ) 1, ‖lbkYTerm D0 t y y' n‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (lbk_summable_bound hD0 ht)
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : ℝ) 1)
      (f := fun y' => ‖lbkYTerm D0 t y y' n‖) (C := lbkYBound D0 t n) (by simp)
      (fun y' hy' => by rw [norm_norm]; exact lbk_term_le hy hy' n)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at this
    simpa using this
  unfold lbkSphereSeries
  rw [← integral_tsum_of_summable_integral_norm hint hsum, tsum_eq_single 0]
  · simp [lbkYTerm, lbk_leg_zero]
  · intro n hn
    have h0 : ∫ y' in Icc (0 : ℝ) 1, (lbkLeg n).eval y' = 0 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
      exact lbk_integral_leg hn
    simp only [lbkYTerm]
    rw [integral_const_mul, h0, mul_zero]

/-!
### Each term solves the backward equation
-/

/-- Each Legendre term solves the backward equation of `Y`: for
`u(t, y) = e^{-(D₀/2)n(n+1)t} P̃_n(y)`, `∂_t u = (D₀/2)[y(1-y)∂²_y u + (1-2y)∂_y u]`. -/
theorem lbk_term_eigen (D0 : ℝ) (n : ℕ) (t y : ℝ) :
    deriv (fun s => Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * s)) * (lbkLeg n).eval y) t =
      D0 / 2 * (y * (1 - y) * (Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) *
          (derivative (derivative (lbkLeg n))).eval y) +
        (1 - 2 * y) * (Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) *
          (derivative (lbkLeg n)).eval y)) := by
  have hode := congrArg (Polynomial.eval y) (lbk_leg_ode n)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_X_pow, eval_add, eval_mul,
    eval_sub, eval_X, eval_pow, eval_one, eval_neg, eval_C] at hode
  have hd : HasDerivAt (fun s => Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * s)) *
      (lbkLeg n).eval y) (Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) *
        (-(D0 / 2 * ((n : ℝ) * (n + 1)))) * (lbkLeg n).eval y) t := by
    have := ((hasDerivAt_id t).const_mul (D0 / 2 * ((n : ℝ) * (n + 1)))).neg.exp
    refine (this.mul_const _).congr_deriv ?_
    simp
  rw [hd.deriv]
  push_cast at hode
  linear_combination (-(D0 / 2) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t))) * hode

end BlockBand.Endpoints
