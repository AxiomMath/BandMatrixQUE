module

public import BlockBand.Endpoints.Response.LifetimeBridgeSpherePosIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Unique continuation for the spherical kernel

For `D₀ > 0`, `t > 0`, `y ∈ [0,1]`, the Legendre series `w ↦ k_t(y, w)` extends to the
holomorphic function `lbkpSeriesC D0 t y` on the disc `|z| < 2` (the coefficients decay like
`e^{-(D₀/2)n(n+1)t}` while `|P̃_n(z)| ≤ 16ⁿ` there). By the identity theorem
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`), if `k_t(y, ·)` vanishes on
a nondegenerate subinterval of `[0,1]`, it vanishes on all of `[0,1]`
(`lbkp_series_unique_continuation`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Polynomial Metric

/-- The summable majorant `(2n+1) e^{-(D₀/2)n(n+1)t} Kⁿ` for any `K ≥ 0`. -/
theorem lbkp_summable_bound_gen {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) {K : ℝ} (hK : 0 ≤ K) :
    Summable fun n : ℕ => (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) *
      K ^ n := by
  have hg : Summable fun n : ℕ => (2 * (n : ℝ) + 1) * (1 / 2 : ℝ) ^ n := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
    have h0 := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    convert (h1.mul_left 2).add h0 using 1
    funext n
    simp
    ring
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  have hlim : Tendsto (fun n : ℕ => K * Real.exp (-(D0 / 2 * ((n : ℝ) + 1) * t))) atTop
      (𝓝 0) := by
    have hc : 0 < D0 / 2 * t := by positivity
    have : Tendsto (fun n : ℕ => -(D0 / 2 * ((n : ℝ) + 1) * t)) atTop atBot := by
      have h := Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
      have h' := h.const_mul_atTop hc
      refine (tendsto_neg_atTop_atBot.comp h').congr fun n => ?_
      simp only [Function.comp]
      ring
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul K
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
  have hexp : Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * K ^ n =
      (K * Real.exp (-(D0 / 2 * ((n : ℝ) + 1) * t))) ^ n := by
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm]
    congr 2
    ring
  have hb : 0 ≤ (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * K ^ n := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hb, mul_assoc, hexp]
  have h0 : 0 ≤ K * Real.exp (-(D0 / 2 * ((n : ℝ) + 1) * t)) := by positivity
  gcongr

/-- The complexified shifted Legendre polynomial. -/
def lbkpLegC (n : ℕ) : ℂ[X] := (lbkLeg n).map Complex.ofRealHom

theorem lbkp_legC_eval_ofReal (n : ℕ) (w : ℝ) :
    (lbkpLegC n).eval (w : ℂ) = (((lbkLeg n).eval w : ℝ) : ℂ) := by
  rw [lbkpLegC, eval_map]
  exact eval₂_at_apply Complex.ofRealHom w

theorem lbkp_legC_bound (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 2) : ‖(lbkpLegC n).eval z‖ ≤ 16 ^ n := by
  have hdeg : (lbkpLegC n).natDegree < n + 1 :=
    Nat.lt_succ_of_le (natDegree_map_le.trans (lbkp_leg_natDegree_le n))
  calc ‖(lbkpLegC n).eval z‖ = ‖∑ i ∈ Finset.range (n + 1), (lbkpLegC n).coeff i * z ^ i‖ := by
        rw [eval_eq_sum_range' hdeg]
    _ ≤ ∑ i ∈ Finset.range (n + 1), ‖(lbkpLegC n).coeff i * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * 8 ^ n := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hin : i ≤ n := by have := Finset.mem_range.1 hi; omega
        rw [norm_mul, norm_pow, lbkpLegC, coeff_map, lbk_leg_coeff, lbkLegCoeff,
          Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, Nat.abs_cast]
        have hc : ((n + i).choose n : ℝ) ≤ 4 ^ n := by
          have h1 := Nat.choose_le_two_pow (n + i) n
          have h2 : 2 ^ (n + i) ≤ 4 ^ n := by
            rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          exact_mod_cast h1.trans h2
        have hzi : ‖z‖ ^ i ≤ 2 ^ n :=
          (pow_le_pow_left₀ (norm_nonneg _) hz i).trans (pow_le_pow_right₀ (by norm_num) hin)
        calc (n.choose i : ℝ) * ((n + i).choose n) * ‖z‖ ^ i ≤ (n.choose i : ℝ) * 4 ^ n * 2 ^ n := by
              gcongr
          _ = (n.choose i : ℝ) * 8 ^ n := by rw [mul_assoc, ← mul_pow]; norm_num
    _ = 16 ^ n := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this, ← mul_pow]
        norm_num

/-- The real coefficient `(2n+1) e^{-(D₀/2)n(n+1)t} P̃_n(y)` of the series in `w`. -/
def lbkpCoef (D0 t y : ℝ) (n : ℕ) : ℝ :=
  (2 * n + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * (lbkLeg n).eval y

/-- The holomorphic extension `z ↦ Σ_n (2n+1) e^{-(D₀/2)n(n+1)t} P̃_n(y) P̃_n(z)`. -/
def lbkpSeriesC (D0 t y : ℝ) (z : ℂ) : ℂ :=
  ∑' n, (lbkpCoef D0 t y n : ℂ) * (lbkpLegC n).eval z

theorem lbkp_seriesC_ofReal (D0 t y w : ℝ) :
    lbkpSeriesC D0 t y (w : ℂ) = (lbkSphereSeries D0 t y w : ℂ) := by
  rw [lbkpSeriesC, lbkSphereSeries, Complex.ofReal_tsum]
  congr 1; funext n
  rw [lbkp_legC_eval_ofReal, lbkYTerm, lbkpCoef]
  push_cast
  ring

theorem lbkp_seriesC_differentiableOn {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) : DifferentiableOn ℂ (lbkpSeriesC D0 t y) (ball 0 2) := by
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun n : ℕ => (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) *
      128 ^ n)
    (lbkp_summable_bound_gen hD0 ht (by norm_num))
    (fun n => ((differentiable_const _).mul (lbkpLegC n).differentiable).differentiableOn)
    isOpen_ball (fun n z hz => ?_)
  have hz' : ‖z‖ ≤ 2 := by rw [mem_ball_zero_iff] at hz; exact hz.le
  have hc : |lbkpCoef D0 t y n| ≤
      (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * 8 ^ n := by
    have hpos : 0 ≤ (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) := by
      positivity
    rw [lbkpCoef, abs_mul, abs_of_nonneg hpos]
    gcongr
    exact lbk_leg_bound n hy
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |lbkpCoef D0 t y n| * ‖(lbkpLegC n).eval z‖ ≤
      ((2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * 8 ^ n) * 16 ^ n :=
        mul_le_mul hc (lbkp_legC_bound n hz') (norm_nonneg _) ((abs_nonneg _).trans hc)
    _ = (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * 128 ^ n := by
        rw [mul_assoc _ ((8 : ℝ) ^ n), ← mul_pow]; norm_num

/-- Unique continuation: if `k_t(y, ·)` vanishes on a nondegenerate `[c, d] ⊆ [0,1]`, it
vanishes on `[0,1]`. -/
theorem lbkp_series_unique_continuation {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 1)
    (hz : ∀ w ∈ Icc c d, lbkSphereSeries D0 t y w = 0) :
    ∀ w ∈ Icc (0 : ℝ) 1, lbkSphereSeries D0 t y w = 0 := by
  have han : AnalyticOnNhd ℂ (lbkpSeriesC D0 t y) (ball 0 2) :=
    (lbkp_seriesC_differentiableOn hD0 ht hy).analyticOnNhd isOpen_ball
  have hmemb : ∀ w : ℝ, |w| ≤ 1 → (w : ℂ) ∈ ball (0 : ℂ) 2 := fun w hw => by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith
  set z0 : ℂ := (((c + d) / 2 : ℝ) : ℂ) with hz0def
  have hz0 : z0 ∈ ball (0 : ℂ) 2 := hmemb _ (by rw [abs_le]; constructor <;> linarith)
  set δ := (d - c) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  let u : ℕ → ℂ := fun k => (((c + d) / 2 + δ / ((k : ℝ) + 1) : ℝ) : ℂ)
  have hu : Tendsto u atTop (𝓝[≠] z0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ).const_add ((c + d) / 2)
      have h2 : Tendsto (fun k : ℕ => (c + d) / 2 + δ / ((k : ℝ) + 1)) atTop
          (𝓝 ((c + d) / 2)) := by
        refine (h1.congr fun k => ?_).trans (by rw [mul_zero, add_zero])
        rw [mul_one_div]
      exact (Complex.continuous_ofReal.tendsto _).comp h2
    · refine Eventually.of_forall fun k => ?_
      simp only [mem_compl_iff, mem_singleton_iff, u, hz0def, Complex.ofReal_inj]
      have : 0 < δ / ((k : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] z0, lbkpSeriesC D0 t y z = 0 := by
    refine hu.frequently (Frequently.of_forall fun k => ?_)
    show lbkpSeriesC D0 t y (u k) = 0
    have hk1 : 0 < δ / ((k : ℝ) + 1) := by positivity
    have hk2 : δ / ((k : ℝ) + 1) ≤ δ := div_le_self hδpos.le (by linarith [k.cast_nonneg (α := ℝ)])
    rw [lbkp_seriesC_ofReal, hz _ ⟨by linarith, by linarith⟩, Complex.ofReal_zero]
  have hEq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0 : ℂ) 2).isPreconnected hz0 hfreq
  intro w hw
  have := hEq (hmemb w (by rw [abs_le]; constructor <;> linarith [hw.1, hw.2]))
  rw [lbkp_seriesC_ofReal, Pi.zero_apply] at this
  exact_mod_cast this

end BlockBand.Endpoints
