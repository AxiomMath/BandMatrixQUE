module

public import Mathlib

/-!
# The negative-clock theorem: from Laplace domination to negative moments

We pass from a Laplace domination to a bound on negative moments; the argument is purely
measure-theoretic.

* `negativeClock_limit_Iio_zero`: a weak limit (bounded continuous tests) of laws carried by
  `[0,∞)` is carried by `[0,∞)` (test `min 1 (max (-x) 0)`).
* `negativeClock_negMoment_of_laplace`: if `μ(-∞,0) = 0` and
  `∫ e^{-s max(x,0)} dμ ≤ E e^{-saX}` for every `s > 0`, with `X > 0` measurable, then
  `μ(-∞,0] = 0` and `∫ x^{-p} dμ ≤ a^{-p} E X^{-p}` for every `p > 0` (`lintegral`s; the
  right side may be `∞`). Proof: dominated convergence for the atom; the Gamma representation
  `x^{-p} = Γ(p)⁻¹ ∫_0^∞ s^{p-1} e^{-sx} ds` (`Real.integral_rpow_mul_exp_neg_mul_Ioi`) and
  Tonelli twice.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace NegativeClockMoments

/-- The test `x ↦ min 1 (max (-x) 0)`: bounded continuous, `0` on `[0,∞)`, positive on
`(-∞,0)`. -/
def negPartTest : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min 1 (max (-x) 0), by fun_prop⟩ 1 fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]
      constructor <;>
        nlinarith [min_le_left (1 : ℝ) (max (-x) 0), min_le_left (1 : ℝ) (max (-y) 0),
          le_min (zero_le_one' ℝ) (le_max_right (-x) 0),
          le_min (zero_le_one' ℝ) (le_max_right (-y) 0)]

theorem negPartTest_apply (x : ℝ) : negPartTest x = min 1 (max (-x) 0) := rfl

/-- The Gamma kernel `Γ(p)⁻¹ s^{p-1}`. -/
def gammaKernel (p s : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((Real.Gamma p)⁻¹ * s ^ (p - 1))

theorem measurable_gammaKernel (p : ℝ) : Measurable (gammaKernel p) := by
  unfold gammaKernel; fun_prop

/-- `x^{-p} = ∫_0^∞ Γ(p)⁻¹ s^{p-1} e^{-sx} ds` for `x, p > 0`. -/
theorem ofReal_rpow_neg_eq_lintegral {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    ENNReal.ofReal (x ^ (-p)) =
      ∫⁻ s in Set.Ioi 0, gammaKernel p s * ENNReal.ofReal (Real.exp (-(s * x))) := by
  have hI := Real.integral_rpow_mul_exp_neg_mul_Ioi hp hx
  have hpos : 0 < (1 / x) ^ p * Real.Gamma p :=
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos hp)
  have hint : IntegrableOn (fun t : ℝ => t ^ (p - 1) * Real.exp (-(x * t))) (Set.Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hI]; exact hpos.ne')
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t : ℝ => t ^ (p - 1) * Real.exp (-(x * t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  have hL := ofReal_integral_eq_lintegral_ofReal hint hnn
  rw [hI] at hL
  have hG : 0 < Real.Gamma p := Real.Gamma_pos_of_pos hp
  have e1 : x ^ (-p) = (Real.Gamma p)⁻¹ * ((1 / x) ^ p * Real.Gamma p) := by
    rw [Real.rpow_neg hx.le, one_div, Real.inv_rpow hx.le]
    field_simp
  rw [e1, ENNReal.ofReal_mul (inv_nonneg.mpr hG.le), hL,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := le_of_lt ht
  simp only [gammaKernel]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hG.le),
    ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hG.le) (Real.rpow_nonneg ht0 _)),
    mul_assoc, mul_comm x t]

end NegativeClockMoments

open NegativeClockMoments

/-- Weak limits of laws carried by `[0,∞)` are carried by `[0,∞)`. -/
theorem negativeClock_limit_Iio_zero {ν : ℕ → Measure ℝ} [∀ j, IsProbabilityMeasure (ν j)]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hν : ∀ j, ν j (Set.Iio 0) = 0)
    (hlim : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ x, f x ∂ν j) atTop (𝓝 (∫ x, f x ∂μ))) :
    μ (Set.Iio 0) = 0 := by
  have hzero : ∀ j, ∫ x, negPartTest x ∂ν j = 0 := by
    intro j
    refine integral_eq_zero_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hν j)] with x hx
    simp only [Set.mem_Iio, not_lt] at hx
    simp [negPartTest_apply, hx]
  have h0 : ∫ x, negPartTest x ∂μ = 0 := by
    have := hlim negPartTest
    simp only [hzero] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hnn : 0 ≤ (fun x => negPartTest x) := fun x => by
    simp only [Pi.zero_apply, negPartTest_apply]
    exact le_min zero_le_one (le_max_right _ _)
  have hae := (integral_eq_zero_iff_of_nonneg hnn (negPartTest.integrable μ)).mp h0
  refine measure_mono_null (fun x (hx : x < 0) => ?_) (ae_iff.mp hae)
  change ¬ negPartTest x = 0
  rw [negPartTest_apply]
  have : 0 < min 1 (max (-x) 0) := lt_min one_pos (lt_max_of_lt_left (by linarith))
  exact this.ne'

/-- **Step (3) of the negative-clock theorem**. Laplace domination
`∫ e^{-s max(x,0)} dμ ≤ E e^{-saX}` (`s > 0`) of a law `μ` carried by `[0,∞)`, by a strictly
positive measurable `X`, gives no atom at `0` and `∫ x^{-p} dμ ≤ a^{-p} E X^{-p}`. -/
theorem negativeClock_negMoment_of_laplace {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) (hXpos : ∀ ω, 0 < X ω)
    {a : ℝ} (ha : 0 < a)
    (hL : ∀ s : ℝ, 0 < s →
      ∫ x, Real.exp (-(s * max x 0)) ∂μ ≤ ∫ ω, Real.exp (-(s * a * X ω)) ∂P)
    {p : ℝ} (hp : 0 < p) :
    μ (Set.Iic 0) = 0 ∧
      ∫⁻ x, ENNReal.ofReal (x ^ (-p)) ∂μ ≤
        ENNReal.ofReal (a ^ (-p)) * ∫⁻ ω, ENNReal.ofReal (X ω ^ (-p)) ∂P := by
  -- integrability of the bounded exponentials
  have hintμ : ∀ s : ℝ, 0 ≤ s → Integrable (fun x : ℝ => Real.exp (-(s * max x 0))) μ := by
    intro s hs
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hs (le_max_right _ _))
  have hintP : ∀ s : ℝ, 0 ≤ s → Integrable (fun ω => Real.exp (-(s * a * X ω))) P := by
    intro s hs
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hs ha.le) (hXpos ω).le)
  -- (ii) no atom at 0
  have hatom : μ {0} = 0 := by
    have hle : ∀ n : ℕ, 0 < n → μ.real {0} ≤ ∫ ω, Real.exp (-((n : ℝ) * a * X ω)) ∂P := by
      intro n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      refine le_trans ?_ (hL n hn')
      rw [← integral_indicator_one (measurableSet_singleton 0)]
      refine integral_mono ((integrable_const 1).indicator (measurableSet_singleton 0))
        (hintμ n hn'.le) fun x => ?_
      by_cases hx : x = 0
      · subst hx; simp
      · rw [Set.indicator_of_notMem (by simpa using hx)]
        exact (Real.exp_pos _).le
    have hlim : Tendsto (fun n : ℕ => ∫ ω, Real.exp (-((n : ℝ) * a * X ω)) ∂P) atTop
        (𝓝 (∫ _ω, (0 : ℝ) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => by fun_prop)
        (integrable_const 1) (fun n => Eventually.of_forall fun ω => ?_)
        (Eventually.of_forall fun ω => ?_)
      · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) ha.le) (hXpos ω).le)
      · have hc : 0 < a * X ω := mul_pos ha (hXpos ω)
        have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const hc)
        refine this.congr fun n => ?_
        simp [Function.comp, mul_assoc]
    rw [integral_zero] at hlim
    have hreal : μ.real {0} ≤ 0 :=
      ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun n hn => hle n hn⟩)
    have : μ.real {0} = 0 := le_antisymm hreal measureReal_nonneg
    rwa [measureReal_eq_zero_iff] at this
  have hIic : μ (Set.Iic 0) = 0 := by
    rw [← Set.Iio_insert, Set.insert_eq]
    exact measure_union_null hatom hμ
  refine ⟨hIic, ?_⟩
  -- (iii) Gamma representation and Tonelli
  set K := gammaKernel p
  have hK := measurable_gammaKernel p
  have hpos_ae : ∀ᵐ x ∂μ, 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hIic] with x hx
    simpa using hx
  have step1 : ∫⁻ x, ENNReal.ofReal (x ^ (-p)) ∂μ =
      ∫⁻ x, (∫⁻ s in Set.Ioi 0, K s * ENNReal.ofReal (Real.exp (-(s * max x 0)))) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hpos_ae] with x hx
    rw [max_eq_left hx.le]
    exact ofReal_rpow_neg_eq_lintegral hp hx
  have hmeas1 : Measurable (Function.uncurry fun (x : ℝ) (s : ℝ) =>
      K s * ENNReal.ofReal (Real.exp (-(s * max x 0)))) := by
    refine (hK.comp measurable_snd).mul ?_
    fun_prop
  have step2 : ∫⁻ x, (∫⁻ s in Set.Ioi 0, K s * ENNReal.ofReal (Real.exp (-(s * max x 0)))) ∂μ =
      ∫⁻ s in Set.Ioi 0, K s * ∫⁻ x, ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂μ := by
    rw [lintegral_lintegral_swap hmeas1.aemeasurable]
    refine lintegral_congr fun s => ?_
    exact lintegral_const_mul _ (by fun_prop)
  have step3 : ∫⁻ s in Set.Ioi 0, K s * ∫⁻ x, ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂μ ≤
      ∫⁻ s in Set.Ioi 0, ∫⁻ ω, K s * ENNReal.ofReal (Real.exp (-(s * (a * X ω)))) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    rw [lintegral_const_mul _ (by fun_prop)]
    refine mul_le_mul' le_rfl ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hintμ s hs.le)
        (Eventually.of_forall fun x => (Real.exp_pos _).le)]
    have e : (fun ω => ENNReal.ofReal (Real.exp (-(s * (a * X ω))))) =
        fun ω => ENNReal.ofReal (Real.exp (-(s * a * X ω))) := by
      funext ω; rw [mul_assoc]
    rw [e, ← ofReal_integral_eq_lintegral_ofReal (hintP s hs.le)
        (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (hL s hs)
  have hmeas2 : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) =>
      K s * ENNReal.ofReal (Real.exp (-(s * (a * X ω))))) := by
    refine (hK.comp measurable_fst).mul ?_
    have : Measurable fun q : ℝ × Ω => X q.2 := hX.comp measurable_snd
    fun_prop
  have step4 : ∫⁻ s in Set.Ioi 0, ∫⁻ ω, K s * ENNReal.ofReal (Real.exp (-(s * (a * X ω)))) ∂P =
      ∫⁻ ω, ENNReal.ofReal (a ^ (-p)) * ENNReal.ofReal (X ω ^ (-p)) ∂P := by
    rw [lintegral_lintegral_swap hmeas2.aemeasurable]
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_rpow_neg_eq_lintegral hp (mul_pos ha (hXpos ω)),
      Real.mul_rpow ha.le (hXpos ω).le, ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
  rw [step1, step2]
  refine step3.trans (le_of_eq ?_)
  rw [step4, lintegral_const_mul _ (by fun_prop)]

end BlockBand.Endpoints.Clock
