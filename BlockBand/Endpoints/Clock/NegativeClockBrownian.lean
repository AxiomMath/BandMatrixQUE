module

public import BlockBand.SourceProcess.CommonMatrixBrownian
public import BlockBand.Internal.Contracts.TransmissionPath
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Negative moments of the one-ended Brownian clock `X_τ`

We bound the negative moments of the Brownian clock `X_τ = d ∫₀^τ e^{√D₀ B_s - D₀ s/2} ds`
uniformly on compact parameter sets.

* `continuous_openClockFunctional`, `measurable_openClockFunctional`;
* `openClockFunctional_pos`: `X_τ > 0` for every path when `b < 1`, `τ > 0`;
* `negativeClock_openClock_negMoment`: `E X_τ^{-p} ≤ C τ^{-p}` with one constant
  `C = C(β, κ, T₀, p)`, uniformly for `b ∈ [β, 1/2 - β]`, `E ∈ bulkInterval κ`, `0 < τ ≤ T₀`
  (the last display of the proof of the negative-clock theorem).

## Method

Instead of the bound `X_τ ≥ dτ exp(-√D₀ sup_{s≤τ}|B_s| - D₀τ/2)` and exponential moments of the
Brownian supremum, no supremum is needed: with `Y_s = √D₀ B_s - D₀ s/2` and the
probability `ds/τ` on `(0, τ]`, Jensen for `exp` gives `X_τ ≥ dτ exp(avg Y)`, hence
`X_τ^{-p} ≤ (dτ)^{-p} exp(avg(-pY)) ≤ (dτ)^{-p} avg exp(-pY)`; Tonelli and the Gaussian moment
generating function `E exp(-p√D₀ B_s) = exp(p²D₀ s/2)` give
`E X_τ^{-p} ≤ d^{-p} τ^{-p} exp((p² + p) D₀ T₀/2)`. Uniformity: `d ≥ 1` and
`4 - E² = (2-E)(2+E) ≥ κ²`, so `D₀ ≤ 2/(βκ²)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess
open scoped ENNReal NNReal

/-- `X_τ = d ∫₀^τ exp(√D₀ B_s − D₀ s/2) ds` on the canonical Wiener path,
`d = dStar b`, `D₀ = transportD0 b E`. -/
def openClockFunctional (b E τ : ℝ) (ω : BlockBand.SourceProcess.CanonicalWienerPath) : ℝ :=
  dStar b * ∫ s in (0 : ℝ)..τ,
    Real.exp (Real.sqrt (transportD0 b E) * ω s.toNNReal - transportD0 b E * s / 2)

namespace NegativeClockBrownian

/-- The exponent `Y_s(ω) = √D₀ ω(s) − D₀ s/2`. -/
def expo (b E : ℝ) (ω : CanonicalWienerPath) (s : ℝ) : ℝ :=
  Real.sqrt (transportD0 b E) * ω s.toNNReal - transportD0 b E * s / 2

theorem continuous_expo_uncurry (b E : ℝ) :
    Continuous (fun q : CanonicalWienerPath × ℝ => expo b E q.1 q.2) := by
  unfold expo
  have hev : Continuous (fun q : CanonicalWienerPath × ℝ => q.1 q.2.toNNReal) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  fun_prop

theorem continuous_expo (b E : ℝ) (ω : CanonicalWienerPath) : Continuous (expo b E ω) :=
  (continuous_expo_uncurry b E).comp (continuous_const.prodMk continuous_id)

/-- Jensen for `exp` on the probability `ds/τ` on `(0, τ]`. -/
theorem exp_avg_le {F : ℝ → ℝ} (hF : Continuous F) {τ : ℝ} (hτ : 0 < τ) :
    Real.exp (τ⁻¹ * ∫ s in Ioc 0 τ, F s) ≤ τ⁻¹ * ∫ s in Ioc 0 τ, Real.exp (F s) := by
  have hvol : (volume : Measure ℝ) (Ioc 0 τ) = ENNReal.ofReal τ := by
    rw [Real.volume_Ioc, sub_zero]
  have h := ConvexOn.map_set_average_le (μ := (volume : Measure ℝ)) (t := Ioc 0 τ) (f := F)
    (s := univ) convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
    (by rw [hvol]; simpa using hτ) (by rw [hvol]; exact ENNReal.ofReal_ne_top)
    (Filter.Eventually.of_forall fun _ => mem_univ _) hF.integrableOn_Ioc
    (Real.continuous_exp.comp hF).integrableOn_Ioc
  have hreal : (volume : Measure ℝ).real (Ioc 0 τ) = τ := by
    rw [measureReal_def, hvol, ENNReal.toReal_ofReal hτ.le]
  simp only [setAverage_eq, hreal, smul_eq_mul] at h
  exact h

/-- Pointwise Jensen bound: `X_τ^{-p} ≤ (dτ)^{-p} τ⁻¹ ∫_{(0,τ]} exp(-pY_s) ds`. -/
theorem rpow_neg_le {b : ℝ} (hb1 : b < 1) (E : ℝ) {τ : ℝ} (hτ : 0 < τ) {p : ℝ} (hp : 0 < p)
    (ω : CanonicalWienerPath) :
    openClockFunctional b E τ ω ^ (-p) ≤
      (dStar b * τ) ^ (-p) * (τ⁻¹ * ∫ s in Ioc 0 τ, Real.exp (-p * expo b E ω s)) := by
  have hF := continuous_expo b E ω
  have hd : 0 < dStar b := by unfold dStar; exact div_pos one_pos (by linarith)
  set A := τ⁻¹ * ∫ s in Ioc 0 τ, Real.exp (expo b E ω s) with hA
  set m := τ⁻¹ * ∫ s in Ioc 0 τ, expo b E ω s with hm
  have hI : openClockFunctional b E τ ω = dStar b * ∫ s in Ioc 0 τ, Real.exp (expo b E ω s) := by
    unfold openClockFunctional
    rw [intervalIntegral.integral_of_le hτ.le]
    rfl
  have hX : openClockFunctional b E τ ω = (dStar b * τ) * A := by
    rw [hI, hA]
    field_simp
  have hJ1 : Real.exp m ≤ A := exp_avg_le hF hτ
  have hJ2 : Real.exp (τ⁻¹ * ∫ s in Ioc 0 τ, -p * expo b E ω s) ≤
      τ⁻¹ * ∫ s in Ioc 0 τ, Real.exp (-p * expo b E ω s) :=
    exp_avg_le (continuous_const.mul hF) hτ
  have hint : ∫ s in Ioc 0 τ, -p * expo b E ω s = -p * ∫ s in Ioc 0 τ, expo b E ω s :=
    integral_const_mul _ _
  have hA0 : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hJ1
  rw [hX, Real.mul_rpow (by positivity) hA0.le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  calc A ^ (-p) ≤ Real.exp m ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hJ1 (by linarith)
    _ = Real.exp (τ⁻¹ * ∫ s in Ioc 0 τ, -p * expo b E ω s) := by
        rw [← Real.exp_mul, hint, hm]; ring_nf
    _ ≤ _ := hJ2

/-- `E exp(-pY_s) = exp((p² + p) D₀ s/2)` for `s ≥ 0`. -/
theorem lintegral_exp_expo {b E : ℝ} (hD : 0 ≤ transportD0 b E) (p : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-p * expo b E ω s)) ∂canonicalWienerLaw =
      ENNReal.ofReal (Real.exp ((p ^ 2 + p) * transportD0 b E * s / 2)) := by
  set D := transportD0 b E
  set X : CanonicalWienerPath → ℝ := fun ω => ω s.toNNReal
  have hlaw : HasLaw X (gaussianReal 0 s.toNNReal) canonicalWienerLaw :=
    canonicalWiener_isBrownian.toIsPreBrownianReal.hasLaw_eval s.toNNReal
  have hmgf := mgf_gaussianReal hlaw (-p * Real.sqrt D)
  have hpt : ∀ ω, Real.exp (-p * expo b E ω s) =
      Real.exp (p * D * s / 2) * Real.exp (-p * Real.sqrt D * X ω) := by
    intro ω
    rw [← Real.exp_add]; unfold expo; congr 1; simp only [X, D]; ring
  have hmgf_ne : ∫ ω, Real.exp (-p * Real.sqrt D * X ω) ∂canonicalWienerLaw ≠ 0 := by
    have : mgf X canonicalWienerLaw (-p * Real.sqrt D) =
        ∫ ω, Real.exp (-p * Real.sqrt D * X ω) ∂canonicalWienerLaw := rfl
    rw [← this, hmgf]; exact (Real.exp_pos _).ne'
  have hi : Integrable (fun ω => Real.exp (-p * expo b E ω s)) canonicalWienerLaw := by
    simp_rw [hpt]
    exact (Integrable.of_integral_ne_zero hmgf_ne).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  congr 1
  simp_rw [hpt]
  rw [integral_const_mul]
  have : ∫ ω, Real.exp (-p * Real.sqrt D * X ω) ∂canonicalWienerLaw =
      mgf X canonicalWienerLaw (-p * Real.sqrt D) := rfl
  rw [this, hmgf, ← Real.exp_add, Real.coe_toNNReal _ hs]
  congr 1
  rw [mul_pow, Real.sq_sqrt hD]
  ring

end NegativeClockBrownian

open NegativeClockBrownian

theorem continuous_openClockFunctional (b E τ : ℝ) : Continuous (openClockFunctional b E τ) := by
  unfold openClockFunctional
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun ω s => Real.exp (expo b E ω s))
    (Real.continuous_exp.comp (continuous_expo_uncurry b E)) 0 τ

theorem measurable_openClockFunctional (b E τ : ℝ) : Measurable (openClockFunctional b E τ) :=
  (continuous_openClockFunctional b E τ).measurable

theorem openClockFunctional_pos {b : ℝ} (hb1 : b < 1) (E : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (ω : BlockBand.SourceProcess.CanonicalWienerPath) : 0 < openClockFunctional b E τ ω := by
  have hd : 0 < dStar b := by unfold dStar; exact div_pos one_pos (by linarith)
  refine mul_pos hd (intervalIntegral.intervalIntegral_pos_of_pos_on ?_
    (fun s _ => Real.exp_pos _) hτ)
  exact (Real.continuous_exp.comp (continuous_expo b E ω)).intervalIntegrable _ _

/-- `β, κ, T₀, p` first; then one `C ≥ 0`; for every `b ∈ [β, 1/2 - β]`,
`E ∈ bulkInterval κ` and `0 < τ ≤ T₀`:
`E X_τ^{-p} ≤ C τ^{-p}` under the canonical Wiener law.
Proved by Jensen (module docstring), not by the Brownian supremum.
-/
theorem negativeClock_openClock_negMoment (β κ T₀ p : ℝ) (hβ : 0 < β) (hβ4 : β < 1 / 4)
    (hκ : 0 < κ) (hT₀ : 0 < T₀) (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ E ∈ bulkInterval κ, ∀ τ : ℝ, 0 < τ → τ ≤ T₀ →
      ∫⁻ ω, ENNReal.ofReal (openClockFunctional b E τ ω ^ (-p))
          ∂BlockBand.SourceProcess.canonicalWienerLaw ≤ ENNReal.ofReal (C * τ ^ (-p)) := by
  set C := Real.exp ((p ^ 2 + p) * (2 / (β * κ ^ 2)) * T₀ / 2) with hC
  refine ⟨C, (Real.exp_pos _).le, fun b hb E hE τ hτ hτT => ?_⟩
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hE0, hE1⟩ := hE
  have hbpos : 0 < b := lt_of_lt_of_le hβ hb0
  have hblt : b < 1 := by linarith
  set D := transportD0 b E with hDdef
  have h4 : κ ^ 2 ≤ 4 - E ^ 2 := by nlinarith
  have hκ2 : 0 < κ ^ 2 := by positivity
  have hD0 : 0 < D := by
    rw [hDdef]; unfold transportD0; exact div_pos two_pos (mul_pos hbpos (by linarith))
  have hDle : D ≤ 2 / (β * κ ^ 2) := by
    rw [hDdef]; unfold transportD0
    exact div_le_div_of_nonneg_left zero_le_two (mul_pos hβ hκ2)
      (mul_le_mul hb0 h4 hκ2.le hbpos.le)
  have hd1 : 1 ≤ dStar b := by
    unfold dStar; rw [le_div_iff₀ (by linarith)]; linarith
  have hd0 : 0 < dStar b := by linarith
  set K := Real.exp ((p ^ 2 + p) * D * T₀ / 2) with hK
  have hKC : K ≤ C := by
    rw [hK, hC]; apply Real.exp_le_exp.mpr
    have : 0 ≤ (p ^ 2 + p) * T₀ / 2 := by positivity
    nlinarith
  set c := (dStar b * τ) ^ (-p) * τ⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  set G : CanonicalWienerPath → ℝ → ℝ≥0∞ :=
    fun ω s => ENNReal.ofReal (Real.exp (-p * expo b E ω s)) with hG
  -- pointwise Jensen, in `lintegral` form
  have hpt : ∀ ω, ENNReal.ofReal (openClockFunctional b E τ ω ^ (-p)) ≤
      ENNReal.ofReal c * ∫⁻ s in Ioc 0 τ, G ω s := by
    intro ω
    have hi : IntegrableOn (fun s => Real.exp (-p * expo b E ω s)) (Ioc 0 τ) :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_expo b E ω))).integrableOn_Ioc
    rw [hG, ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le), ← ENNReal.ofReal_mul hc0]
    refine ENNReal.ofReal_le_ofReal ((rpow_neg_le hblt E hτ hp ω).trans (le_of_eq ?_))
    rw [hc]; ring
  have hmeas : Measurable (Function.uncurry G) := by
    have : Continuous (fun q : CanonicalWienerPath × ℝ => Real.exp (-p * expo b E q.1 q.2)) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_expo_uncurry b E))
    exact ENNReal.measurable_ofReal.comp this.measurable
  have hinner : ∀ s ∈ Ioc (0 : ℝ) τ, ∫⁻ ω, G ω s ∂canonicalWienerLaw ≤ ENNReal.ofReal K := by
    intro s hs
    rw [hG, lintegral_exp_expo hD0.le p hs.1.le]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : s ≤ T₀ := hs.2.trans hτT
    have : 0 ≤ (p ^ 2 + p) * D := by positivity
    nlinarith
  calc ∫⁻ ω, ENNReal.ofReal (openClockFunctional b E τ ω ^ (-p)) ∂canonicalWienerLaw
      ≤ ∫⁻ ω, ENNReal.ofReal c * (∫⁻ s in Ioc 0 τ, G ω s) ∂canonicalWienerLaw :=
        lintegral_mono hpt
    _ = ENNReal.ofReal c * ∫⁻ s in Ioc 0 τ, (∫⁻ ω, G ω s ∂canonicalWienerLaw) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_lintegral_swap hmeas.aemeasurable]
    _ ≤ ENNReal.ofReal c * ∫⁻ _ in Ioc 0 τ, ENNReal.ofReal K := by
        gcongr ENNReal.ofReal c * ?_
        exact setLIntegral_mono measurable_const hinner
    _ = ENNReal.ofReal (c * K * τ) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hc0]
        congr 1; ring
    _ ≤ ENNReal.ofReal (C * τ ^ (-p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hcK : c * K * τ = (dStar b) ^ (-p) * K * τ ^ (-p) := by
          rw [hc, Real.mul_rpow hd0.le hτ.le]; field_simp
        rw [hcK]
        have hdp : (dStar b) ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hd1 (by linarith)
        have hτp : 0 < τ ^ (-p) := Real.rpow_pos_of_pos hτ _
        have hK0 : 0 < K := Real.exp_pos _
        have hdp0 : 0 ≤ (dStar b) ^ (-p) := Real.rpow_nonneg hd0.le _
        calc (dStar b) ^ (-p) * K * τ ^ (-p) ≤ 1 * C * τ ^ (-p) := by gcongr
          _ = C * τ ^ (-p) := by ring

end BlockBand.Endpoints.Clock
