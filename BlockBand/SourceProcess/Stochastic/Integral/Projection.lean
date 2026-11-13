module
public import BlockBand.SourceProcess.Stochastic.Integral.Density
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeAgreement
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Timewise projections of the integral

Measure `driverLaw μ`, raw filtration `F = commonWienerFiltration S κ`.

* `condExp_rectangle_increment`: for `s ≤ r`, an `F_s`-measurable `H ∈ L²` and any time `v`,
  `E[H (W^c_r − W^c_s) | F_v] = H (W^c_{max s (min r v)} − W^c_s)` a.s.
* `processL2 μ T v : PredictableFamily T →L[ℝ] L²` is `f ↦ E[I_T f | F_{min v T}]`, a continuous
  linear map, and the draft process `nativeAdaptedLimit μ T f v` is a.s. equal to it.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)

omit [Fintype κ] in
theorem measurable_brownian_coord (c : κ) (r : ℝ≥0) :
    Measurable[commonWienerFiltration S κ r] (fun x : DriverSample S κ => commonRealBrownian r x c) :=
  (measurable_pi_apply c).comp (commonRealBrownian_adapted r)

omit [MeasurableSpace S] [Fintype κ] in
theorem increment_eq_driverStep (c : κ) {s r : ℝ≥0} (hsr : s ≤ r) (H : DriverSample S κ → ℝ) :
    (fun x : DriverSample S κ => H x * (commonRealBrownian r x c - commonRealBrownian s x c)) =
      driverStep s (r - s) c H := by
  funext x
  simp only [driverStep, driverIncrement, add_tsub_cancel_of_le hsr]

/-- Conditional mean of a rectangle increment given the raw past at an arbitrary time. -/
theorem condExp_rectangle_increment (c : κ) {s r : ℝ≥0} (hsr : s ≤ r)
    {H : DriverSample S κ → ℝ} (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) (v : ℝ≥0) :
    (driverLaw (κ := κ) μ)[fun x => H x * (commonRealBrownian r x c - commonRealBrownian s x c) |
      commonWienerFiltration S κ v] =ᵐ[driverLaw (κ := κ) μ]
      fun x => H x * (commonRealBrownian (max s (min r v)) x c - commonRealBrownian s x c) := by
  by_cases hvs : v ≤ s
  · rw [max_eq_left ((min_le_right _ _).trans hvs), increment_eq_driverStep c hsr H]
    filter_upwards [driverStep_condExp_earlier μ v s (r - s) hvs c hH hHL2] with x hx
    rw [hx, sub_self, mul_zero]
    rfl
  have hsv : s ≤ v := (lt_of_not_ge hvs).le
  have hHv : Measurable[commonWienerFiltration S κ v] H :=
    hH.mono ((commonWienerFiltration S κ).mono hsv) le_rfl
  by_cases hrv : r ≤ v
  · rw [min_eq_left hrv, max_eq_right hsr]
    have hm : StronglyMeasurable[commonWienerFiltration S κ v]
        (fun x => H x * (commonRealBrownian r x c - commonRealBrownian s x c)) :=
      (hHv.mul (((measurable_brownian_coord c r).mono ((commonWienerFiltration S κ).mono hrv)
        le_rfl).sub ((measurable_brownian_coord c s).mono
          ((commonWienerFiltration S κ).mono hsv) le_rfl))).stronglyMeasurable
    have hi : Integrable (fun x => H x * (commonRealBrownian r x c - commonRealBrownian s x c))
        (driverLaw (κ := κ) μ) := by
      rw [increment_eq_driverStep c hsr H]
      exact (driverStep_memLp μ s (r - s) c hH hHL2).integrable one_le_two
    rw [condExp_of_stronglyMeasurable ((commonWienerFiltration S κ).le v) hm hi]
  · have hvr : v ≤ r := (lt_of_not_ge hrv).le
    rw [min_eq_right hvr, max_eq_right hsv]
    have hsplit : (fun x => H x * (commonRealBrownian r x c - commonRealBrownian s x c)) =
        driverStep v (r - v) c H +
          fun x => H x * (commonRealBrownian v x c - commonRealBrownian s x c) := by
      rw [← increment_eq_driverStep c hvr H]
      funext x
      simp only [Pi.add_apply]
      ring
    have hm : StronglyMeasurable[commonWienerFiltration S κ v]
        (fun x => H x * (commonRealBrownian v x c - commonRealBrownian s x c)) :=
      (hHv.mul ((measurable_brownian_coord c v).sub ((measurable_brownian_coord c s).mono
          ((commonWienerFiltration S κ).mono hsv) le_rfl))).stronglyMeasurable
    have hi : Integrable (fun x => H x * (commonRealBrownian v x c - commonRealBrownian s x c))
        (driverLaw (κ := κ) μ) := by
      rw [increment_eq_driverStep c hsv H]
      exact (driverStep_memLp μ s (v - s) c hH hHL2).integrable one_le_two
    rw [hsplit]
    filter_upwards [condExp_add ((driverStep_memLp μ v (r - v) c hHv hHL2).integrable one_le_two)
      hi (commonWienerFiltration S κ v), driverStep_condExp μ v (r - v) c hHv hHL2] with x hx hz
    rw [hx, Pi.add_apply, hz,
      condExp_of_stronglyMeasurable ((commonWienerFiltration S κ).le v) hm hi]
    simp only [Pi.zero_apply, zero_add]

/-- The time-`v` projection `f ↦ E[I_T f | F_{min v T}]` as a continuous linear map. -/
def processL2 (v : ℝ≥0) :
    PredictableFamily (S := S) (κ := κ) (μ := μ) T →L[ℝ] Lp ℝ 2 (driverLaw (κ := κ) μ) :=
  (lpMeas ℝ ℝ (commonWienerFiltration S κ (min v T)) 2 (driverLaw (κ := κ) μ)).subtypeL.comp
    ((condExpL2 ℝ ℝ ((commonWienerFiltration S κ).le (min v T))).comp
      (fullNativeIntegral (κ := κ) μ T).toContinuousLinearMap)

theorem processL2_coeFn (v : ℝ≥0) (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    (processL2 μ T v f : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
      (driverLaw (κ := κ) μ)[(fullNativeIntegral (κ := κ) μ T f : DriverSample S κ → ℝ) |
        commonWienerFiltration S κ (min v T)] := by
  have h := (Lp.memLp (fullNativeIntegral (κ := κ) μ T f)).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) ((commonWienerFiltration S κ).le (min v T))
  rw [Lp.toLp_coeFn] at h
  exact h

/-- The draft raw-adapted process is, at each time, a.s. the projection `processL2`. -/
theorem nativeAdaptedLimit_ae_processL2 (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T)
    (v : ℝ≥0) :
    nativeAdaptedLimit μ T f v =ᵐ[driverLaw (κ := κ) μ] (processL2 μ T v f : DriverSample S κ → ℝ) := by
  rw [nativeAdaptedLimit_eq_min]
  exact nativeAdaptedLimit_ae_projection μ T f (min_le_right v T)

end BlockBand.SourceProcess.Stochastic.Integral
