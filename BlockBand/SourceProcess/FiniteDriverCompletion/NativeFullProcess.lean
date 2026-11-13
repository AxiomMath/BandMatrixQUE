module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeProjectionLimit
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeHorizonClamp

/-!
# The limit process is a martingale

The limit process of the finite-grid approximants agrees at the horizon with the Itô integral of
the predictable family, is square integrable at every time, equals at each time the conditional
mean of the terminal integral given the enlarged past, and is therefore a martingale.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)

/-- At the horizon, the limit process agrees almost surely with the Itô integral. -/
theorem nativeAdaptedLimit_terminal_ae
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    nativeAdaptedLimit μ T f T =ᵐ[driverLaw (κ := κ) μ]
      (fullNativeIntegral (κ := κ) μ T f : DriverSample S κ → ℝ) := by
  have ht := ((fullNativeIntegral (κ := κ) μ T).continuous.tendsto f).comp
    (nativeFiniteApproximation_tendsto μ T f)
  have hi := tendstoInMeasure_of_tendsto_Lp ht
  have hf : ∀ n, (fullNativeIntegral (κ := κ) μ T (nativeFiniteApproximation μ T f n).val :
      DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
        nativeFiniteProcess μ T (nativeFiniteApproximation μ T f n) T := by
    intro n
    rw [fullNativeIntegral_finite]
    exact nativeFiniteProcess_terminal μ T _
  have ha := tendstoInMeasure_of_tendsto_ae
    (fun n => (nativeFiniteProcess_memLp μ T (nativeFiniteApproximation μ T f n) T).aestronglyMeasurable)
    (nativeApproximation_evaluation_tendsto_ae μ T f le_rfl)
  exact tendstoInMeasure_ae_unique ha (hi.congr_left hf)

/-- The limit process is square integrable at every time. -/
theorem nativeAdaptedLimit_memLp_all
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (u : ℝ≥0) :
    MemLp (nativeAdaptedLimit μ T f u) 2 (driverLaw (κ := κ) μ) := by
  by_cases hu : u ≤ T
  · exact nativeAdaptedLimit_memLp μ T f hu
  · rw [nativeAdaptedLimit_after_horizon μ T f (le_of_not_ge hu)]
    exact nativeAdaptedLimit_memLp μ T f le_rfl

/-- At each time, the limit process is the conditional mean of the terminal integral given the
enlarged past. -/
theorem nativeAdaptedLimit_condExp_all
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (u : ℝ≥0) :
    (driverLaw (κ := κ) μ)[(fullNativeIntegral (κ := κ) μ T f : DriverSample S κ → ℝ) |
      commonWienerFiltration S κ u] =ᵐ[driverLaw (κ := κ) μ] nativeAdaptedLimit μ T f u := by
  by_cases hu : u ≤ T
  · have h := (Lp.memLp (fullNativeIntegral (κ := κ) μ T f)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) ((commonWienerFiltration S κ).le u)
    rw [Lp.toLp_coeFn] at h
    exact h.symm.trans (nativeAdaptedLimit_ae_projection μ T f hu).symm
  · have hTu : T ≤ u := le_of_not_ge hu
    have hm : StronglyMeasurable[commonWienerFiltration S κ u] (nativeAdaptedLimit μ T f T) :=
      ((nativeAdaptedLimit_adapted μ T f T).mono
        ((commonWienerFiltration S κ).mono hTu) le_rfl).stronglyMeasurable
    have hi : Integrable (nativeAdaptedLimit μ T f T) (driverLaw (κ := κ) μ) :=
      memLp_one_iff_integrable.1 ((nativeAdaptedLimit_memLp μ T f le_rfl).mono_exponent one_le_two)
    have hc := condExp_congr_ae (m := commonWienerFiltration S κ u)
      (nativeAdaptedLimit_terminal_ae μ T f).symm
    rw [condExp_of_stronglyMeasurable ((commonWienerFiltration S κ).le u) hm hi] at hc
    exact hc.trans (Eventually.of_forall fun x =>
      (congrFun (nativeAdaptedLimit_after_horizon μ T f hTu) x).symm)

/-- The limit process is a martingale on the enlarged filtration, under `μ` times the law of
independent Wiener paths. -/
theorem nativeAdaptedLimit_martingale
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    Martingale (nativeAdaptedLimit μ T f) (commonWienerFiltration S κ)
      (driverLaw (κ := κ) μ) := by
  apply (martingale_condExp
    (fullNativeIntegral (κ := κ) μ T f : DriverSample S κ → ℝ)
    (commonWienerFiltration S κ) (driverLaw (κ := κ) μ)).congr
  · intro u
    exact (nativeAdaptedLimit_adapted μ T f u).stronglyMeasurable
  · exact nativeAdaptedLimit_condExp_all μ T f

end BlockBand.SourceProcess.FiniteDriverCompletion
