module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeTimewiseProjection
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeUniformConvergence

/-!
# Identification of the limit process

The finite-grid approximants converge to the predictable family, their terminal integrals and
their timewise projections converge in `L²`, and the limit process agrees almost surely, at every
time, with the conditional `L²` projection of the terminal integral.
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

/-- The Itô integral agrees with the finite-grid integral on finite-grid classes. -/
theorem fullNativeIntegral_finite (f : nativeFinitePredictable (κ := κ) μ T) :
    fullNativeIntegral (κ := κ) μ T f.val = nativeFiniteIntegral (κ := κ) μ T f := by
  rcases nativeFinite_zero_or_presentation μ T f with hf | ⟨d, hd⟩
  · rw [hf]
    change fullNativeIntegral (κ := κ) μ T 0 = nativeFiniteIntegral (κ := κ) μ T 0
    exact (fullNativeIntegral (κ := κ) μ T).map_zero.trans
      (nativeFiniteIntegral (κ := κ) μ T).map_zero.symm
  · rw [hd]
    exact (fullNativeIntegral_presentation μ T d).trans
      (nativeFiniteIntegral_presentation μ T d).symm

/-- The finite-grid approximants converge to the predictable family. -/
theorem nativeFiniteApproximation_tendsto
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    Tendsto (fun n => (nativeFiniteApproximation μ T f n).val) atTop (𝓝 f) := by
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero (fun n => dist_nonneg)
    (fun n => (dist_comm _ _).trans_le (nativeFiniteApproximation_rate μ T f n).le)
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/8)
    (by norm_num : (1/8:ℝ) < 1)).comp (tendsto_add_atTop_nat 1)

/-- The timewise projections of the approximants converge in `L²`. -/
theorem nativeProjectionApproximation_tendsto
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (u : ℝ≥0) :
    Tendsto (fun n => nativeTimewiseProjection μ T (nativeFiniteApproximation μ T f n).val u)
      atTop (𝓝 (nativeTimewiseProjection μ T f u)) := by
  have ht := ((fullNativeIntegral (κ := κ) μ T).continuous.tendsto f).comp
    (nativeFiniteApproximation_tendsto μ T f)
  have hp := ((condExpL2 ℝ ℝ ((commonWienerFiltration S κ).le u)).continuous.tendsto
    (fullNativeIntegral (κ := κ) μ T f)).comp ht
  exact (continuous_subtype_val.tendsto _).comp hp

/-- The timewise projection of each approximant is its finite process, almost surely. -/
theorem nativeProjectionApproximation_ae
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) {u : ℝ≥0} (hu : u ≤ T) (n : ℕ) :
    (nativeTimewiseProjection μ T (nativeFiniteApproximation μ T f n).val u : DriverSample S κ → ℝ)
      =ᵐ[driverLaw (κ := κ) μ]
        nativeFiniteProcess μ T (nativeFiniteApproximation μ T f n) u := by
  unfold nativeTimewiseProjection
  rw [fullNativeIntegral_finite]
  exact nativeFiniteProcess_condExpL2_terminal μ T _ hu

/-- The finite processes converge almost surely to the limit process at every time of the
horizon. -/
theorem nativeApproximation_evaluation_tendsto_ae
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) {u : ℝ≥0} (hu : u ≤ T) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ,
      Tendsto (fun n => nativeFiniteProcess μ T (nativeFiniteApproximation μ T f n) u x)
        atTop (𝓝 (nativeAdaptedLimit μ T f u x)) := by
  filter_upwards [nativeApproximation_path_converges_ae μ T f] with x hx
  rcases hx with ⟨L, hL⟩
  let t : Set.Icc (0 : ℝ≥0) T := ⟨u, zero_le, hu⟩
  have ht := ((continuous_eval_const t).tendsto L).comp hL
  have he : nativeAdaptedLimit μ T f u x = L t := ht.limUnder_eq
  rw [he]
  exact ht

/-- The limit process is almost surely the conditional `L²` projection of the terminal integral. -/
theorem nativeAdaptedLimit_ae_projection
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) {u : ℝ≥0} (hu : u ≤ T) :
    nativeAdaptedLimit μ T f u =ᵐ[driverLaw (κ := κ) μ]
      (nativeTimewiseProjection μ T f u : DriverSample S κ → ℝ) := by
  have hp := tendstoInMeasure_of_tendsto_Lp (nativeProjectionApproximation_tendsto μ T f u)
  have hpf := hp.congr_left (nativeProjectionApproximation_ae μ T f hu)
  have ha := tendstoInMeasure_of_tendsto_ae
    (fun n => (nativeFiniteProcess_memLp μ T (nativeFiniteApproximation μ T f n) u).aestronglyMeasurable)
    (nativeApproximation_evaluation_tendsto_ae μ T f hu)
  exact tendstoInMeasure_ae_unique ha hpf

/-- The limit process is square integrable at every time of the horizon. -/
theorem nativeAdaptedLimit_memLp
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) {u : ℝ≥0} (hu : u ≤ T) :
    MemLp (nativeAdaptedLimit μ T f u) 2 (driverLaw (κ := κ) μ) :=
  (Lp.memLp (nativeTimewiseProjection μ T f u)).ae_eq
    (nativeAdaptedLimit_ae_projection μ T f hu).symm

end BlockBand.SourceProcess.FiniteDriverCompletion
