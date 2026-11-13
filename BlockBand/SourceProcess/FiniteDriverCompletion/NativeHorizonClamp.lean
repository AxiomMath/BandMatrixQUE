module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeUniformConvergence

/-!
# Constancy after the horizon

Continuous grid sums, finite processes and the limit process are constant after the horizon `T`,
so the limit process factors through `u ↦ min u T` and has almost surely continuous paths at all
nonnegative times.
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

omit [IsProbabilityMeasure μ] in
/-- Continuous grid sums are constant after the horizon. -/
theorem GridPresentation.continuousIntegral_after_horizon
    (d : GridPresentation (κ := κ) μ T) {u : ℝ≥0} (hu : T ≤ u) :
    d.continuousIntegral u = d.continuousIntegral T := by
  funext x
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  have hl : d.grid.time k.castSucc ≤ T := by
    exact (d.grid.strictMono_time.monotone (Fin.le_last _)).trans_eq d.terminal_time
  have hr : d.grid.time k.succ ≤ T := by
    exact (d.grid.strictMono_time.monotone (Fin.le_last _)).trans_eq d.terminal_time
  simp only [GridPresentation.continuousTerm, min_eq_right hl, min_eq_right hr,
    min_eq_right (hl.trans hu), min_eq_right (hr.trans hu)]

/-- Finite processes are constant after the horizon. -/
theorem nativeFiniteProcess_after_horizon
    (f : nativeFinitePredictable (κ := κ) μ T) {u : ℝ≥0} (hu : T ≤ u) :
    nativeFiniteProcess μ T f u = nativeFiniteProcess μ T f T := by
  classical
  by_cases h : ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d
  · simp only [nativeFiniteProcess, dite_eq_left h]
    exact h.choose.continuousIntegral_after_horizon μ T hu
  · simp only [nativeFiniteProcess, dite_eq_right h, Pi.zero_apply]

/-- The limit process is constant after the horizon. -/
theorem nativeAdaptedLimit_after_horizon
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) {u : ℝ≥0} (hu : T ≤ u) :
    nativeAdaptedLimit μ T f u = nativeAdaptedLimit μ T f T := by
  funext x
  unfold nativeAdaptedLimit
  congr 1
  funext n
  exact congrFun (nativeFiniteProcess_after_horizon μ T _ hu) x

/-- The limit process at time `u` equals the limit process at time `min u T`. -/
theorem nativeAdaptedLimit_eq_min
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (u : ℝ≥0) :
    nativeAdaptedLimit μ T f u = nativeAdaptedLimit μ T f (min u T) := by
  by_cases hu : u ≤ T
  · rw [min_eq_left hu]
  · rw [min_eq_right (le_of_not_ge hu)]
    exact nativeAdaptedLimit_after_horizon μ T f (le_of_not_ge hu)

/-- The limit process has almost surely continuous paths on all nonnegative times. -/
theorem nativeAdaptedLimit_continuous_all_ae
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous (fun u => nativeAdaptedLimit μ T f u x) := by
  filter_upwards [nativeAdaptedLimit_continuous_ae μ T f] with x hx
  let c : ℝ≥0 → Set.Icc (0 : ℝ≥0) T := fun u => ⟨min u T, zero_le, min_le_right _ _⟩
  have hc : Continuous c := (continuous_id.min continuous_const).subtype_mk _
  have he : (fun u => nativeAdaptedLimit μ T f u x) =
      (fun t : Set.Icc (0 : ℝ≥0) T => nativeAdaptedLimit μ T f t.val x) ∘ c := by
    funext u
    exact congrFun (nativeAdaptedLimit_eq_min μ T f u) x
  rw [he]
  exact hx.comp hc

end BlockBand.SourceProcess.FiniteDriverCompletion
