module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeProcessInterface

/-!
# Initial values and agreement with finite processes

The finite-grid sums, the finite processes and the limit process all start at zero, and for a
finite-grid class the limit process agrees almost surely with its finite process at every time.
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
/-- The continuous grid sum starts at zero for every sample. -/
theorem GridPresentation.continuousIntegral_initial
    (d : GridPresentation (κ := κ) μ T) : d.continuousIntegral 0 = 0 := by
  funext x
  have h0 (r : ℝ≥0) : min 0 r = 0 := min_eq_left zero_le
  simp only [GridPresentation.continuousIntegral, GridPresentation.continuousTerm,
    h0, sub_self, mul_zero, Finset.sum_const_zero, Pi.zero_apply]

/-- The finite process starts at zero. -/
theorem nativeFiniteProcess_initial
    (f : nativeFinitePredictable (κ := κ) μ T) : nativeFiniteProcess μ T f 0 = 0 := by
  classical
  by_cases h : ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d
  · simp only [nativeFiniteProcess, dite_eq_left h]
    exact h.choose.continuousIntegral_initial μ T
  · simp only [nativeFiniteProcess, dite_eq_right h, Pi.zero_apply]

/-- The limit process starts at zero for every sample. -/
theorem nativeAdaptedLimit_initial
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    nativeAdaptedLimit μ T f 0 = 0 := by
  funext x
  have ht : Tendsto (fun n => nativeFiniteProcess μ T (nativeFiniteApproximation μ T f n) 0 x)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [nativeFiniteProcess_initial, Pi.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact ht.limUnder_eq

/-- For a finite-grid class, the limit process agrees almost surely with the finite process at
every time. -/
theorem nativeAdaptedLimit_finite_ae
    (f : nativeFinitePredictable (κ := κ) μ T) (u : ℝ≥0) :
    nativeAdaptedLimit μ T f.val u =ᵐ[driverLaw (κ := κ) μ] nativeFiniteProcess μ T f u := by
  have h (v : ℝ≥0) (hv : v ≤ T) :
      nativeAdaptedLimit μ T f.val v =ᵐ[driverLaw (κ := κ) μ] nativeFiniteProcess μ T f v := by
    have hc := nativeAdaptedLimit_condExp_all μ T f.val v
    rw [fullNativeIntegral_finite] at hc
    exact hc.symm.trans (nativeFiniteProcess_condExp_terminal μ T f hv)
  by_cases hu : u ≤ T
  · exact h u hu
  · rw [nativeAdaptedLimit_after_horizon μ T f.val (le_of_not_ge hu),
      nativeFiniteProcess_after_horizon μ T f (le_of_not_ge hu)]
    exact h T le_rfl

end BlockBand.SourceProcess.FiniteDriverCompletion
