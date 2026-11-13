module
public import BlockBand.SourceProcess.FiniteDriverCompletion.FullNativeOperator
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeGridMartingale
public import BlockBand.SourceProcess.FiniteDriverCompletion.ContinuousGridRelations

/-!
# The finite process of a finite-grid class

Every finite-grid class is zero or has a grid presentation; `nativeFiniteProcess` is the
continuous grid sum of a chosen presentation. It has continuous paths, is adapted, is a
square-integrable martingale under the driver law, and at the horizon agrees almost surely with the
finite-grid integral.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)

/-- Every finite-grid class is zero or has a grid presentation. -/
theorem nativeFinite_zero_or_presentation (f : nativeFinitePredictable (κ := κ) μ T) :
    f = 0 ∨ ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d := by
  rcases f.property with ⟨z, hz, he⟩
  change z.2 = f.val at he
  rcases nativeGraph_zero_or_presentation μ T hz with hz0 | ⟨d, hd⟩
  · left
    apply Subtype.ext
    exact he.symm.trans (congrArg Prod.snd hz0)
  · right
    refine ⟨d, ?_⟩
    apply Subtype.ext
    exact he.symm.trans (congrArg Prod.snd hd)

/-- The finite process of a finite-grid class: the continuous grid sum of a chosen presentation,
and zero for the zero class. -/
def nativeFiniteProcess (f : nativeFinitePredictable (κ := κ) μ T) :
    ℝ≥0 → DriverSample S κ → ℝ := by
  classical
  exact if h : ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d then
    h.choose.continuousIntegral else 0

/-- Finite processes have continuous paths for every sample. -/
theorem nativeFiniteProcess_continuous (f : nativeFinitePredictable (κ := κ) μ T)
    (x : DriverSample S κ) : Continuous (fun u => nativeFiniteProcess μ T f u x) := by
  classical
  by_cases h : ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d
  · simpa only [nativeFiniteProcess, dite_eq_left h] using h.choose.continuousIntegral_continuous x
  · simpa only [nativeFiniteProcess, dite_eq_right h, Pi.zero_apply] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))

/-- Finite processes are adapted to the enlarged filtration. -/
theorem nativeFiniteProcess_adapted (f : nativeFinitePredictable (κ := κ) μ T) (u : ℝ≥0) :
    Measurable[commonWienerFiltration S κ u] (nativeFiniteProcess μ T f u) := by
  classical
  by_cases h : ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d
  · simpa only [nativeFiniteProcess, dite_eq_left h] using h.choose.continuousIntegral_adapted u
  · simp only [nativeFiniteProcess, dite_eq_right h, Pi.zero_apply]
    exact @measurable_zero ℝ (DriverSample S κ) inferInstance
      (commonWienerFiltration S κ u) inferInstance

/-- The finite process is a martingale under the driver law. -/
theorem nativeFiniteProcess_martingale (f : nativeFinitePredictable (κ := κ) μ T) :
    Martingale (nativeFiniteProcess μ T f) (commonWienerFiltration S κ) (driverLaw (κ := κ) μ) := by
  classical
  by_cases h : ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d
  · simpa only [nativeFiniteProcess, dite_eq_left h] using h.choose.continuousIntegral_martingale
  · simpa only [nativeFiniteProcess, dite_eq_right h, Pi.zero_apply] using
      (martingale_zero ℝ (commonWienerFiltration S κ) (driverLaw (κ := κ) μ))

/-- The finite process is square integrable at every time. -/
theorem nativeFiniteProcess_memLp (f : nativeFinitePredictable (κ := κ) μ T) (u : ℝ≥0) :
    MemLp (nativeFiniteProcess μ T f u) 2 (driverLaw (κ := κ) μ) := by
  classical
  by_cases h : ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d
  · simpa only [nativeFiniteProcess, dite_eq_left h] using h.choose.continuousIntegral_memLp u
  · simpa only [nativeFiniteProcess, dite_eq_right h, Pi.zero_apply] using
      (MemLp.zero : MemLp (fun _ : DriverSample S κ => (0 : ℝ)) 2 (driverLaw (κ := κ) μ))

/-- At the horizon, the finite process agrees almost surely with the finite-grid integral. -/
theorem nativeFiniteProcess_terminal (f : nativeFinitePredictable (κ := κ) μ T) :
    (nativeFiniteIntegral (κ := κ) μ T f : DriverSample S κ → ℝ)
      =ᵐ[driverLaw (κ := κ) μ] nativeFiniteProcess μ T f T := by
  classical
  by_cases h : ∃ d : GridPresentation (κ := κ) μ T, f = nativePresentationClass μ T d
  · have he : nativeFiniteProcess μ T f T = h.choose.integral := by
      funext x
      simp only [nativeFiniteProcess, dite_eq_left h, h.choose.continuousIntegral_terminal]
    have hi : nativeFiniteIntegral (κ := κ) μ T f = h.choose.integralLp := by
      exact (congrArg (nativeFiniteIntegral (κ := κ) μ T) h.choose_spec).trans
        (nativeFiniteIntegral_presentation μ T h.choose)
    rw [he, hi]
    exact h.choose.integralLp_coeFn
  · have hf : f = 0 := (nativeFinite_zero_or_presentation μ T f).resolve_right h
    have he : nativeFiniteProcess μ T f T = 0 := by
      funext x
      simp only [nativeFiniteProcess, dite_eq_right h, Pi.zero_apply]
    have hi : nativeFiniteIntegral (κ := κ) μ T f = 0 :=
      (congrArg (nativeFiniteIntegral (κ := κ) μ T) hf).trans
        (nativeFiniteIntegral (κ := κ) μ T).map_zero
    rw [he, hi]
    exact Lp.coeFn_zero ℝ 2 (driverLaw (κ := κ) μ)

end BlockBand.SourceProcess.FiniteDriverCompletion
