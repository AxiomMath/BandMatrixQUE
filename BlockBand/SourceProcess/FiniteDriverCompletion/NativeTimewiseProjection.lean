module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeFiniteProcess
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Timewise projections of the terminal integral

`nativeTimewiseProjection`: the conditional `L²` projection of the Itô integral onto the enlarged
past at a time `u ≤ T`. It is bounded by the predictable energy, and for a finite-grid class it is
the finite process at time `u`.
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

/-- The conditional `L²` projection of the terminal integral onto the enlarged past at time `u`. -/
def nativeTimewiseProjection
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (u : ℝ≥0) :
    NativeRandomL2 (κ := κ) μ :=
  (condExpL2 ℝ ℝ ((commonWienerFiltration S κ).le u)
    (fullNativeIntegral (κ := κ) μ T f) : NativeRandomL2 (κ := κ) μ)

/-- The timewise projection is bounded by the predictable energy. -/
theorem nativeTimewiseProjection_norm
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (u : ℝ≥0) :
    ‖nativeTimewiseProjection μ T f u‖ ≤ ‖f‖ := by
  exact (norm_condExpL2_coe_le ((commonWienerFiltration S κ).le u)
    (fullNativeIntegral (κ := κ) μ T f)).trans_eq (fullNativeIntegral_norm μ T f)

/-- The conditional mean of a finite-grid integral is its finite process. -/
theorem nativeFiniteProcess_condExp_terminal
    (f : nativeFinitePredictable (κ := κ) μ T) {u : ℝ≥0} (hu : u ≤ T) :
    (driverLaw (κ := κ) μ)[(nativeFiniteIntegral (κ := κ) μ T f : DriverSample S κ → ℝ) |
      commonWienerFiltration S κ u] =ᵐ[driverLaw (κ := κ) μ]
      nativeFiniteProcess μ T f u := by
  exact (condExp_congr_ae (nativeFiniteProcess_terminal μ T f)).trans
    ((nativeFiniteProcess_martingale μ T f).condExp_ae_eq hu)

/-- For a finite-grid class, the timewise projection equals the finite process at each time up to
the horizon. -/
theorem nativeFiniteProcess_condExpL2_terminal
    (f : nativeFinitePredictable (κ := κ) μ T) {u : ℝ≥0} (hu : u ≤ T) :
    (condExpL2 ℝ ℝ ((commonWienerFiltration S κ).le u)
      (nativeFiniteIntegral (κ := κ) μ T f) : DriverSample S κ → ℝ)
      =ᵐ[driverLaw (κ := κ) μ] nativeFiniteProcess μ T f u := by
  have h := (Lp.memLp (nativeFiniteIntegral (κ := κ) μ T f)).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) ((commonWienerFiltration S κ).le u)
  rw [Lp.toLp_coeFn] at h
  exact h.trans (nativeFiniteProcess_condExp_terminal μ T f hu)

end BlockBand.SourceProcess.FiniteDriverCompletion
