module
public import BlockBand.SourceProcess.FiniteDriverCompletion.FullPredictableDensity

/-!
# The Itô integral on all predictable families

Since the finite-grid classes are dense, the closure is the whole space of predictable
`L²` families, and the Itô integral extends to an isometry `fullNativeIntegral` from predictable
families to `L²` of the driver law, agreeing with the finite-grid sums.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)

/-- The inclusion of the whole predictable family space into the closure. -/
def fullNativeClosureEmbedding : PredictableFamily (S := S) (κ := κ) (μ := μ) T →ₗᵢ[ℝ]
    nativeClosedPredictable (κ := κ) μ T where
  toFun f := ⟨f, by
    classical
    rw [nativeClosedPredictable_eq_top]
    trivial⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The terminal Itô integral on the whole space of enlarged predictable families, under `dt` times
the law of the old state and the independent finite family of Wiener paths. -/
def fullNativeIntegral : PredictableFamily (S := S) (κ := κ) (μ := μ) T →ₗᵢ[ℝ]
    NativeRandomL2 (κ := κ) μ :=
  (nativeClosedIntegral (κ := κ) μ T).comp (fullNativeClosureEmbedding (κ := κ) μ T)

/-- The integral of a finite-grid family is its finite stochastic sum, in `L²`. -/
theorem fullNativeIntegral_presentation (d : GridPresentation (κ := κ) μ T) :
    fullNativeIntegral (κ := κ) μ T d.predictableFamily = d.integralLp := by
  have he : fullNativeClosureEmbedding (κ := κ) μ T d.predictableFamily =
      nativeClosureEmbedding (κ := κ) μ T (nativePresentationClass μ T d) := rfl
  change nativeClosedIntegral (κ := κ) μ T
    (fullNativeClosureEmbedding (κ := κ) μ T d.predictableFamily) = _
  rw [he, nativeClosedIntegral_presentation]

/-- The Itô isometry for every predictable family. -/
theorem fullNativeIntegral_norm (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    ‖fullNativeIntegral (κ := κ) μ T f‖ = ‖f‖ :=
  (fullNativeIntegral (κ := κ) μ T).norm_map f

end BlockBand.SourceProcess.FiniteDriverCompletion
