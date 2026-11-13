module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeFiniteProcess
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# The adapted limit of finite-grid approximants

Every predictable family is approximated by finite-grid classes at a geometric rate; the timewise
limit of the corresponding finite processes, defined at each time with a default value, is adapted
to the enlarged filtration.
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

/-- Finite-grid classes approximate every predictable family. -/
theorem exists_nativeFinite_near (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T)
    (ε : ℝ) (hε : 0 < ε) : ∃ g : nativeFinitePredictable (κ := κ) μ T, dist f g.val < ε := by
  classical
  have hf : f ∈ nativeClosedPredictable (κ := κ) μ T := by
    rw [nativeClosedPredictable_eq_top]
    trivial
  change f ∈ closure (nativeFinitePredictable (κ := κ) μ T :
    Set (PredictableFamily (S := S) (κ := κ) (μ := μ) T)) at hf
  rcases Metric.mem_closure_iff.1 hf ε hε with ⟨g, hg, hd⟩
  exact ⟨⟨g, hg⟩, hd⟩

/-- A choice of finite-grid approximants. -/
def nativeFiniteApproximation (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T)
    (n : ℕ) : nativeFinitePredictable (κ := κ) μ T :=
  (exists_nativeFinite_near μ T f ((1 / 8 : ℝ)^(n + 1)) (by positivity)).choose

/-- The approximation rate of `nativeFiniteApproximation`. -/
theorem nativeFiniteApproximation_rate (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T)
    (n : ℕ) : dist f (nativeFiniteApproximation μ T f n).val < (1 / 8 : ℝ)^(n + 1) :=
  (exists_nativeFinite_near μ T f ((1 / 8 : ℝ)^(n + 1)) (by positivity)).choose_spec

/-- The timewise limit of the finite processes, with a default value where the limit does not
exist, taken separately at each time. -/
def nativeAdaptedLimit (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T)
    (u : ℝ≥0) (x : DriverSample S κ) : ℝ :=
  limUnder atTop (fun n : ℕ => nativeFiniteProcess μ T (nativeFiniteApproximation μ T f n) u x)

/-- The timewise limit is adapted to the (uncompleted) enlarged filtration. -/
theorem nativeAdaptedLimit_adapted (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T)
    (u : ℝ≥0) : Measurable[commonWienerFiltration S κ u] (nativeAdaptedLimit μ T f u) := by
  let : MeasurableSpace (DriverSample S κ) := commonWienerFiltration S κ u
  exact (StronglyMeasurable.limUnder (fun n : ℕ =>
    (nativeFiniteProcess_adapted μ T (nativeFiniteApproximation μ T f n) u).stronglyMeasurable)).measurable

end BlockBand.SourceProcess.FiniteDriverCompletion
