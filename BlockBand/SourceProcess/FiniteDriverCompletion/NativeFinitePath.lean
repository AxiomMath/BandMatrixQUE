module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeFiniteDifferenceTail
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Finite processes as continuous paths on the horizon

The finite process of a finite-grid class, restricted to `[0, T]`, is a measurable map into the
continuous functions with the uniform norm, and the uniform distance between two such paths is
controlled in probability by the predictable energy of the difference.
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

/-- The finite process as a continuous path on `[0, T]`. -/
def nativeFinitePath (f : nativeFinitePredictable (κ := κ) μ T) (x : DriverSample S κ) :
    C(Set.Icc (0 : ℝ≥0) T, ℝ) where
  toFun t := nativeFiniteProcess μ T f t.val x
  continuous_toFun := (nativeFiniteProcess_continuous μ T f x).comp continuous_subtype_val

/-- The path-valued finite process is measurable. -/
theorem nativeFinitePath_measurable (f : nativeFinitePredictable (κ := κ) μ T) :
    Measurable (nativeFinitePath μ T f) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  exact (nativeFiniteProcess_adapted μ T f t.val).mono
    ((commonWienerFiltration S κ).le t.val) le_rfl

/-- The uniform-distance tail event is the supremum event of the difference process. -/
theorem nativeFinitePath_tail_eq (f g : nativeFinitePredictable (κ := κ) μ T) (ε : ℝ≥0) :
    {x | (ε : ℝ) < ‖nativeFinitePath μ T f x - nativeFinitePath μ T g x‖} =
    {x | ∃ u ≤ T, ((ε^2 : ℝ≥0) : ℝ) <
      (nativeFiniteProcess μ T f u x - nativeFiniteProcess μ T g u x)^2} := by
  classical
  have hsq (z : ℝ) : (ε : ℝ) < ‖z‖ ↔ ((ε^2 : ℝ≥0) : ℝ) < z^2 := by
    rw [NNReal.coe_pow, Real.norm_eq_abs, ← sq_abs z]
    exact (sq_lt_sq₀ (NNReal.coe_nonneg ε) (abs_nonneg z)).symm
  ext x
  constructor
  · intro hx
    have ht : ∃ t : Set.Icc (0 : ℝ≥0) T,
        (ε : ℝ) < ‖(nativeFinitePath μ T f x - nativeFinitePath μ T g x) t‖ := by
      by_contra hn
      push Not at hn
      exact not_lt_of_ge ((ContinuousMap.norm_le _ (NNReal.coe_nonneg ε)).2 hn) hx
    rcases ht with ⟨t, ht⟩
    exact ⟨t.val, t.property.2, (hsq _).1 ht⟩
  · rintro ⟨u, hu, hx⟩
    let t : Set.Icc (0 : ℝ≥0) T := ⟨u, zero_le, hu⟩
    have ht : (ε : ℝ) < ‖(nativeFinitePath μ T f x - nativeFinitePath μ T g x) t‖ :=
      (hsq _).2 hx
    exact ht.trans_le ((nativeFinitePath μ T f x - nativeFinitePath μ T g x).norm_coe_le_norm t)

/-- The uniform path distance is controlled by the predictable energy of the difference. -/
theorem nativeFinitePath_maximal_tail (f g : nativeFinitePredictable (κ := κ) μ T) (ε : ℝ≥0) :
    (ε^2 : ℝ≥0) * (driverLaw (κ := κ) μ)
      {x | (ε : ℝ) < ‖nativeFinitePath μ T f x - nativeFinitePath μ T g x‖} ≤
      ENNReal.ofReal (‖f.val - g.val‖^2) := by
  rw [nativeFinitePath_tail_eq μ T f g ε]
  exact nativeFiniteProcess_difference_tail μ T f g ε

end BlockBand.SourceProcess.FiniteDriverCompletion
