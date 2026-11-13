module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeGridIntegral

/-!
# Continuous-time finite-grid stochastic sums

For a grid presentation with past-measurable coefficients, the stopped increments
`H_{k,a}(W_a(t_{k+1} ∧ u) - W_a(t_k ∧ u))` and their sum `continuousIntegral u` have continuous
paths and are adapted to the enlarged filtration.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}
namespace GridPresentation

/-- The stopped-increment process of one coefficient. -/
def continuousTerm (d : GridPresentation (κ := κ) μ T) (k : Fin d.steps) (a : κ)
    (u : ℝ≥0) (x : DriverSample S κ) : ℝ :=
  d.coeff k a x * (commonRealBrownian (min u (d.grid.time k.succ)) x a -
    commonRealBrownian (min u (d.grid.time k.castSucc)) x a)

omit [IsProbabilityMeasure μ] in
/-- Stopped increments have continuous paths for every sample. -/
theorem continuousTerm_continuous (d : GridPresentation (κ := κ) μ T)
    (k : Fin d.steps) (a : κ) (x : DriverSample S κ) :
    Continuous (fun u => d.continuousTerm k a u x) :=
  continuous_const.mul (((x.2 a).continuous.comp (continuous_id.min continuous_const)).sub
    ((x.2 a).continuous.comp (continuous_id.min continuous_const)))

omit [IsProbabilityMeasure μ] in
/-- Stopped increments are adapted to the (uncompleted) enlarged filtration. -/
theorem continuousTerm_adapted (d : GridPresentation (κ := κ) μ T)
    (k : Fin d.steps) (a : κ) (u : ℝ≥0) :
    Measurable[commonWienerFiltration S κ u] (d.continuousTerm k a u) := by
  by_cases hu : u ≤ d.grid.time k.castSucc
  · have hr : u ≤ d.grid.time k.succ := hu.trans
      (d.grid.strictMono_time k.castSucc_lt_succ).le
    have he : d.continuousTerm k a u = 0 := by
      funext x
      simp [continuousTerm, min_eq_left hu, min_eq_left hr]
    rw [he]
    exact measurable_const
  · have hl : d.grid.time k.castSucc ≤ u := (lt_of_not_ge hu).le
    have hm (r : ℝ≥0) : Measurable[commonWienerFiltration S κ u]
        (fun x : DriverSample S κ => commonRealBrownian (min u r) x a) :=
      ((measurable_pi_apply a).comp (commonRealBrownian_adapted (min u r))).mono
        ((commonWienerFiltration S κ).mono (min_le_left _ _)) le_rfl
    exact ((d.adapted k a).mono ((commonWienerFiltration S κ).mono hl) le_rfl).mul
      ((hm _).sub (hm _))

/-- The continuous finite-grid stochastic sum at time `u`. -/
def continuousIntegral (d : GridPresentation (κ := κ) μ T) (u : ℝ≥0)
    (x : DriverSample S κ) : ℝ := ∑ k, ∑ a, d.continuousTerm k a u x

omit [IsProbabilityMeasure μ] in
theorem continuousIntegral_continuous (d : GridPresentation (κ := κ) μ T)
    (x : DriverSample S κ) : Continuous (fun u => d.continuousIntegral u x) := by
  exact continuous_finsetSum _ (fun k _ => continuous_finsetSum _
    (fun a _ => d.continuousTerm_continuous k a x))

omit [IsProbabilityMeasure μ] in
theorem continuousIntegral_adapted (d : GridPresentation (κ := κ) μ T) (u : ℝ≥0) :
    Measurable[commonWienerFiltration S κ u] (d.continuousIntegral u) := by
  exact Finset.measurable_sum _ (fun k _ => Finset.measurable_sum _
    (fun a _ => d.continuousTerm_adapted k a u))

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
