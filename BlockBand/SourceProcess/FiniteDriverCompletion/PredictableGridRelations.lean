module
public import BlockBand.SourceProcess.FiniteDriverCompletion.PredictableGridEnergy

/-!
# Linearity of predictable classes of grid presentations

Coefficient rectangles are additive and homogeneous in the coefficient, and the predictable
classes of grid presentations respect the sum and scalar multiple of presentations.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open FiniteIto ContinuousItoCommonRefinement PredictableRectangle

namespace PredictableRectangle

theorem coefficientRectangle_add {Ω : Type*} (s t : ℝ≥0) (H K : Ω → ℝ) (x : ℝ × Ω) :
    coefficientRectangle s t (H + K) x = coefficientRectangle s t H x + coefficientRectangle s t K x := by
  by_cases hx : x ∈ Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set Ω) <;>
    simp [coefficientRectangle, hx]

theorem coefficientRectangle_smul {Ω : Type*} (s t : ℝ≥0) (c : ℝ) (H : Ω → ℝ) (x : ℝ × Ω) :
    coefficientRectangle s t (c • H) x = c * coefficientRectangle s t H x := by
  by_cases hx : x ∈ Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set Ω) <;>
    simp [coefficientRectangle, hx]

end PredictableRectangle
namespace GridPresentation
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

theorem scalarPredictable_smul (c : ℝ) (d : GridPresentation (κ := κ) μ T) (a : κ) :
    (d.smul c).scalarPredictable a = c • d.scalarPredictable a := by
  apply (predictableL2_eq_iff_ae_eq _ _).2
  have hc : ((c • d.scalarPredictable a : PredictableL2 enlargedPredictableFiltration T
      (driverLaw (κ := κ) μ)) : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) =
      c • ((d.scalarPredictable a : PredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ)) : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) := rfl
  rw [hc]
  filter_upwards [(d.smul c).scalarPredictable_coeFn a, d.scalarPredictable_coeFn a,
    Lp.coeFn_smul c ((d.scalarPredictable a : PredictableL2 enlargedPredictableFiltration T
      (driverLaw (κ := κ) μ)) : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)))] with x ha hd hs
  rw [ha, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hd]
  change (∑ k, coefficientRectangle (d.grid.time k.castSucc) (d.grid.time k.succ)
    (c • d.coeff k a) x) = c * d.predictableFunction a x
  simp_rw [PredictableRectangle.coefficientRectangle_smul]
  exact (Finset.mul_sum Finset.univ _ _).symm

theorem predictableFamily_smul (c : ℝ) (d : GridPresentation (κ := κ) μ T) :
    (d.smul c).predictableFamily = c • d.predictableFamily := by
  apply PiLp.ext
  intro a
  change (d.smul c).scalarPredictable a = c • d.scalarPredictable a
  exact d.scalarPredictable_smul c a

theorem scalarPredictable_add (d e : GridPresentation (κ := κ) μ T) (a : κ) :
    (d.add e).scalarPredictable a = d.scalarPredictable a + e.scalarPredictable a := by
  let rd := leftCommonRefinement d.grid e.grid
    (d.initial_time.trans e.initial_time.symm) (d.terminal_time.trans e.terminal_time.symm)
  let re := rightCommonRefinement d.grid e.grid
    (d.initial_time.trans e.initial_time.symm) (d.terminal_time.trans e.terminal_time.symm)
  have hp : (d.add e).scalarPredictable a =
      (d.pullback rd).scalarPredictable a + (e.pullback re).scalarPredictable a := by
    apply (predictableL2_eq_iff_ae_eq _ _).2
    have hc : (((d.pullback rd).scalarPredictable a + (e.pullback re).scalarPredictable a :
        PredictableL2 enlargedPredictableFiltration T (driverLaw (κ := κ) μ)) :
        Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) =
        (((d.pullback rd).scalarPredictable a : PredictableL2 enlargedPredictableFiltration T
          (driverLaw (κ := κ) μ)) : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) +
        (((e.pullback re).scalarPredictable a : PredictableL2 enlargedPredictableFiltration T
          (driverLaw (κ := κ) μ)) : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) := rfl
    rw [hc]
    filter_upwards [(d.add e).scalarPredictable_coeFn a,
      (d.pullback rd).scalarPredictable_coeFn a, (e.pullback re).scalarPredictable_coeFn a,
      Lp.coeFn_add
        (((d.pullback rd).scalarPredictable a : PredictableL2 enlargedPredictableFiltration T
          (driverLaw (κ := κ) μ)) : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)))
        (((e.pullback re).scalarPredictable a : PredictableL2 enlargedPredictableFiltration T
          (driverLaw (κ := κ) μ)) : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)))]
        with x ha hd he hs
    rw [ha, hs]
    simp only [Pi.add_apply]
    rw [hd, he]
    change (∑ k, coefficientRectangle ((commonTimeGrid d.grid e.grid).time k.castSucc)
      ((commonTimeGrid d.grid e.grid).time k.succ)
      ((d.pullback rd).coeff k a + (e.pullback re).coeff k a) x) = _
    simp_rw [PredictableRectangle.coefficientRectangle_add]
    exact Finset.sum_add_distrib
  rw [hp, d.scalarPredictable_pullback rd a, e.scalarPredictable_pullback re a]

theorem predictableFamily_add (d e : GridPresentation (κ := κ) μ T) :
    (d.add e).predictableFamily = d.predictableFamily + e.predictableFamily := by
  apply PiLp.ext
  intro a
  change (d.add e).scalarPredictable a = d.scalarPredictable a + e.scalarPredictable a
  exact d.scalarPredictable_add e a

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
