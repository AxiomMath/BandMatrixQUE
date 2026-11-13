module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeGridIntegral

/-!
# Conditional means of driver steps at earlier times

A driver step after time `s` with a coefficient measurable at time `s` has conditional mean zero
given the enlarged past at any earlier time `r ≤ s`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ]

/-- A future driver increment has conditional mean zero given every earlier enlarged past (by the
tower property). -/
theorem driverStep_condExp_earlier (r s u : ℝ≥0) (hrs : r ≤ s) (a : κ)
    {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    (driverLaw (κ := κ) μ)[driverStep s u a H | commonWienerFiltration S κ r]
      =ᵐ[driverLaw (κ := κ) μ] 0 := by
  have ht := condExp_condExp_of_le
    (μ := driverLaw (κ := κ) μ) (f := driverStep s u a H)
    ((commonWienerFiltration S κ).mono hrs) ((commonWienerFiltration S κ).le s)
  have hz := condExp_congr_ae (m := commonWienerFiltration S κ r)
    (driverStep_condExp μ s u a hH hHL2)
  exact ht.symm.trans (hz.trans (Eventually.of_forall (fun x => by simp)))

end BlockBand.SourceProcess.FiniteDriverCompletion
