module
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionMain
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Nonexplosion

`nonexplosionFor_holds`: `NonexplosionFor μ E` holds for `S κ : Type`, by
`nonexplosionFor_of_ito` and the Itô formula `semimartingaleItoFormula_holds`.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory

/-- **Nonexplosion holds** (for `S κ : Type`). -/
theorem nonexplosionFor_holds {S κ : Type} [MeasurableSpace S] [Fintype κ]
    (μ : Measure S) [IsProbabilityMeasure μ] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    NonexplosionFor (κ := κ) μ E :=
  nonexplosionFor_of_ito μ E SemimartingaleIto.semimartingaleItoFormula_holds

end BlockBand.SourceProcess.Stochastic.NativeSDE
