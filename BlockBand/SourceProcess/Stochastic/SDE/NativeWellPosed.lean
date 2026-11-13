module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeLocalExit
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Local strong well-posedness on the driver space

`localWellPosednessFor_holds : LocalWellPosednessFor μ E` for every old-state space `S`,
finite noise index `κ`, probability `μ` and finite-dimensional real normed `E` with Borel
σ-algebra. Measure `driverLaw μ = μ ⊗ Wiener^κ`; filtration `F_t ∨ N`; solutions are native
Itô processes (`IsNativeItoProcess`); no integrability of `ξ` is assumed.

It assembles three results proved in sibling modules:
`exists_solutionUntil_exitTime` (existence until the own exit time),
`ae_eq_of_isSDESolutionUntil_exitTime` (uniqueness until the exit time) and
`ae_eq_of_isSDESolution` (global pathwise uniqueness).

Dependency chain: the continuous stopped integral → horizon consistency → isometry/linearity →
Gronwall uniqueness → Picard iteration on `L²(dt ⊗ P)` (`SDE.picard_fixedPoint`) → global
Lipschitz solutions → truncation and exit times.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory

/-- **Local strong well-posedness holds.** -/
theorem localWellPosednessFor_holds {S κ : Type*} [MeasurableSpace S] [Fintype κ]
    (μ : Measure S) [IsProbabilityMeasure μ] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    LocalWellPosednessFor (κ := κ) μ E := fun _ _ hb hσ _ hξ =>
  ⟨fun R => exists_solutionUntil_exitTime hb hσ hξ R,
    fun _ _ _ hX hY => ae_eq_of_isSDESolutionUntil_exitTime hb hσ hX hY,
    fun _ _ hX hY => ae_eq_of_isSDESolution hb hσ hX hY⟩

end BlockBand.SourceProcess.Stochastic.NativeSDE
