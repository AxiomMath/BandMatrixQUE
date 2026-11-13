module
public import BlockBand.SourceProcess.Stochastic.Assembly.NonexplosionExitU
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionMain
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Nonexplosion from the Itô formula

`NonexplosionFor μ E` follows from the universe-polymorphic Itô formula
(`nonexplosionFor_of_itoU`), and hence holds unconditionally (`nonexplosionFor_holdsU`).

1. Strong exit-time solutions `X^n` of radius `n` (`exists_solutionUntil_exitTime_strong`); each
   stays in `K` by the invariance hypothesis.
2. Exit times escape (`ae_exists_lt_exitTimeU`): coordinates, the bridge to the Itô process, the
   Itô formula with `U = univ` and `φ(t,y) = e^{-ct}(1 + Φ(L⁻¹y))`, `c = max C 0`, whose Itô
   drift is `≤ 0` on `K`; localization of `ξ` on `{‖ξ‖ ≤ r}`; coercivity.
3. Gluing by radius consistency (`exists_isSDESolution_of_family`).

The hypotheses `IsClosed K` and `ξ ∈ K` a.s. of `NonexplosionFor` are not needed (they follow
from, or are subsumed by, the invariance of `K` under exit-time solutions).
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory
open BlockBand.Internal.Contracts.Transmission

universe u v

/-- **Nonexplosion** `NonexplosionFor μ E`, given the Itô formula `SemimartingaleItoFormulaU` in
the universe `max u v`. -/
theorem nonexplosionFor_of_itoU {S : Type u} {κ : Type v} [MeasurableSpace S] [Fintype κ]
    (μ : Measure S) [IsProbabilityMeasure μ] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hIto : ∀ d, SemimartingaleIto.SemimartingaleItoFormulaU.{max u v} d) : NonexplosionFor (κ := κ) μ E := by
  intro b σ hb hσ ξ hξ K _ _ hinv Φ C hΦ hΦK hcoer hgen
  choose X hX using fun n : ℕ => exists_solutionUntil_exitTime_strong hb hσ hξ (n : ℝ)
  exact exists_isSDESolution_of_family hb hσ hξ hX
    (ae_exists_lt_exitTimeU (hIto _) hξ hΦ hΦK hcoer hgen hX fun n => hinv n (X n) (hX n).sol)

end BlockBand.SourceProcess.Stochastic.NativeSDE

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
universe u' v'
/-- **Nonexplosion in every universe**: `NonexplosionFor μ E` for `S : Type u`, `κ : Type v`. -/
theorem nonexplosionFor_holdsU {S : Type u'} {κ : Type v'} [MeasurableSpace S] [Fintype κ]
    (μ : MeasureTheory.Measure S) [MeasureTheory.IsProbabilityMeasure μ] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] : NonexplosionFor (κ := κ) μ E :=
  nonexplosionFor_of_itoU μ E fun d => SemimartingaleIto.semimartingaleItoFormulaU_holds d
end BlockBand.SourceProcess.Stochastic.NativeSDE
