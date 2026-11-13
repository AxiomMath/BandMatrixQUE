module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalDefs
public import BlockBand.SourceProcess.PhysApprox.B3Pins2

/-!
# The moment sums of the local Gram estimate

Measure: `closedLaw b W np` (unconditioned; the cap event is inside `b3Alive`). Steps: the steps
`n_s ≤ j < ⌊W T⌋` without a birth (those of `b3LindebergErr`). Coordinates: Gram coordinates
`Sum.inl c`, `c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)`. Fixed level `R`.

* `CondExpReplace` (abstract): on an a.e.-`m`-measurable set `A`, against an `m`-measurable
  coefficient `g` bounded by `C` on `A`, replacing `X` by `β` costs at most
  `C · ∫⁻ ‖1_A (E[1_A X | m] − β)‖ₑ` (the shape of the errors of `b3SummedErr`).
* `GramMomSumSq`: the summed second moments are eventually bounded, uniformly in `W`
  (Hermitian finite-`W` Gram states give `|ΔX_c|² = ΔX_c ΔX_{c*}`; the bracket error of
  `ComplexClosedSummed` and the bound of `cCov` on feasible states of trace `< R`).
* `GramMomSumCube`: the summed third moments tend to `0` (`η³ ≤ εη² + η⁴/ε`, `GramMomSumSq` and
  `ComplexClosedLindeberg`).
* `GramMomSingle`: the first moment at any single step without a birth tends to `0`.

They are proved as `condExpReplace_holds`, `gramMomSumSq_holds`, `gramMomSumCube_holds` and
`gramMomSingle_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-- The steps `n_s ≤ j < ⌊W T⌋` without a birth. -/
def nbSteps (s T : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W : ℕ) : Finset ℕ :=
  (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => ¬ IsBirthStep τ W j)

/-- **`CondExpReplace`** (abstract): replacing `X` by `β` against a bounded `m`-measurable
coefficient on an a.e.-`m`-measurable set costs the conditional error. -/
def CondExpReplace : Prop :=
  ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω), m ≤ mΩ → ∀ (A A' : Set Ω), MeasurableSet[m] A' → A =ᵐ[μ] A' →
    ∀ (g : Ω → ℂ), StronglyMeasurable[m] g → ∀ C : ℝ, (∀ ω ∈ A, ‖g ω‖ ≤ C) →
    ∀ (X β : Ω → ℂ), Integrable (A.indicator X) μ → AEStronglyMeasurable β μ →
      ‖(∫ ω, A.indicator (fun ω => g ω * X ω) ω ∂μ) -
          ∫ ω, A.indicator (fun ω => g ω * β ω) ω ∂μ‖ₑ ≤
        ENNReal.ofReal C * ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator X | m] ω - β ω) ω‖ₑ ∂μ

/-- **`GramMomSumSq`**: for every level `R` and Gram coordinate `c`, the summed second
moments of the closed increments on the alive set, away from the births, are eventually bounded
by a constant independent of `W`. -/
def GramMomSumSq : Prop :=
  ComplexClosedSummed → ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    ∃ C : ℝ, ∀ᶠ W in atTop,
      ∑ j ∈ nbSteps s T τ W, ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl c) y‖ₑ ^ 2) y ∂closedLaw b W np ≤
        ENNReal.ofReal C

/-- **`GramMomSumCube`**: the summed third moments tend to `0`. -/
def GramMomSumCube : Prop :=
  ComplexClosedSummed → ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    Tendsto (fun W => ∑ j ∈ nbSteps s T τ W, ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl c) y‖ₑ ^ 3) y ∂closedLaw b W np)
      atTop (𝓝 0)

/-- **`GramMomSingle`**: at any single step without a birth, the first moment tends
to `0`. -/
def GramMomSingle : Prop :=
  ComplexClosedSummed → ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np))
    (jW : ℕ → ℕ), (∀ᶠ W in atTop, jW W ∈ nbSteps s T τ W) →
    Tendsto (fun W => ∫⁻ y, (b3Alive b E s h τ m R W (jW W) (Vs W)).indicator
        (fun y => ‖b3dX b E s h τ m W (jW W) (Vs W) (Sum.inl c) y‖ₑ) y ∂closedLaw b W np)
      atTop (𝓝 0)

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
