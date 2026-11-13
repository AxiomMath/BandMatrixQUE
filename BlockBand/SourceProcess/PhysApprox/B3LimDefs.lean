module

public import BlockBand.SourceProcess.PhysApprox.B3Pins2
public import BlockBand.SourceProcess.PhysApprox.PinsIdent
public import BlockBand.SourceProcess.CapCond.Defs

/-!
# The conditioned complex cap limit

* `condClosedPhysExpectation`: `cappedClosedPhysExpectation / P_W(physCapEventC)` (`0` if null);
* `ComplexCapCondLaw`: for `0 < h < 1` with no atom of any `t_k(μ(s))` at `h²` (`NoAtom`),
  frequently in `K`, if `P(μ(s) ∈ capSet K h) ≠ 0`, every limit point of the conditioned
  expectation is `modelExpectation` of some filtered `IsFiniteComplexSourceModel` with entrance
  `μ(s)[|capSet K h]`;
* `ComplexCapCondLawStopped`: the same with `IsStoppedTestedComplexModel` (no filtration; stopped
  tested identities). It implies `ComplexCapCondLaw` by
  `IsStoppedTestedComplexModel.isFiniteComplexSourceModel`;
* `TargetCapCondLaw'`: `TargetCapCond'` with conclusion `ComplexCapCondLaw` (it implies
  `TargetCapCond'`);
* `ComplexClosedFeasible`: exact `GramFeasible` of the finite-`W` closed Gram process on the cap
  event at every length `j ≥ n_s`, almost surely. It is a separate hypothesis of the limit
  passage; it is proved in `complexClosedFeasible_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-- **The closed expectation conditioned on the physical cap event** (`0` if the event is
null). -/
def condClosedPhysExpectation (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (K W : ℕ) : ℝ :=
  cappedClosedPhysExpectation b E s T h τ m Φ K W /
    (growthPathLaw W b (physCapEventC b E s h K W)).toReal

/-- **The conditioned complex cap limit** (on the cap event `{t_K ≤ h²}`; complex copy of
`CapCond.CapCondLaw`). For non-atomic `0 < h < 1`, frequently in `K`, if the cap event has
positive entrance probability, every limit point `ℓ` of the conditioned closed expectation along
`W_n → ∞` is the value at `T − s` of some filtered complex finite model with entrance `μ(s)`
conditioned on `capSet K h`. -/
def ComplexCapCondLaw : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ h : ℝ, 0 < h → h < 1 → CapCond.NoAtom (entranceLaw P μ s) h →
  ∃ᶠ K in atTop, entranceLaw P μ s (capSet K h) ≠ 0 →
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ ℓ : ℝ,
      Tendsto (fun n => condClosedPhysExpectation b E s T h τ m Φ K (φ n)) atTop (𝓝 ℓ) →
      ∃ (Ω' : Type) (mΩ : MeasurableSpace Ω') (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω')
        (tseq : Ω' → ℕ → ℝ) (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
        (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
        IsFiniteComplexSourceModel b E s τ m h K ((entranceLaw P μ s)[|capSet K h]) 𝓖 Q
          tseq G Kc ∧
        modelExpectation K s T Q G Kc Φ = ℓ

/-- **The conditioned complex cap limit, stopped tested form**: `ComplexCapCondLaw` with the
stopped tested model `IsStoppedTestedComplexModel` (no filtration; every martingale clause tested
after the Gram trace stop) in place of the filtered model. -/
def ComplexCapCondLawStopped : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ h : ℝ, 0 < h → h < 1 → CapCond.NoAtom (entranceLaw P μ s) h →
  ∃ᶠ K in atTop, entranceLaw P μ s (capSet K h) ≠ 0 →
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ ℓ : ℝ,
      Tendsto (fun n => condClosedPhysExpectation b E s T h τ m Φ K (φ n)) atTop (𝓝 ℓ) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
        (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
        (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
        IsStoppedTestedComplexModel b E s τ m h K ((entranceLaw P μ s)[|capSet K h]) Q
          tseq G Kc ∧
        modelExpectation K s T Q G Kc Φ = ℓ

/-- **The conditioned limit passage**: `TargetCapCond'` with the conditioned conclusion
`ComplexCapCondLaw`. It implies `TargetCapCond'` (`targetCapCond'_of_law`). -/
def TargetCapCondLaw' : Prop :=
  TransmissionLawContract → ExistsTimeSFrame → ComplexClosedSummed → ComplexClosedTight →
    ComplexKStoppedMomentMax → ComplexClosedCurrent → ComplexClosedLindeberg →
    ComplexCapCondLaw

/-- **`ComplexClosedFeasible`** (the projection identity): for every admissible time-`s` frame,
eventually in `W`, almost surely on the cap event, the closed Gram state is `GramFeasible` for the
source signature at every length `j ≥ n_s`. It is the finite-`W` input of the `feasible` field of
the limit model; it is **not** a hypothesis of `TargetCapCond'`, only an explicit hypothesis of
the passage theorems. It is proved as `complexClosedFeasible_holds`.
-/
def ComplexClosedFeasible : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop, ∀ᵐ y ∂closedLaw b W np,
      y.1.1 ∈ physCapEventC b E s h K W → ∀ j, closeLen s W ≤ j →
        GramFeasible (srcSignature K (Fin np)) (b3ClosedGramAt b E s h τ m W j (Vs W) y)

end BlockBand.SourceProcess.PhysApprox.B3
