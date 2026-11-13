module

public import BlockBand.SourceProcess.PhysApprox.B3LimObs

/-!
# The conditioned fdd limit at all times

`ComplexCapFdd` freezes the observables after `T` (`limLen`) and tests the finite-dimensional
distributions only at model times `s + u ≤ max(s, T)`. The complex estimates hold at every
`T' ≥ T` (`ComplexSourceLawDomain` only asks `τ_j < T`), so the cap at `T` is not needed. This file states the
uncapped variant.

* `b3ObsAll`: the observables of `b3Obs` (Gram entries of `b3ClosedGramAt` itself, entrance
  coordinates, `𝒦` entries) read at `limLenAll`.
* `condObsTestAll`: the test of finitely many of them under the closed law conditioned on the
  physical cap event (`0` if the event is null).
* `IsCapFddLimitAll`: conditioned fdd convergence at **every** model time `u` that is not a birth
  time (`s + u ≠ τ_j`); no `T` cap.
* **`ComplexCapFddAll`**: `ComplexCapFdd` with `IsCapFddLimitAll`. The candidate satisfies
  `IsCapLimitData` (probability, measurability, `G − J` and `𝒦 − J_𝒦` continuous for every `ω`).
* **`TargetCapFddAll`**: the hypotheses of `TargetCapFdd` give `ComplexCapFddAll`.
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

/-- The closed length at model time `u` (physical time `s + u`), not stopped at `T`. -/
def limLenAll (s : ℝ) (W : ℕ) (u : ℝ≥0) : ℕ := ⌊(W : ℝ) * (s + u)⌋₊

/-- **The finite-`W` observables at every time**, indexed as `complexObs`. -/
def b3ObsAll (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    LIdx K np → ℝ≥0 → ProbedPath W np × ℝ → ℂ
  | Sum.inl e => fun u y => gramEntry e (b3ClosedGramAt b E s h τ m W (limLenAll s W u) Vs y)
  | Sum.inr (Sum.inl k) => fun _ y => (physTseq b E s W y.1.1 k : ℂ)
  | Sum.inr (Sum.inr ij) => fun u y => b3ClosedKAt b E s h τ m W (limLenAll s W u) y ij.1 ij.2

/-- **The conditioned test at every time**: `E_W[ψ(obs_{i_l}(u_l)) | physical cap event]` (`0`
if the event is null). -/
def condObsTestAll (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {ι : Type} [Fintype ι]
    (i : ι → LIdx K np) (u : ι → ℝ≥0) (ψ : BoundedContinuousFunction (ι → ℂ) ℝ) : ℝ :=
  (∫ y, (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
      ψ (fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y) ∂closedLaw b W np) /
    (growthPathLaw W b (physCapEventC b E s h K W)).toReal

/-- **Conditioned fdd convergence at every non-birth time** along `φ` to the candidate
`(tseq, G, Kc)` on `(Ω', Q)`. -/
def IsCapFddLimitAll (b E s h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (φ : ℕ → ℕ)
    {Ω' : Type} [MeasurableSpace Ω'] (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (i : ι → LIdx K np) (u : ι → ℝ≥0), (∀ l j, s + (u l : ℝ) ≠ τ j) →
    ∀ ψ : BoundedContinuousFunction (ι → ℂ) ℝ,
      Tendsto (fun n => condObsTestAll b E s h τ m (φ n) (Vs (φ n)) i u ψ) atTop
        (𝓝 (∫ ω, ψ (fun l => complexObs tseq G Kc (i l) (u l) ω) ∂Q))

/-- **`ComplexCapFddAll`** (Prokhorov on the cap event at all times, and a continuous version):
for an admissible frame, a non-atomic cutoff and a cap of positive entrance mass, every `W_n → ∞`
has a subsequence along which the conditioned fdd converge at every non-birth time to a continuous
candidate. `targetCapFddAll_holds` derives it from `TransmissionLawContract`,
`ComplexClosedSummed`, `ComplexClosedTight`, `ComplexKStoppedMomentMax` and
`ComplexClosedLindeberg`. -/
def ComplexCapFddAll : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    CapCond.NoAtom (entranceLaw P μ s) h → entranceLaw P μ s (capSet K h) ≠ 0 →
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
        (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
        (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
        IsCapLimitData b E s τ m K Q tseq G Kc ∧
        IsCapFddLimitAll b E s h τ m K Vs (fun n => φ (ψ n)) Q tseq G Kc

/-- **Prokhorov on the cap event at all times** from the hypotheses of `TargetCapFdd`. -/
def TargetCapFddAll : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg → ComplexCapFddAll

end BlockBand.SourceProcess.PhysApprox.B3
