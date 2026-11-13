module

public import BlockBand.SourceProcess.PhysApprox.B3LimSubseq

/-!
# Observables of the conditioned closed process and its limit points

* `condObsTest`: the expectation of a bounded continuous test of finitely many observables under
  the closed law **conditioned** on the physical cap event.
* `IsCapFddLimit`: the conditioned finite-dimensional laws converge along a subsequence to those
  of `(tseq, G, Kc)` on `(Ω', Q)`, at every model time `u` with `s + u ≤ max(s, T)` that is not a
  birth time (`s + u ≠ τ_j`; at a birth step the finite-`W` coordinate is still unborn, the limit
  is right-continuous). The `max` only matters in the degenerate case `np = 0`, `T ≤ s`.
* `IsCapLimitData`: probability, measurability and continuity (`G − J`, `𝒦 − J_𝒦` continuous for
  every `ω`) of the candidate.
* **`ComplexCapIdent`**, stated as a hypothesis: every such candidate has the law at `T − s` of a
  stopped tested complex model with entrance `μ(s)[|capSet K h]`. Its ingredients: the entrance
  (`tendsto_capWeighted`, `countExt_smCount`); the initial state; feasibility
  (`ComplexClosedFeasible` and closedness of the feasible set); the stopped tested
  identities on `[0, T − s]` (`ComplexClosedSummed`, `ComplexClosedLindeberg`,
  `ComplexKStoppedMomentMax`, levels at which the stop is a.s. continuous); the horizon (glue an
  unborn continuation after `T − s`, all births being earlier).
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

/-- The index set of `complexObs`: Gram entries, entrance coordinates, `𝒦` entries. -/
abbrev LIdx (K np : ℕ) := (Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) ⊕ ℕ ⊕ (Fin np × Fin np)

/-- The closed length at model time `u` (physical time `s + u`), stopped at `⌊W max(s,T)⌋`
(`= ⌊WT⌋` when `s < T`).
-/
def limLen (s T : ℝ) (W : ℕ) (u : ℝ≥0) : ℕ := min ⌊(W : ℝ) * (s + u)⌋₊ ⌊(W : ℝ) * max s T⌋₊

/-- **The finite-`W` observables** of the closed process, indexed as `complexObs`. -/
def b3Obs (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    LIdx K np → ℝ≥0 → ProbedPath W np × ℝ → ℂ
  | Sum.inl e => fun u y => gramEntry e (b3ClosedGramAt b E s h τ m W (limLen s T W u) Vs y)
  | Sum.inr (Sum.inl k) => fun _ y => (physTseq b E s W y.1.1 k : ℂ)
  | Sum.inr (Sum.inr ij) => fun u y => b3ClosedKAt b E s h τ m W (limLen s T W u) y ij.1 ij.2

/-- **The conditioned test**: `E_W[ψ(obs_{i_l}(u_l)) | physical cap event]` (`0` if the event is
null). -/
def condObsTest (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {ι : Type} [Fintype ι]
    (i : ι → LIdx K np) (u : ι → ℝ≥0) (ψ : BoundedContinuousFunction (ι → ℂ) ℝ) : ℝ :=
  (∫ y, (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
      ψ (fun l => b3Obs b E s T h τ m W Vs (i l) (u l) y) ∂closedLaw b W np) /
    (growthPathLaw W b (physCapEventC b E s h K W)).toReal

/-- **Conditioned fdd convergence** along `φ` to the candidate `(tseq, G, Kc)` on `(Ω', Q)`, at
model times `u` with `s + u ≤ max(s, T)` off the births. -/
def IsCapFddLimit (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (φ : ℕ → ℕ)
    {Ω' : Type} [MeasurableSpace Ω'] (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (i : ι → LIdx K np) (u : ι → ℝ≥0), (∀ l, s + (u l : ℝ) ≤ max s T) →
    (∀ l j, s + (u l : ℝ) ≠ τ j) → ∀ ψ : BoundedContinuousFunction (ι → ℂ) ℝ,
      Tendsto (fun n => condObsTest b E s T h τ m (φ n) (Vs (φ n)) i u ψ) atTop
        (𝓝 (∫ ω, ψ (fun l => complexObs tseq G Kc (i l) (u l) ω) ∂Q))

/-- The regularity of a limit candidate: probability, measurability, and continuity of `G − J`
and `𝒦 − J_𝒦` for every `ω` (a continuous version). -/
def IsCapLimitData (b E s : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (K : ℕ) {Ω' : Type}
    [MeasurableSpace Ω'] (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ) : Prop :=
  IsProbabilityMeasure Q ∧ Measurable tseq ∧ (∀ u, StronglyMeasurable (G u)) ∧
    (∀ u, StronglyMeasurable (Kc u)) ∧ (∀ ω, Continuous fun u => G u ω - gramJ b s τ m u) ∧
    ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u

/-- **`ComplexCapFdd`** (Prokhorov on the cap event, and a continuous version): for an admissible
frame, a non-atomic cutoff and a cap of positive entrance mass, every `W_n → ∞` has a subsequence
along which the conditioned fdd converge to a continuous candidate. -/
def ComplexCapFdd : Prop :=
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
        IsCapFddLimit b E s T h τ m K Vs (fun n => φ (ψ n)) Q tseq G Kc

/-- **`ComplexCapIdent`** (identification of the limit points): every continuous candidate that
is a conditioned fdd limit has, at model time `T − s`, the law of a stopped tested complex model
with entrance `μ(s)[|capSet K h]`. -/
def ComplexCapIdent : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    CapCond.NoAtom (entranceLaw P μ s) h → entranceLaw P μ s (capSet K h) ≠ 0 →
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
    ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
      (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
      (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
      IsCapLimitData b E s τ m K Q tseq G Kc → IsCapFddLimit b E s T h τ m K Vs φ Q tseq G Kc →
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (Q'' : Measure Ω'') (tseq'' : Ω'' → ℕ → ℝ)
        (G'' : ℝ≥0 → Ω'' → GramState (SrcCol K (Fin np)))
        (Kc'' : ℝ≥0 → Ω'' → Matrix (Fin np) (Fin np) ℂ),
        IsStoppedTestedComplexModel b E s τ m h K ((entranceLaw P μ s)[|capSet K h]) Q''
          tseq'' G'' Kc'' ∧
        ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
          modelExpectation K s T Q'' G'' Kc'' Φ = modelExpectation K s T Q G Kc Φ

end BlockBand.SourceProcess.PhysApprox.B3
