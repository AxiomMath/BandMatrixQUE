module

public import BlockBand.SourceProcess.CapCond.Bound
public import BlockBand.SourceProcess.ClosedReduce.Defs

/-!
# The conditioned closed limit on the cap event

`ClosedReduce.CapCondLimit` combines three things: the frequent quantifiers in `h, K`, the cap mass
`P(μ(s) ∈ capSet K h)`, and the identification of the closed process on the cap event. The first
two are proved separately (`capCondLimit_of_capCondLaw`). What is left is `CapCondLaw`: the
identification of the limit of the closed transform **conditioned** on the physical cap event,
`condTransform = cappedClosedTransform / P_W(physCapEvent)`, with the value of the cap-`K` model
whose entrance is `μ(s)` conditioned on `capSet K h`.

`CapCondLaw` is not a new hypothesis on the physics: it is the conditional form of the limit
passage that identifies the physical finite-coordinate martingales with the unique finite Gram
law, and is what a Prokhorov and martingale-problem argument has to prove from
`ClosedSummed`, `ClosedTight` and `ClosedLindeberg`. It is stated
* only for `0 < h < 1` such that no `t_k(μ(s))` has an atom at `h²` (`NoAtom`),
* frequently in `K`, and only when `P(μ(s) ∈ capSet K h) ≠ 0`,
* for the stopped, filtered `IsFiniteSourceModel` (no tested, unstopped identities).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedIdent
open scoped NNReal ENNReal

/-- The closed transform conditioned on the physical cap event (`0` if the event is null). -/
def condTransform (b E s T h : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ) (a : Fin J → Fin p → ℝ)
    (K M W : ℕ) : ℝ :=
  cappedClosedTransform b E s T h q a K M W / (growthPathLaw W b (physCapEvent b E s h K W)).toReal

/-- **The conditioned closed limit** on the cap event `{t_K ≤ h²}`. For non-atomic `h`,
frequently in `K`, if the cap event has positive entrance probability, every limit point `ℓ` of
the conditioned closed transform along `W_n → ∞` is the value at `T − s` of some filtered cap-`K`
finite source model with entrance `μ(s)` conditioned on `capSet K h`. -/
def CapCondLaw : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ M : ℕ, 0 < M → ∀ h : ℝ, 0 < h → h < 1 → NoAtom (entranceLaw P μ s) h →
    ∃ᶠ K in atTop, entranceLaw P μ s (capSet K h) ≠ 0 →
      ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ ℓ : ℝ,
        Tendsto (fun n => condTransform b E s T h q a K M (φ n)) atTop (𝓝 ℓ) →
          ∃ (Ω' : Type) (m : MeasurableSpace Ω') (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω')
            (tseq : Ω' → ℕ → ℝ) (τ : Ω' → Fin p × Fin M → ℝ)
            (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin p × Fin M))),
            IsFiniteSourceModel b E s T q h K M ((entranceLaw P μ s)[|capSet K h]) 𝓖 Q tseq τ G ∧
            ∫ ω, sampledTransformValue a (G (T - s).toNNReal ω) ∂Q = ℓ

end BlockBand.SourceProcess.CapCond
