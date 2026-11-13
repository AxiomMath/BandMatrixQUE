module

public import BlockBand.SourceProcess.ClosedLimit.Reduction

/-!
# Two smaller statements behind `ClosedLimitLaw`

`ClosedLimitLaw` asks, for each limit point `L` of the capped closed transform, for a
*tested* cap-`K` model (unstopped tested martingale identities, `G − J` continuous for every `ω`)
with the **full** entrance `μ(s)` and capped value `L`. It mixes two different contents:

* **model content**: unstopped tested identities and a model off the cap event `{t_K ≤ h²}`, where
  the physical hypotheses (`ClosedSummed`, `ClosedTight`) say nothing;
* **physical content**: the weak limit of the closed coordinates on the cap event.

This file states each as a separate hypothesis.

* `TestedOfFinite` (model content): every finite source model has a tested model
  with the same parameters and entrance. This holds if the finite source SDE has a unique,
  nonexplosive solution (as in the finite Gram law proposition): its `V`-equation is
  linear with bounded coefficients (`P, P'` projections), so all moments are finite, and under
  the two-projection constraint the Gram drift and covariance coefficients
  grow linearly (`g = ½Tr(𝖣M𝖣M) ≤ ½ rank`, `M𝖣M ⪯ M`); the unstopped compensated coordinates
  and their compensated products are then true martingales.
* `CapCondLimit` (physical content restricted to the cap event): every limit
  point is `μ(s)(capSet) ·` the value of some (filtered, trace-stopped) model whose entrance is
  `μ(s)` conditioned on `capSet K h`; when `μ(s)(capSet) = 0` the limit point is `0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedReduce

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedIdent BlockBand.SourceProcess.ClosedLimit
open scoped NNReal ENNReal

/-- **Finite source models are tested models** (model content). Every cap-`K` finite source
model has a tested model (`IsTestedModel`: unstopped tested identities, `G − J` continuous for
every `ω`) with the same parameters and entrance. This is stated as a hypothesis. -/
def TestedOfFinite : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (entrance : Measure (Measure unitInterval)) (h : ℝ) (K M : ℕ), 0 < h → 0 < M →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
      (tseq : Ω → ℕ → ℝ) (τ : Ω → Fin p × Fin M → ℝ)
      (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))),
      IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q' : Measure Ω') (tseq' : Ω' → ℕ → ℝ)
      (τ' : Ω' → Fin p × Fin M → ℝ) (G' : ℝ≥0 → Ω' → GramState (SrcCol K (Fin p × Fin M))),
      IsTestedModel b E s T q h K M entrance Q' tseq' τ' G'

/-- **The closed limit on the cap event** (physical content), on the event `{t_K ≤ h²}` where
the cap is inactive. For each fixed `M`, frequently as `h ↓ 0`
and frequently as `K → ∞`, along every `W_n → ∞` on which the capped closed transform converges
to `L`: if `μ(s)(capSet K h) = 0` then `L = 0`; otherwise some filtered cap-`K` finite source
model with entrance `μ(s)` conditioned on `capSet K h` has value `L / μ(s)(capSet K h)` at
`T − s`. Only the stopped (trace-level) martingale problem of `IsFiniteSourceModel` is asked,
and nothing off the cap event. This is stated as a hypothesis. -/
def CapCondLimit : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ M : ℕ, 0 < M → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop,
      ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ L : ℝ,
        Tendsto (fun n => cappedClosedTransform b E s T h q a K M (φ n)) atTop (𝓝 L) →
        (entranceLaw P μ s (capSet K h) = 0 → L = 0) ∧
        (entranceLaw P μ s (capSet K h) ≠ 0 →
          ∃ (Ω' : Type) (m : MeasurableSpace Ω') (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω')
            (tseq : Ω' → ℕ → ℝ) (τ : Ω' → Fin p × Fin M → ℝ)
            (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin p × Fin M))),
            IsFiniteSourceModel b E s T q h K M ((entranceLaw P μ s)[|capSet K h]) 𝓖 Q tseq τ G ∧
            (entranceLaw P μ s (capSet K h)).toReal *
              ∫ ω, sampledTransformValue a (G (T - s).toNNReal ω) ∂Q = L)

end BlockBand.SourceProcess.ClosedReduce
