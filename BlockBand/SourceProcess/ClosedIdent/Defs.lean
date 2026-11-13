module

public import BlockBand.SourceProcess.ClosingAux.Integrand
public import BlockBand.SourceProcess.CapLimit.Main
public import BlockBand.SourceProcess.Closing.Split

/-!
# The capped closed identification

The closed identification `Closing.ClosedIdentification`, together with the cap removal, has two
parts in the proof of the source process theorem:

* At fixed `h, M` and a finite cap on the number of retained modes, close the omitted channels and
  identify the physical finite-coordinate martingales with the unique finite Gram law: on the
  event that at most `K` modes are retained, the closed physical process is identified with the
  cap-`K` model. This is `CappedClosedIdentification`.
* Remove the current-count cap by the homogeneous fractional trace bound: proved in
  `closedIdentification_of_capped` (physical side from the fractional trace bound of
  `TransmissionLawContract`, model side from `tendsto_capSet_compl`).

The physical cap event `physCapEvent` is `{μ_W(s) ∈ capSet K h}`: the `(K+1)`-st largest
transmission eigenvalue of `T_{⌊Ws⌋}` (trace measure `μ_W(s) = transmissionProcess`) is `≤ h²`,
i.e. at most `K` modes `t_i > h²` are retained. The model event is
`entEvent tseq (capSet K h) = {t_K ≤ h²}`, the same set of trace measures.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedIdent

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.CapLimit
open scoped NNReal

/-- **The physical cap event at time `s`**: at most `K` transmission eigenvalues of
`T_{⌊Ws⌋}` exceed `h²` (`μ_W(s) ∈ capSet K h`). -/
def physCapEvent (b E s h : ℝ) (K W : ℕ) : Set (GrowthPath W) :=
  {ω | ((transmissionProcess b E (fun _ => 0) W s ω : FiniteMeasure unitInterval) :
    Measure unitInterval) ∈ capSet K h}

/-- **The capped closed sampled transform**: `closedSampledTransform` with its integrand
(`closedIntegrand`, by `rfl`) restricted to the physical cap event. -/
def cappedClosedTransform (b E s T h : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) (K M W : ℕ) : ℝ :=
  ∫ y, (physCapEvent b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
      closedIntegrand b E s T h q a M W y
    ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw)

/-- **Identification at a fixed cap.** For each fixed `M` and
`ε > 0`, frequently as `h ↓ 0` and frequently as `K → ∞`, for every cap-`K` finite model with
entrance `μ(s)`: eventually in `W`, the closed sampled transform restricted to the physical event
"at most `K` retained modes" is within `ε` of the model transform restricted to the model event
`{t_K ≤ h²}`.

On these events the cap is not active (all modes `t_i > h²` are retained), so this is the
identification, at fixed `h, M` and a finite cap, of the closed physical finite-coordinate
martingales with the unique finite Gram law. The frequent `h` avoids the countably many entrance
atoms at `h²`; the frequent `K` is weaker than "every `K`". This is stated as a hypothesis. -/
def CappedClosedIdentification : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ M : ℕ, 0 < M → ∀ ε : ℝ, 0 < ε → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop,
      ∀ (Ω' : Type) (m : MeasurableSpace Ω') (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω')
        (tseq : Ω' → ℕ → ℝ) (τ : Ω' → Fin p × Fin M → ℝ)
        (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin p × Fin M))),
        IsFiniteSourceModel b E s T q h K M (entranceLaw P μ s) 𝓖 Q tseq τ G →
        ∀ᶠ W in atTop, |cappedClosedTransform b E s T h q a K M W -
          ∫ ω in entEvent tseq (capSet K h), sampledTransformValue a (G (T - s).toNNReal ω) ∂Q|
            ≤ ε

end BlockBand.SourceProcess.ClosedIdent
