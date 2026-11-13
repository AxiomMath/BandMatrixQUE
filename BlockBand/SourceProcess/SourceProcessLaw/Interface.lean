module

public import BlockBand.SourceProcess.SourceProcessLaw.Sampling

/-!
# The source process theorem: decomposition into named steps

| Step | content |
|---|---|
| `EntranceAtomic` | a.s. `μ(s) = Σ t_i δ_{t_i}` for a transmission sequence `t` |
| `SeqExtraction` | the sequence is a measurable function of its trace measure |
| `ModelExists` | the positive finite source model exists |
| `ModelUnique` | its Gram law is unique (births included) |
| `CapRemoval` | the model values converge as the count cap `K → ∞` |
| `CutoffRemoval` | then as the current cutoff `h ↓ 0` (rank-free coupling) |
| `PhysicalSampling` | positive source sampling for the physical path |
| `PhysicalApproximation` | closing and identification at fixed `M` |
| `EarlySources` | sources before `s` change the transform by `O(s)` |
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal Matrix

/-- **Atomicity of the entrance.** For a homogeneous transmission limit, at every positive time
`μ(s)` is a.s. the trace measure `Σ_i t_i δ_{t_i}` of a transmission sequence (`t` antitone in
`[0,1]`, summable). Proof idea: finite-`W` measures have this form, the count above `x > 0` is tight
by `fractional`, the closure adds only `cδ₀`, and `noMassAtZero` removes it. -/
def EntranceAtomic : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s : ℝ, 0 < s → ∀ᵐ ω ∂P, ∃ t : ℕ → ℝ, IsTransmissionSequence t ∧
      (μ s ω : Measure unitInterval) = seqTraceMeasure t

/-- **Measurable extraction of the sequence** (pure measure theory): a Giry-measurable map that
recovers every transmission sequence from its trace measure. -/
def SeqExtraction : Prop :=
  ∃ ext : Measure unitInterval → ℕ → ℝ, Measurable ext ∧
    ∀ t : ℕ → ℝ, IsTransmissionSequence t → ext (seqTraceMeasure t) = t

/-- **Existence of the positive finite source model** (initial frame, retained modes, existence of
the finite Gram law, near probe births, births perpendicular in unused near dimensions): for every
entrance that is the law of the trace measure of a random transmission sequence, the model
exists. -/
def ModelExists : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ ρ : Measure (ℕ → ℝ), IsProbabilityMeasure ρ → (∀ᵐ t ∂ρ, IsTransmissionSequence t) →
    ∀ (h : ℝ) (K M : ℕ), 0 < h → 0 < M →
      ∃ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
        (tseq : Ω → ℕ → ℝ) (τ : Ω → Fin p × Fin M → ℝ)
        (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))),
        IsFiniteSourceModel b E s T q h K M (ρ.map seqTraceMeasure) 𝓖 Q tseq τ G

/-- **Uniqueness of the born Gram law** (uniqueness of the finite Gram law, with `𝓖₀`-random
births): two finite source models with the same parameters and entrance have the same Gram law at
every time. -/
def ModelUnique : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (entrance : Measure (Measure unitInterval)) (h : ℝ) (K M : ℕ), 0 < h → 0 < M →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
      (tseq : Ω → ℕ → ℝ) (τ : Ω → Fin p × Fin M → ℝ)
      (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))),
      IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G →
    ∀ (Ω' : Type) (m' : MeasurableSpace Ω') (𝓖' : Filtration ℝ≥0 m') (Q' : Measure Ω')
      (tseq' : Ω' → ℕ → ℝ) (τ' : Ω' → Fin p × Fin M → ℝ)
      (G' : ℝ≥0 → Ω' → GramState (SrcCol K (Fin p × Fin M))),
      IsFiniteSourceModel b E s T q h K M entrance 𝓖' Q' tseq' τ' G' →
    ∀ t : ℝ≥0, Q.map (G t) = Q'.map (G' t)

/-- **Removal of the current-count cap** (by the homogeneous fractional trace bound): at fixed
cutoff `h` and sample size `M`, the model values converge as `K → ∞` (a.s. only finitely many
`t_i > h²`). -/
def CapRemoval : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ (h : ℝ) (M : ℕ), 0 < h → 0 < M → ∀ Φ : ℕ → ℝ,
      (∀ K, FiniteSourceModelValue b E s T q h K M (entranceLaw P μ s) a (Φ K)) →
      ∃ Λ : ℝ, Tendsto Φ atTop (𝓝 Λ)

/-- **Removal of the current cutoff** (the rank-independent coupling removes `h` in the finite
positive models at each fixed `M`): the cap-free values `Λ(h)` converge as `h ↓ 0`. -/
def CutoffRemoval : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ M : ℕ, 0 < M → ∀ (Φ : ℕ → ℝ → ℝ) (Λ : ℝ → ℝ),
      (∀ K h, 0 < h → FiniteSourceModelValue b E s T q h K M (entranceLaw P μ s) a (Φ K h)) →
      (∀ h, 0 < h → Tendsto (fun K => Φ K h) atTop (𝓝 (Λ h))) →
      ∃ Λ' : ℝ, Tendsto Λ (𝓝[>] 0) (𝓝 Λ')

/-- **Positive source sampling for the physical path**: the sampled
transform with `M` tag locations differs from the source transform by `C_{τ,q,a}/M`, for all
large `W`. -/
def PhysicalSampling : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
      ∃ C : ℝ, ∀ M : ℕ, 0 < M → ∀ᶠ W in atTop,
        |sourceTransform b E T q a W - sampledPhysTransform b E T q a M W| ≤ C / M

/-- **Closing and identification at fixed sample size** (physical current carrier, small channel
leakage, Gaussian closing error, closing at time `s`; at fixed `h, M` and cap `K` the physical
finite-coordinate martingales are identified with the finite Gram law, and the physical closing
error vanishes as `h ↓ 0`): for small cutoff and large cap, the physical sampled transforms are
eventually within `ε` of the finite-model value. -/
def PhysicalApproximation : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ M : ℕ, 0 < M → ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ v : ℝ,
        FiniteSourceModelValue b E s T q h K M (entranceLaw P μ s) a v →
        ∀ᶠ W in atTop, |sampledPhysTransform b E T q a M W - v| ≤ ε

/-- **Sources before `s`** (they have expected positive trace `O(s)` by the full tag clock moments,
so restoring them changes a bounded positive transform by `O(s)`): for tests on `[0,T]`,
truncating them to `[s,T]` changes the transform by at most `Cs` for all large `W`. -/
def EarlySources : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ T : ℝ, 0 < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest 0 T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
      ∃ C : ℝ, ∀ s : ℝ, 0 < s → s < T → ∀ᶠ W in atTop,
        |sourceTransform b E T q a W -
          sourceTransform b E T (fun i => Set.indicator (Set.Icc s T) (q i)) a W| ≤ C * s

end BlockBand.SourceProcess.SourceProcessLaw
