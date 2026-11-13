module

public import BlockBand.SourceProcess.ClosedLimit.Model
public import BlockBand.SourceProcess.ClosedIdent.LimitPoints
public import BlockBand.SourceProcess.ModelExist.ModelData
public import BlockBand.SourceProcess.FullSourceStops.CoefficientMoments

/-!
# `ClosedLimitIdentification` from tested limit laws

* defines `IsTestedModel`: the data laws of `IsFiniteSourceModel`, `G − J` continuous for every
  `ω`, feasibility, and tested martingale increments of the **unstopped** compensated coordinates
  and of their compensated products, for the observables `modelObs` (Gram entries, entrance
  coordinates, birth locations);
* proves `IsTestedModel.isFiniteSourceModel` (with `isFiniteSourceModel_of_tested`): such a
  space, with its raw natural filtration, is a finite source model;
* states the hypothesis `ClosedLimitLaw`: `ClosedLimitIdentification` with
  `IsTestedModel` in place of `IsFiniteSourceModel`;
* proves `closedLimitIdentification_of_law : ClosedLimitLaw → ClosedLimitIdentification` and
  `closedIdentification_of_law hMT hGA hLp hP hL : ClosedIdentification`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedLimit

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.CapLimit BlockBand.SourceProcess.ClosedIdent
open scoped NNReal ENNReal

/-- The model birth jump process (as in `IsFiniteSourceModel.solution`). -/
def modelJ {Ω : Type*} (b s T : ℝ) {p : ℕ} (q : Fin p → ℝ → ℝ) (K M : ℕ)
    (τ : Ω → Fin p × Fin M → ℝ) (t : ℝ≥0) (ω : Ω) : GramState (SrcCol K (Fin p × Fin M)) :=
  birthJump (fun i => τ ω i - s) (fun i => dStar b * sourceMass s T (q i.1) / M) (t : ℝ)

/-- **A tested finite source model**: the data of `IsFiniteSourceModel` on a probability space
without filtration, with tested (unstopped) martingale increments for the observables
`modelObs tseq τ G` in place of the filtered stopped martingale problem. -/
structure IsTestedModel (b E s T : ℝ) {p : ℕ} (q : Fin p → ℝ → ℝ) (h : ℝ) (K M : ℕ)
    (entrance : Measure (Measure unitInterval)) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (τ : Ω → Fin p × Fin M → ℝ)
    (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))) : Prop where
  prob : IsProbabilityMeasure Q
  entrance_measurable : Measurable tseq
  births_measurable : Measurable τ
  gram_measurable : ∀ u, StronglyMeasurable (G u)
  entrance_sequence : ∀ᵐ ω ∂Q, IsTransmissionSequence (tseq ω)
  entrance_law : Q.map (fun ω => seqTraceMeasure (tseq ω)) = entrance
  births_law : Q.map τ = Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1)
  independent : IndepFun tseq τ Q
  initial : ∀ᵐ ω ∂Q, G 0 ω = initialGram K (Fin p × Fin M) (tseq ω) h
  continuous : ∀ ω, Continuous fun u => G u ω - modelJ b s T q K M τ u ω
  feasible : ∀ᵐ ω ∂Q, ∀ t, GramFeasible (srcSignature K (Fin p × Fin M)) (G t ω)
  drift : ∀ e, IsTestedMart Q (modelObs tseq τ G)
    (bornCompensated (transportD0 b E) (srcSignature K (Fin p × Fin M)) G
      (modelJ b s T q K M τ) e)
  bracket : ∀ e e', IsTestedMart Q (modelObs tseq τ G)
    (bornBracket (transportD0 b E) (srcSignature K (Fin p × Fin M)) G (modelJ b s T q K M τ) e e')

/-- **A tested model is a finite source model**, for the natural filtration of `modelObs`. -/
theorem IsTestedModel.isFiniteSourceModel {b E s T h : ℝ} {p K M : ℕ} {q : Fin p → ℝ → ℝ}
    {entrance : Measure (Measure unitInterval)} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {tseq : Ω → ℕ → ℝ} {τ : Ω → Fin p × Fin M → ℝ}
    {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))}
    (hT : IsTestedModel b E s T q h K M entrance Q tseq τ G) (hb : b < 1)
    (hq : ∀ i, IsSourceTest s T (q i)) :
    IsFiniteSourceModel b E s T q h K M entrance
      (pastFiltration (modelObs tseq τ G)
        (measurable_modelObs hT.entrance_measurable hT.births_measurable hT.gram_measurable))
      Q tseq τ G := by
  have := hT.prob
  exact isFiniteSourceModel_of_tested hT.entrance_measurable hT.births_measurable
    hT.gram_measurable (fun i => div_nonneg (mul_nonneg (FullSourceStops.dStar_pos hb).le
      (ModelExist.sourceMass_nonneg (hq i.1))) (Nat.cast_nonneg M))
    hT.entrance_sequence hT.entrance_law hT.births_law hT.independent hT.initial hT.continuous
    hT.feasible hT.drift hT.bracket

/-- **Limit points of the capped closed transform are tested-model values.** As
`ClosedIdent.ClosedLimitIdentification`, with the tested form `IsTestedModel` of the cap-`K`
finite source model: for each fixed `M`, frequently as `h ↓ 0` and frequently as `K → ∞`, along
every `W_n → ∞` on which the capped closed transform converges to `L`, some probability space
carries a tested cap-`K` model with entrance `μ(s)` whose transform restricted to `{t_K ≤ h²}`
equals `L`. This is what the weak limit of the closed physical finite-coordinate processes
provides: the scalar entrance and the deterministic birth data identify the physical
finite-coordinate martingales, with the drift and bracket identities as tested identities of
bounded continuous cylinder tests. This is stated as a hypothesis. -/
def ClosedLimitLaw : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ M : ℕ, 0 < M → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop,
      ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ L : ℝ,
        Tendsto (fun n => cappedClosedTransform b E s T h q a K M (φ n)) atTop (𝓝 L) →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
          (τ : Ω' → Fin p × Fin M → ℝ) (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin p × Fin M))),
          IsTestedModel b E s T q h K M (entranceLaw P μ s) Q tseq τ G ∧
          ∫ ω in entEvent tseq (capSet K h), sampledTransformValue a (G (T - s).toNNReal ω) ∂Q
            = L

/-- **`ClosedLimitIdentification` from `ClosedLimitLaw`.** -/
theorem closedLimitIdentification_of_law (hL : ClosedLimitLaw) : ClosedLimitIdentification := by
  intro b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM
  refine (hL b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM).mono
    fun h hK => hK.mono fun K hKL => ?_
  intro φ hφ L hφL
  obtain ⟨Ω', m', Q, tseq, τ, G, hT, hval⟩ := hKL φ hφ L hφL
  exact ⟨Ω', m', _, Q, tseq, τ, G, hT.isFiniteSourceModel (by linarith) hq, hval⟩

/-- **`ClosedIdentification` from the input hypotheses and `ClosedLimitLaw`.** -/
theorem closedIdentification_of_law (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hL : ClosedLimitLaw) : ClosedIdentification :=
  closedIdentification_of_limits hMT hGA hLp hP (closedLimitIdentification_of_law hL)

end BlockBand.SourceProcess.ClosedLimit
