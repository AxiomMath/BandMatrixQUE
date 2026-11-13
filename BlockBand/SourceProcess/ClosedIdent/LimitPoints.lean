module

public import BlockBand.SourceProcess.ClosedIdent.Main
public import BlockBand.SourceProcess.BornUnique.Holds
public import BlockBand.SourceProcess.BornStopped.Main
public import BlockBand.SourceProcess.HorizonExt.Holds
public import BlockBand.SourceProcess.BornRestart.Holds

/-!
# `CappedClosedIdentification` from the identification of limit points

The closed physical finite-coordinate martingales are identified with the **unique** finite Gram
law. This file separates the two halves:

* the existence half, stated as the hypothesis `ClosedLimitIdentification`: every limit point,
  along any `W_n → ∞`, of the capped closed transform is the restricted transform of *some* cap-`K`
  finite model with entrance `μ(s)` (the limit points solve the finite Gram martingale problem);
* the uniqueness half, proved: by `ModelUnique` (proved with no hypothesis:
  `BornUnique.modelUnique_of_pins`, `BornStopped.bornStoppedLaw_of_extension`,
  `HorizonExt.gramHorizonExtension_holds`, `BornRestart.bornRestart_holds`) and
  `setIntegral_capSet_eq`, the restricted value `c` is the same in every model. The capped
  transforms lie in `[0,1]`, so every subsequence has a convergent further subsequence, whose
  limit is `c`; hence the whole sequence converges to `c` (`tendsto_of_subseq_tendsto`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedIdent

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-- **Limit points of the capped closed transform are model values**: the existence half of the
identification of the physical finite-coordinate martingales with the unique finite Gram law.
For each fixed `M`, frequently as `h ↓ 0` and frequently as `K → ∞`: along every `W_n → ∞` on
which the capped closed transform converges to `L`, there is a cap-`K` finite model with entrance
`μ(s)` whose transform restricted to `{t_K ≤ h²}` equals `L`. This is stated as a hypothesis. -/
def ClosedLimitIdentification : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ M : ℕ, 0 < M → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop,
      ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ L : ℝ,
        Tendsto (fun n => cappedClosedTransform b E s T h q a K M (φ n)) atTop (𝓝 L) →
        ∃ (Ω' : Type) (m : MeasurableSpace Ω') (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω')
          (tseq : Ω' → ℕ → ℝ) (τ : Ω' → Fin p × Fin M → ℝ)
          (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin p × Fin M))),
          IsFiniteSourceModel b E s T q h K M (entranceLaw P μ s) 𝓖 Q tseq τ G ∧
          ∫ ω in entEvent tseq (capSet K h), sampledTransformValue a (G (T - s).toNNReal ω) ∂Q
            = L

/-- `ModelUnique`, with no hypothesis. -/
theorem modelUnique_holds : ModelUnique :=
  BornUnique.modelUnique_of_pins
    (BornStopped.bornStoppedLaw_of_extension HorizonExt.gramHorizonExtension_holds)
    BornRestart.bornRestart_holds

/-- The capped closed transform lies in `[0,1]`. -/
theorem cappedClosedTransform_mem {b E s T h : ℝ} {p J : ℕ} {q : Fin p → ℝ → ℝ}
    {a : Fin J → Fin p → ℝ} {K M W : ℕ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hq : ∀ i x, 0 ≤ q i x) (ha : ∀ j i, 0 ≤ a j i) :
    cappedClosedTransform b E s T h q a K M W ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := closed_sub_capped_mem (s := s) (h := h) (K := K) (T := T) (W := W) (M := M)
    hb hE1 hE2 hq ha
  have h2 := closedSampledTransform_mem b E s T h hq ha M W
  refine ⟨integral_nonneg fun y => ?_, by linarith [h1.1, h2.2]⟩
  have hf := closedIntegrand_mem b E s T h hq ha M W y
  by_cases hy : y.1.1 ∈ physCapEvent b E s h K W
  · rw [Set.indicator_of_mem hy, one_mul]; exact hf.1
  · rw [Set.indicator_of_notMem hy, zero_mul]; exact le_rfl

/-- **`CappedClosedIdentification` from `ClosedLimitIdentification`**, the uniqueness half being
proved. -/
theorem cappedClosedIdentification_of_limits (hL : ClosedLimitIdentification) :
    CappedClosedIdentification := by
  intro b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM ε hε
  have hb1 : b < 1 := by linarith
  have hq0 : ∀ i x, 0 ≤ q i x := fun i => (hq i).1
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  refine ((hL b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM).and_eventually
    hpos).mono fun h ⟨hK, hh⟩ => hK.mono fun K hKL => ?_
  intro Ω' m' 𝓖 Q tseq τ G hMod
  set c := ∫ ω in entEvent tseq (capSet K h), sampledTransformValue a (G (T - s).toNNReal ω) ∂Q
  set x : ℕ → ℝ := fun W => cappedClosedTransform b E s T h q a K M W
  have hx : Tendsto x atTop (𝓝 c) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨L, -, φ, hφ, hφL⟩ := tendsto_subseq_of_bounded (x := fun n => x (ns n))
      (Metric.isBounded_Icc (0 : ℝ) 1) fun n => cappedClosedTransform_mem hb1 hE1 hE2 hq0 ha
    obtain ⟨Ω₁, m₁, 𝓖₁, Q₁, tseq₁, τ₁, G₁, hM₁, hval⟩ :=
      hKL (fun n => ns (φ n)) (hns.comp hφ.tendsto_atTop) L hφL
    have heq := setIntegral_capSet_eq (a := a) modelUnique_holds hb0 hb hE1 hE2 hs hsT hq hh hM
      le_rfl hMod hM₁ (T - s).toNNReal
    refine ⟨φ, ?_⟩
    have : c = L := heq.trans hval
    rw [this]
    exact hφL
  filter_upwards [(tendsto_order.1 hx).1 _ (show c - ε < c by linarith),
    (tendsto_order.1 hx).2 _ (show c < c + ε by linarith)] with W h1 h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **`ClosedIdentification` from the input hypotheses and `ClosedLimitIdentification`.** -/
theorem closedIdentification_of_limits (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hL : ClosedLimitIdentification) : ClosedIdentification :=
  closedIdentification_of_pins hMT hGA hLp hP (cappedClosedIdentification_of_limits hL)

end BlockBand.SourceProcess.ClosedIdent
