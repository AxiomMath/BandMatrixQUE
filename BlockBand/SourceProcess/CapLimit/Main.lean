module

public import BlockBand.SourceProcess.CapLimit.Compare
public import BlockBand.SourceProcess.BornUnique.Holds

/-!
# `CapRemoval` from `ModelUnique`

* `tendsto_capSet_compl`: `P(t_K > h²) = entrance (capSet K h)ᶜ → 0`. Read in any one model:
  every `tseq ω` is a.s. a transmission sequence, hence summable, so `t_k → 0` and only
  finitely many `t_k > h²` (`IsTransmissionSequence` gives this for every sequence; neither
  `EntranceAtomic` nor the fractional bound is needed once a model exists).
* `capRemoval_of (hB2 : ModelUnique) : CapRemoval`: `|Φ(K) − Φ(K')| ≤ P(t_K > h²)` for
  `K ≤ K'` (`abs_value_sub_le`), so `Φ` is Cauchy.
* `capRemoval_of_pins`: the same through `modelUnique_of_pins`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLimit

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

/-- **`P(t_K > h²) → 0`.** -/
theorem tendsto_capSet_compl {b E s T : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ} {h : ℝ} {K₀ M : ℕ}
    {entrance : Measure (Measure unitInterval)} {Ω : Type*} [MeasurableSpace Ω]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Q : Measure Ω}
    {tseq : Ω → ℕ → ℝ} {τ : Ω → Fin p × Fin M → ℝ}
    {G : ℝ≥0 → Ω → GramState (SrcCol K₀ (Fin p × Fin M))}
    (hM : IsFiniteSourceModel b E s T q h K₀ M entrance 𝓖 Q tseq τ G) (hh : 0 < h) :
    Tendsto (fun K : ℕ => (entrance (capSet K h)ᶜ).toReal) atTop (𝓝 0) := by
  have := hM.prob
  have ht : Measurable tseq := hM.entrance_measurable.mono (𝓖.le 0) le_rfl
  set C : ℕ → Set Ω := fun K => ⋃ k, ⋃ (_ : K ≤ k), {ω | h ^ 2 < tseq ω k} with hC
  have hCm : ∀ K, MeasurableSet (C K) := fun K => MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun _ =>
      measurableSet_lt measurable_const ((measurable_pi_apply k).comp ht)
  have hCa : Antitone C := fun K K' hKK ω hω => by
    simp only [hC, Set.mem_iUnion] at hω ⊢
    obtain ⟨k, hk, hω⟩ := hω
    exact ⟨k, hKK.trans hk, hω⟩
  have hnull : Q (⋂ K, C K) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hM.entrance_sequence)
    intro hseq
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((tendsto_order.1 hseq.2.2.tendsto_atTop_zero).2 _ (pow_pos hh 2))
    have hω' := Set.mem_iInter.1 hω N
    simp only [hC, Set.mem_iUnion, Set.mem_ofPred_eq] at hω'
    obtain ⟨k, hk, hlt⟩ := hω'
    exact lt_asymm hlt (hN k hk)
  have hlim : Tendsto (fun K => Q (C K)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (fun K => (hCm K).nullMeasurableSet) hCa
      ⟨0, measure_ne_top Q _⟩
    rwa [hnull] at this
  have hle : ∀ K, entrance (capSet K h)ᶜ ≤ Q (C K) := by
    intro K
    rw [← measure_entEvent hM (measurableSet_capSet K h).compl]
    refine measure_mono_ae (hM.entrance_sequence.mono fun ω hseq hω => ?_)
    have h1 : ¬ seqExtract (seqTraceMeasure (tseq ω)) K ≤ h ^ 2 := hω
    rw [seqExtract_seqTraceMeasure hseq] at h1
    exact Set.mem_iUnion.2 ⟨K, Set.mem_iUnion.2 ⟨le_rfl, not_le.1 h1⟩⟩
  have h0 : Tendsto (fun K => entrance (capSet K h)ᶜ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
  rw [ENNReal.toReal_zero] at this
  exact this

/-- **`CapRemoval` from `ModelUnique`.** -/
theorem capRemoval_of (hB2 : ModelUnique) : CapRemoval := by
  intro b hb0 hb E hE1 hE2 Ω _ P μ _ s T hs hsT p q hq J a ha h M hh hMp Φ hΦ
  obtain ⟨Ω₀, m₀, 𝓖₀, Q₀, t₀, τ₀, G₀, hM₀⟩ := (hΦ 0).1
  have hc : CauchySeq Φ := cauchySeq_of_le_tendsto_0' _ (fun n m hnm => by
      rw [Real.dist_eq]
      exact abs_value_sub_le hB2 hb0 hb hE1 hE2 hs hsT hq ha hh hMp hnm (hΦ n) (hΦ m))
    (tendsto_capSet_compl hM₀ hh)
  exact cauchySeq_tendsto_of_complete hc

/-- **`CapRemoval` from the Gram-level hypotheses `BornStoppedLaw` and `BornRestart`**
(through `modelUnique_of_pins`). -/
theorem capRemoval_of_pins (hSt : BornUnique.BornStoppedLaw) (hR : BornUnique.BornRestart) :
    CapRemoval :=
  capRemoval_of (BornUnique.modelUnique_of_pins hSt hR)

end BlockBand.SourceProcess.CapLimit
