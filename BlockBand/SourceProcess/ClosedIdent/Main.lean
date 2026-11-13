module

public import BlockBand.SourceProcess.ClosedIdent.PhysTail
public import BlockBand.SourceProcess.ClosedIdent.Restrict
public import BlockBand.Transmission.LawForced.LawHolds

/-!
# `ClosedIdentification` from the capped identification

The target is `Closing.ClosedIdentification`, with the cap removal. Its two steps:

* identification at a fixed cap: the hypothesis `CappedClosedIdentification`;
* cap removal by the homogeneous fractional trace bound: proved. With `ε/3` each,
  `|closed − v| ≤ (closed − capped) + |capped − ∫_A F| + (v − ∫_A F)`, where
  `closed − capped ≤ P_W(more than K modes t_i > h² at s)` (`closed_sub_capped_mem`, small for
  large `K` uniformly in large `W` by `eventually_physCapEvent_compl_le` and the fractional trace
  bound), and `v − ∫_A F ≤ P(t_K > h²)` (`model_sub_restrict_mem`, small by
  `tendsto_capSet_compl`).

`closedIdentification_of_pins` replaces `TransmissionLawContract` by the matched-traces and
Gaussian inputs it is proved from.
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
open BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-- **`ClosedIdentification` from `CappedClosedIdentification`** and the fractional trace bound. -/
theorem closedIdentification_of_capped (hTL : TransmissionLawContract)
    (hC : CappedClosedIdentification) : ClosedIdentification := by
  intro b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM ε hε
  have hε3 : 0 < ε / 3 := by linarith
  have hb1 : b < 1 := by linarith
  have hq0 : ∀ i x, 0 ≤ q i x := fun i => (hq i).1
  have hfreq := hC b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM (ε / 3) hε3
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  refine (hfreq.and_eventually hpos).mono fun h ⟨hK, hh⟩ => ?_
  by_cases hex : ∃ (K₀ : ℕ) (Ω' : Type) (m' : MeasurableSpace Ω') (𝓖 : Filtration ℝ≥0 m')
      (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ) (τ : Ω' → Fin p × Fin M → ℝ)
      (G : ℝ≥0 → Ω' → GramState (SrcCol K₀ (Fin p × Fin M))),
      IsFiniteSourceModel b E s T q h K₀ M (entranceLaw P μ s) 𝓖 Q tseq τ G
  swap
  · refine Frequently.of_forall fun K v hv => ?_
    obtain ⟨Ω', m', 𝓖, Q, tseq, τ, G, hMod⟩ := hv.1
    exact absurd ⟨K, Ω', m', 𝓖, Q, tseq, τ, G, hMod⟩ hex
  obtain ⟨K₀, Ω₀, m₀, 𝓖₀, Q₀, tseq₀, τ₀, G₀, hM₀⟩ := hex
  have hmt : ∀ᶠ K : ℕ in atTop, (entranceLaw P μ s (capSet K h)ᶜ).toReal ≤ ε / 3 :=
    (tendsto_order.1 (tendsto_capSet_compl hM₀ hh)).2 _ (by linarith) |>.mono fun _ h => h.le
  have hpt := eventually_physCapEvent_compl_le hTL hb0 hb hE1 hE2 hs hh hε3
  refine ((hK.and_eventually hmt).and_eventually hpt).mono ?_
  rintro K ⟨⟨hKp, hKm⟩, hKph⟩ v hv
  obtain ⟨Ω', m', 𝓖, Q, tseq, τ, G, hMod⟩ := hv.1
  have e := hv.2 Ω' m' 𝓖 Q tseq τ G hMod
  have hmod := model_sub_restrict_mem (a := a) hMod ha (T - s).toNNReal
  rw [e] at hmod
  filter_upwards [hKp Ω' m' 𝓖 Q tseq τ G hMod, hKph] with W h1 h2
  have hphys := closed_sub_capped_mem (s := s) (h := h) (K := K) (T := T) (W := W) (M := M)
    hb1 hE1 hE2 hq0 ha
  rw [abs_sub_le_iff] at h1 ⊢
  constructor <;> linarith [hphys.1, hphys.2, hmod.1, hmod.2, h1.1, h1.2]

/-- **`ClosedIdentification` from the input hypotheses and `CappedClosedIdentification`.** -/
theorem closedIdentification_of_pins (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hC : CappedClosedIdentification) : ClosedIdentification :=
  closedIdentification_of_capped
    (Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP) hC

end BlockBand.SourceProcess.ClosedIdent
