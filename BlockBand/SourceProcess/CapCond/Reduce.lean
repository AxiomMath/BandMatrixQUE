module

public import BlockBand.SourceProcess.CapCond.Defs
public import BlockBand.SourceProcess.SourceProcessMain.Holds7

/-!
# The conditioned closed limit and the source process theorem from `CapCondLaw`

* **Zero case** (`limit_eq_zero`): if `P(μ(s) ∈ capSet K h) = 0`, every limit point of the capped
  transform is `0`, for every `h` and `K`: `0 ≤ capped ≤ P_W(cap)` (`capped_mem`) and
  `limsup P_W(cap) ≤ P(μ(s) ∈ capSet K h)` (`eventually_capProb_le`).
* **Cap mass** (`tendsto_condTransform`): for non-atomic `h`, `P_W(cap) → P(μ(s) ∈ capSet K h)`
  (`tendsto_capProb`), so `capped → L` gives `condTransform → L / P(μ(s) ∈ capSet K h)`.
* **Frequent `h`** (`frequently_of_noAtom`): the non-atomic `h` are frequent.

Besides `CapCondLaw`, `capCondLimit_of_capCondLaw` uses only `TransmissionLawContract` (through
`entranceAtomic_of`). `sourceProcessContract_of_capCondLaw` then gives `SourceProcessContract`
(the source process theorem) from `CapCondLaw` and the Gaussian and transmission inputs.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedIdent
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {b E : ℝ}

/-- **Zero case.** -/
theorem limit_eq_zero (hTL : TransmissionLawContract) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s T : ℝ}
    (hs : 0 < s) {p J : ℕ} {q : Fin p → ℝ → ℝ} (hq : ∀ i, IsSourceTest s T (q i))
    {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (h : ℝ) (K M : ℕ) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) {L : ℝ}
    (hL : Tendsto (fun n => cappedClosedTransform b E s T h q a K M (φ n)) atTop (𝓝 L))
    (h0 : entranceLaw P μ s (capSet K h) = 0) : L = 0 := by
  have hq' : ∀ i x, 0 ≤ q i x := fun i => (hq i).1
  have hb1 : b < 1 := by linarith
  have hL0 : 0 ≤ L := ge_of_tendsto' hL fun n => (capped_mem (W := φ n) (s := s) (h := h)
    (K := K) (M := M) (T := T) hb1 hE1 hE2 hq' ha).1
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) hL0
  have hev := hφ.eventually (eventually_capProb_le hTL hb0 hb hE1 hE2 hlim hs h K hε)
  refine le_of_tendsto hL (hev.mono fun n hn => ?_)
  have := (capped_mem (W := φ n) (s := s) (h := h) (K := K) (M := M) (T := T) hb1
    hE1 hE2 hq' ha).2
  rw [h0, ENNReal.toReal_zero, zero_add] at hn
  linarith

/-- **Cap mass**: for non-atomic `h`, `capped → L` gives `condTransform → L / P(cap)`. -/
theorem tendsto_condTransform (hTL : TransmissionLawContract) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s T : ℝ}
    (hs : 0 < s) {p J : ℕ} {q : Fin p → ℝ → ℝ} {a : Fin J → Fin p → ℝ} {h : ℝ} (hh : 0 < h)
    (hA : NoAtom (entranceLaw P μ s) h) (K M : ℕ) (hne : entranceLaw P μ s (capSet K h) ≠ 0)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {L : ℝ}
    (hL : Tendsto (fun n => cappedClosedTransform b E s T h q a K M (φ n)) atTop (𝓝 L)) :
    Tendsto (fun n => condTransform b E s T h q a K M (φ n)) atTop
      (𝓝 (L / (entranceLaw P μ s (capSet K h)).toReal)) := by
  have := hlim.prob
  have := isFiniteMeasure_entranceLaw P μ s
  have hpos : (entranceLaw P μ s (capSet K h)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨hne, measure_ne_top _ _⟩
  have hP := (tendsto_capProb hTL hb0 hb hE1 hE2 hlim hs hh K (hA K)).comp hφ
  exact hL.div hP hpos

/-- **`CapCondLimit` from `CapCondLaw` and `TransmissionLawContract`.** -/
theorem capCondLimit_of_capCondLaw (hTL : TransmissionLawContract) (hC : CapCondLaw) :
    ClosedReduce.CapCondLimit := by
  intro b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM
  have := hlim.prob
  have := isFiniteMeasure_entranceLaw P μ s
  refine frequently_of_noAtom (entranceLaw P μ s) fun h hh0 hh1 hA => ?_
  refine (hC b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM h hh0 hh1 hA).mono
    fun K hK => ?_
  intro φ hφ L hL
  refine ⟨limit_eq_zero hTL hb0 hb hE1 hE2 hlim hs hq ha h K M hφ hL, fun hne => ?_⟩
  obtain ⟨Ω', m', 𝓖, Q, tseq, τ, G, hmod, hval⟩ :=
    hK hne φ hφ _ (tendsto_condTransform hTL hb0 hb hE1 hE2 hlim hs hh0 hA K M hne hφ hL)
  refine ⟨Ω', m', 𝓖, Q, tseq, τ, G, hmod, ?_⟩
  have hpos : (entranceLaw P μ s (capSet K h)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨hne, measure_ne_top _ _⟩
  rw [hval]
  field_simp

/-- **The same from the four input hypotheses.** -/
theorem capCondLimit_of_capCondLaw_baseContracts (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hC : CapCondLaw) : ClosedReduce.CapCondLimit :=
  capCondLimit_of_capCondLaw
    (BlockBand.Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP) hC

/-- From the input hypotheses and `CapCondLaw` (with the lead's
`sourceProcessContract_of_capCond`).
-/
theorem sourceProcessContract_of_capCondLaw (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hC : CapCondLaw) : SourceProcessContract :=
  SourceProcessMain.sourceProcessContract_of_capCond hMT hGA hLp hP hSR
    (capCondLimit_of_capCondLaw_baseContracts hMT hGA hLp hP hC)

end BlockBand.SourceProcess.CapCond
