module

public import BlockBand.SourceProcess.PhysApprox.B3LimDefs
public import BlockBand.SourceProcess.PhysApprox.IdentCap
public import BlockBand.SourceProcess.PhysApprox.IdentTested

/-!
# `ComplexCapCondLimit` from the conditioned law

* `abs_cappedClosedPhysExpectation_le_capProb`: `|capped| ≤ ‖Φ‖ P_W(physCapEventC)` (no
  measurability of the cap event needed).
* **Zero case** `complexCap_limit_eq_zero` (every `h, K`): if `P(μ(s) ∈ capSet K h) = 0`, every
  limit point of the capped expectation is `0` (`eventually_capProb_le`).
* **Cap mass** `tendsto_condClosedPhysExpectation`: for non-atomic `h`, `capped → L` gives
  `cond → L / P(μ(s) ∈ capSet K h)` (`tendsto_capProb`).
* **`complexCapCondLimit_of_law`**: `TransmissionLawContract → ComplexCapCondLaw →
  ComplexCapCondLimit` (frequent `h` by `frequently_of_noAtom`).
* `complexCapCondLaw_of_stopped`: the stopped tested form gives the filtered form
  (`IsStoppedTestedComplexModel.isFiniteComplexSourceModel`).
* **`targetCapCond'_of_law`**: `TargetCapCondLaw' → TargetCapCond'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}

/-- **`|capped| ≤ ‖Φ‖ P_W(physical cap event)`.** -/
theorem abs_cappedClosedPhysExpectation_le_capProb {b E s T h : ℝ} {np : ℕ} {τ m : Fin np → ℝ}
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (K W : ℕ) :
    |cappedClosedPhysExpectation b E s T h τ m Φ K W| ≤
      ‖Φ‖ * (growthPathLaw W b (physCapEventC b E s h K W)).toReal := by
  set ν := (probedPathLaw W np b).prod phaseLaw
  set A := (fun y : ProbedPath W np × ℝ => y.1.1) ⁻¹' physCapEventC b E s h K W
  have hA : ν A = growthPathLaw W b (physCapEventC b E s h K W) :=
    probedPhase_preimage_path b _
  unfold cappedClosedPhysExpectation
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  have hle : ∫⁻ y, ENNReal.ofReal ‖(physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
      Φ (closedSourceData b E s T h τ m W (phase y.2) y.1)‖ ∂ν ≤ ENNReal.ofReal ‖Φ‖ * ν A := by
    refine (lintegral_mono fun y => ?_).trans (lintegral_indicator_const_le A _)
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y.1.1 ∈ _ from hy), one_mul]
      exact ENNReal.ofReal_le_ofReal (Φ.norm_coe_le_norm _)
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (show y.1.1 ∉ _ from hy),
        zero_mul, norm_zero, ENNReal.ofReal_zero]
  have hfin : ENNReal.ofReal ‖Φ‖ * ν A ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  refine (ENNReal.toReal_mono hfin hle).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), hA]

/-- **Zero case**: with no entrance mass on the cap, every limit point of the capped closed
expectation is `0` (every `h`, every `K`). -/
theorem complexCap_limit_eq_zero (hTL : TransmissionLawContract) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s T : ℝ} (hs : 0 < s) {np : ℕ}
    {τ m : Fin np → ℝ} (Φ : BoundedContinuousFunction (SourceData np) ℝ) (h : ℝ) (K : ℕ)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {L : ℝ}
    (hL : Tendsto (fun n => cappedClosedPhysExpectation b E s T h τ m Φ K (φ n)) atTop (𝓝 L))
    (h0 : entranceLaw P μ s (capSet K h) = 0) : L = 0 := by
  refine abs_nonpos_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  have hN : 0 < ‖Φ‖ + 1 := by positivity
  have hev := hφ.eventually
    (CapCond.eventually_capProb_le hTL hb0 hb hE1 hE2 hlim hs h K (div_pos hε hN))
  rw [zero_add]
  refine le_of_tendsto hL.abs (hev.mono fun n hn => ?_)
  rw [h0, ENNReal.toReal_zero, zero_add] at hn
  have h1 := abs_cappedClosedPhysExpectation_le_capProb (b := b) (E := E) (s := s) (T := T)
    (h := h) (τ := τ) (m := m) Φ K (φ n)
  have h2 : ‖Φ‖ * (growthPathLaw (φ n) b (physCapEventC b E s h K (φ n))).toReal ≤
      ‖Φ‖ * (ε / (‖Φ‖ + 1)) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
  have h3 : ‖Φ‖ * (ε / (‖Φ‖ + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hN]
    nlinarith [norm_nonneg Φ]
  exact h1.trans (h2.trans h3)

/-- **Cap mass**: for non-atomic `h`, `capped → L` gives `cond → L / P(μ(s) ∈ capSet K h)`. -/
theorem tendsto_condClosedPhysExpectation (hTL : TransmissionLawContract) {b E : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s T : ℝ} (hs : 0 < s) {np : ℕ}
    {τ m : Fin np → ℝ} (Φ : BoundedContinuousFunction (SourceData np) ℝ) {h : ℝ} (hh : 0 < h)
    (hA : CapCond.NoAtom (entranceLaw P μ s) h) (K : ℕ)
    (hne : entranceLaw P μ s (capSet K h) ≠ 0) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {L : ℝ}
    (hL : Tendsto (fun n => cappedClosedPhysExpectation b E s T h τ m Φ K (φ n)) atTop (𝓝 L)) :
    Tendsto (fun n => condClosedPhysExpectation b E s T h τ m Φ K (φ n)) atTop
      (𝓝 (L / (entranceLaw P μ s (capSet K h)).toReal)) := by
  have := hlim.prob
  have := CapCond.isFiniteMeasure_entranceLaw P μ s
  have hpos : (entranceLaw P μ s (capSet K h)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨hne, measure_ne_top _ _⟩
  unfold condClosedPhysExpectation
  exact hL.div ((CapCond.tendsto_capProb hTL hb0 hb hE1 hE2 hlim hs hh K (hA K)).comp hφ) hpos

/-- **`ComplexCapCondLimit` from the conditioned law** (`TransmissionLawContract`). -/
theorem complexCapCondLimit_of_law (hTL : TransmissionLawContract) (hC : ComplexCapCondLaw) :
    ComplexCapCondLimit := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := id hD
  have := hlim.prob
  have := CapCond.isFiniteMeasure_entranceLaw P μ s
  refine CapCond.frequently_of_noAtom (entranceLaw P μ s) fun h hh0 hh1 hA => ?_
  refine (hC b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ h hh0 hh1 hA).mono fun K hK => ?_
  intro φ hφ L hL
  refine ⟨complexCap_limit_eq_zero hTL hb0 hb hE1 hE2 hlim hs Φ h K hφ hL, fun hne => ?_⟩
  obtain ⟨Ω', mΩ', 𝓖, Q, tseq, G, Kc, hM, hval⟩ := hK hne φ hφ _
    (tendsto_condClosedPhysExpectation hTL hb0 hb hE1 hE2 hlim hs Φ hh0 hA K hne hφ hL)
  refine ⟨Ω', mΩ', 𝓖, Q, tseq, G, Kc, hM, ?_⟩
  have hpos : (entranceLaw P μ s (capSet K h)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨hne, measure_ne_top _ _⟩
  rw [hval]
  field_simp

/-- **The stopped tested form gives the filtered form**
(`IsStoppedTestedComplexModel.isFiniteComplexSourceModel`, raw natural filtration). -/
theorem complexCapCondLaw_of_stopped (hS : ComplexCapCondLawStopped) : ComplexCapCondLaw := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ h hh0 hh1 hA
  have hb : b < 1 / 2 := hD.2.1
  have hm : ∀ j, 0 ≤ m j := hD.2.2.2.2.2.2.1
  refine (hS b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ h hh0 hh1 hA).mono
    fun K hK hne φ hφ ℓ hℓ => ?_
  obtain ⟨Ω', mΩ', Q, tseq, G, Kc, hT, hval⟩ := hK hne φ hφ ℓ hℓ
  exact ⟨Ω', mΩ', _, Q, tseq, G, Kc, hT.isFiniteComplexSourceModel (by linarith) hm, hval⟩

/-- **`TargetCapCond'` from the conditioned target.** -/
theorem targetCapCond'_of_law (hT : TargetCapCondLaw') : TargetCapCond' :=
  fun hTL hEx hS hTi hK hC hL => complexCapCondLimit_of_law hTL (hT hTL hEx hS hTi hK hC hL)

end BlockBand.SourceProcess.PhysApprox.B3
