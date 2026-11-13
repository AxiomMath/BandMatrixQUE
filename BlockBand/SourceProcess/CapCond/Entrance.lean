module

public import BlockBand.SourceProcess.CapCond.EntranceConv

/-!
# The weighted entrance on the cap event converges

**`tendsto_capWeighted`**: `E_W[1_{physCapEvent} w(μ_W(s))] → E[1{μ(s) ∈ capSet K h} w(μ(s))]` for
every bounded continuous `w ≥ 0`, when `t_K(μ(s))` has no atom at `h² > 0`. The proof sandwiches
the cap indicator between the weighted tests `wTest` (`finInt_le`, `le_finInt`,
`integral_wTest_le`, `limInt_le_integral_wTest`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedIdent
open scoped ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {b E : ℝ} {w : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ}

theorem norm_mul_small (w : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : δ ≤ ε / (2 * (‖w‖ + 1))) : ‖w‖ * δ ≤ ε / 2 := by
  have h1 : 0 < ‖w‖ + 1 := by positivity
  calc ‖w‖ * δ ≤ ‖w‖ * (ε / (2 * (‖w‖ + 1))) := mul_le_mul_of_nonneg_left hδ (norm_nonneg _)
    _ = ε / 2 * (‖w‖ / (‖w‖ + 1)) := by field_simp
    _ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left ((div_le_one h1).2 (by linarith)) (by positivity)
    _ = ε / 2 := mul_one _

/-- **The weighted entrance on the cap event converges.** -/
theorem tendsto_capWeighted (hTL : TransmissionLawContract) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s : ℝ}
    (hs : 0 < s) {h : ℝ} (hh : 0 < h) (K : ℕ)
    (h0 : entranceLaw P μ s {ν | seqExtract ν K = h ^ 2} = 0) (hw : ∀ ν, 0 ≤ w ν) :
    Tendsto (fun W => finInt b E s h K W w) atTop (𝓝 (limInt P μ s w (capSet K h))) := by
  have := hlim.prob
  have := isFiniteMeasure_entranceLaw P μ s
  have hμ := hlim.measurable s hs
  have hA := SourcePins.entranceAtomic_of hTL b hb0 hb E hE1 hE2 Ω _ P μ hlim s hs
  have hcap := measurableSet_capSet K h
  refine tendsto_order.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
  · -- lower bound
    set ε := limInt P μ s w (capSet K h) - x
    have hε : 0 < ε := sub_pos.2 hx
    have hη : 0 < ε / (2 * (‖w‖ + 1)) := by positivity
    have hh2 : 0 < h ^ 2 := by positivity
    obtain ⟨n, hn, hn'⟩ := (((tendsto_ent_below (entranceLaw P μ s) K h).eventually
      (lt_mem_nhds (sub_lt_self (entranceLaw P μ s {ν | seqExtract ν K < h ^ 2}).toReal hη))).and
      (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hh2))).exists
    have ha : 0 < h ^ 2 - 1 / ((n : ℝ) + 1) := by linarith
    have hac : h ^ 2 - 1 / ((n : ℝ) + 1) < h ^ 2 := by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hsub : {ν : Measure unitInterval | seqExtract ν K < h ^ 2 - 1 / ((n : ℝ) + 1)} ⊆
        capSet K h := fun ν (hν : seqExtract ν K < _) => (show seqExtract ν K ≤ h ^ 2 by linarith)
    have hgap := limInt_sub_le (P := P) (w := w) hμ (measurableSet_extract_lt K _) hcap hsub
    rw [← ent_lt_eq_capSet _ K h h0] at hgap
    have hmono : (entranceLaw P μ s {ν | seqExtract ν K < h ^ 2 - 1 / ((n : ℝ) + 1)}).toReal ≤
        (entranceLaw P μ s {ν | seqExtract ν K < h ^ 2}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ν (hν : seqExtract ν K < _) =>
        (show seqExtract ν K < h ^ 2 by linarith))
    have hsmall := norm_mul_small w hε (δ := (entranceLaw P μ s {ν | seqExtract ν K < h ^ 2}).toReal -
      (entranceLaw P μ s {ν | seqExtract ν K < h ^ 2 - 1 / ((n : ℝ) + 1)}).toReal)
      (by linarith)
    have hle := limInt_le_integral_wTest hw hμ hA ha hac K
    have hconv := hlim.fdd 1 (fun _ => s) (fun _ => hs) (wTest _ (h ^ 2) ha K w)
    filter_upwards [hconv.eventually (lt_mem_nhds (sub_lt_self
      (∫ ω, wTest _ (h ^ 2) ha K w (fun _ => μ s ω) ∂P) (half_pos hε))), eventually_ge_atTop 1]
      with W hW hW1
    have := le_finInt (s := s) hw hb hE1 hE2 hW1 ha hac le_rfl K
    linarith
  · -- upper bound
    set ε := x - limInt P μ s w (capSet K h)
    have hε : 0 < ε := sub_pos.2 hx
    have hη : 0 < ε / (2 * (‖w‖ + 1)) := by positivity
    obtain ⟨n, hn⟩ := ((tendsto_ent_above (entranceLaw P μ s) K h).eventually
      (gt_mem_nhds (lt_add_of_pos_right (entranceLaw P μ s (capSet K h)).toReal hη))).exists
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have ha : 0 < (h ^ 2 + (h ^ 2 + 1 / ((n : ℝ) + 1))) / 2 := by positivity
    have hac : (h ^ 2 + (h ^ 2 + 1 / ((n : ℝ) + 1))) / 2 < h ^ 2 + 1 / ((n : ℝ) + 1) := by
      linarith
    have hha : h ^ 2 < (h ^ 2 + (h ^ 2 + 1 / ((n : ℝ) + 1))) / 2 := by linarith
    have hsub : capSet K h ⊆ {ν : Measure unitInterval | seqExtract ν K < h ^ 2 + 1 / ((n : ℝ) + 1)} :=
      fun ν (hν : seqExtract ν K ≤ h ^ 2) => (show seqExtract ν K < _ by linarith)
    have hgap := limInt_sub_le (P := P) (w := w) hμ hcap (measurableSet_extract_lt K _) hsub
    have hmono : (entranceLaw P μ s (capSet K h)).toReal ≤
        (entranceLaw P μ s {ν | seqExtract ν K < h ^ 2 + 1 / ((n : ℝ) + 1)}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    have hsmall := norm_mul_small w hε
      (δ := (entranceLaw P μ s {ν | seqExtract ν K < h ^ 2 + 1 / ((n : ℝ) + 1)}).toReal -
        (entranceLaw P μ s (capSet K h)).toReal) (by linarith)
    have hle := integral_wTest_le hw hμ hA ha hac K
    have hconv := hlim.fdd 1 (fun _ => s) (fun _ => hs)
      (wTest _ (h ^ 2 + 1 / ((n : ℝ) + 1)) ha K w)
    filter_upwards [hconv.eventually (gt_mem_nhds (lt_add_of_pos_right
      (∫ ω, wTest _ (h ^ 2 + 1 / ((n : ℝ) + 1)) ha K w (fun _ => μ s ω) ∂P) (half_pos hε))),
      eventually_ge_atTop 1] with W hW hW1
    have := finInt_le (s := s) hw hb hE1 hE2 hW1 ha hac hha K
    linarith

end BlockBand.SourceProcess.CapCond
