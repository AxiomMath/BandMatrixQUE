module

public import BlockBand.SourceProcess.ClosingLeak.Mass
public import BlockBand.SourceProcess.SourceProcessLaw.EarlyHolds

/-!
# The leaked path mass `Re Tr(farEmbed(A_-) Q(q))` is integrable

Since `farEmbed(A_-)` is an orthogonal projection and `Q(q) ⪰ 0`, the leaked mass is at most
`Re Tr Q(q)`; the tag moments of `FullSourceMomentsContract` then make it integrable for all
large `W` (`eventually_integrable_leak`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingLeak

open Matrix MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Sampling
open scoped ComplexOrder

variable {W : ℕ}

/-- `Re Tr(PQ) ≤ Re Tr Q` for an orthogonal projection `P` and `Q ⪰ 0`. -/
theorem re_trace_proj_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] {P Q : Matrix ι ι ℂ}
    (hP2 : P * P = P) (hPH : Pᴴ = P) (hQ : Q.PosSemidef) : (P * Q).trace.re ≤ Q.trace.re := by
  have e : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hPH, sub_mul, mul_sub, mul_sub, hP2]
    simp
  have h := re_trace_mul_nonneg (e ▸ posSemidef_conjTranspose_mul_self (1 - P)) hQ
  rw [sub_mul, one_mul, trace_sub, Complex.sub_re] at h
  linarith

theorem intervalSource_psd (b E : ℝ) (n : ℕ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (ω : GrowthPath W) : (intervalSource b E W n q ω).PosSemidef :=
  posSemidef_sum _ fun k _ => PosSemidef.smul
    ((tagProjection_posSemidef n k).conjTranspose_mul_mul_same _)
    (Complex.zero_le_real.2 (div_nonneg (hq _) (sq_nonneg _)))

theorem re_trace_intervalSource (b E : ℝ) (n : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    (intervalSource b E W n q ω).trace.re = ∑ k ∈ Finset.range n,
      q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 * (tagResponse b E W n k ω).trace.re := by
  simp only [intervalSource, trace_sum, trace_smul, smul_eq_mul, Complex.re_sum,
    Complex.re_ofReal_mul]

theorem measurable_intervalSource (b E : ℝ) (n : ℕ) (q : ℝ → ℝ) :
    Measurable (intervalSource b E W n q) :=
  measurable_matrix_sum _ fun k _ => measurable_matrix_smul _ (measurable_tagResponse b E n k)

/-- **The leaked path mass is integrable** for all large `W` (tag moments, `p = 1`). -/
theorem eventually_integrable_leak (hFM : FullSourceMomentsContract) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {s T h : ℝ} (hT : 0 < T) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) :
    ∀ᶠ W in atTop, Integrable (fun ω => (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
      intervalSource b E W ⌊(W : ℝ) * T⌋₊ q ω).trace.re) (growthPathLaw W b) := by
  obtain ⟨C, W₀, hC⟩ := hFM.tag b hb0 hb E hE1 hE2 T 1 le_rfl
  filter_upwards [eventually_ge_atTop (max W₀ 1)] with W hW
  have hW0 : 0 < W := by omega
  set n := ⌊(W : ℝ) * T⌋₊
  have hn : (n : ℝ) ≤ T * W := by
    rw [mul_comm]; exact Nat.floor_le (by positivity)
  have hY : ∀ k ∈ Finset.range n,
      Integrable (fun ω => (tagResponse b E W n k ω).trace.re) (growthPathLaw W b) := by
    intro k hk
    have h1 := hC W (le_of_max_le_left hW) n hn k (Finset.mem_range.1 hk)
    rw [ENNReal.ofReal_one] at h1
    have h2 := h1.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))
    rw [← ENNReal.ofReal_one] at h2
    exact (tag_mean_le hW0 (le_max_right C 0) h2).1
  have hG : Integrable (fun ω => (intervalSource b E W n q ω).trace.re) (growthPathLaw W b) := by
    simp_rw [re_trace_intervalSource]
    exact integrable_finsetSum _ fun k hk => (hY k hk).const_mul _
  have hm : Measurable fun ω => (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
      intervalSource b E W n q ω).trace.re :=
    measurable_trace_re (measurable_matrix_mul'
      (measurable_farEmbed (measurable_omittedProj b E h _)) (measurable_intervalSource b E n q))
  refine hG.mono' hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have hQ := intervalSource_psd b E n hq ω
  have h0 := re_trace_mul_nonneg (farEmbed_omittedProj_psd b E h ⌊(W : ℝ) * s⌋₊ ω) hQ
  have h1 := re_trace_proj_mul_le
    (by rw [farEmbed_mul, omittedProj_mul_self] :
      farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
        farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) =
          farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
    (by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]) hQ
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

end BlockBand.SourceProcess.ClosingLeak
