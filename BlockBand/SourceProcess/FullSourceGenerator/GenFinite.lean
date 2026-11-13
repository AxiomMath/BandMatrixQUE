module

public import BlockBand.SourceProcess.FullSourceGenerator.GenStep

/-!
# The tested increments vanish as `W → ∞`

`tendsto_tested`: along windows `[j₀, j₁]` in `[εW, TW]` after all tag births, the tested
finite-`W` increments of `Φ - ∫𝒜Φ` vanish as `W → ∞`.

Hypotheses: `EarlySummed`, `FullSourceStopsContract` and the four hypotheses `MatchedTracesContract`,
`GaussianAbsorptionContract`, `GaussianLpGradient`, `ScalarRecursionContract` of
`lintegral_polyValue_pow_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory MvPolynomial Finset Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

theorem memLp_two_of_lintegral_four {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) {B : ℝ}
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂μ ≤ ENNReal.ofReal B) : MemLp f 2 μ := by
  refine memLp_two_of_lintegral hf (ne_top_of_le_ne_top (b := ∫⁻ ω, (1 + ‖f ω‖ₑ ^ 4) ∂μ) ?_ ?_)
  · rw [lintegral_add_left measurable_const, lintegral_const]
    exact ENNReal.add_ne_top.mpr ⟨by simp, ne_top_of_le_ne_top ENNReal.ofReal_ne_top h⟩
  · refine lintegral_mono fun ω => ?_
    rw [enorm_sq_eq_ofReal, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
    exact ENNReal.ofReal_le_ofReal (sq_le_one_add_pow4 _)

/-- **The tested finite-`W` increments of `Φ - ∫𝒜Φ` vanish.** -/
theorem tendsto_tested (hES : EarlySummed) (hFS : FullSourceStopsContract)
    (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {nT nI : ℕ} {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q)
    {t₀ : ℝ} (hq0 : ∀ a t, t₀ < t → q a t = 0) {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ)
    {ε T : ℝ} (hε : 0 < ε) (hεT : ε < T) (k : ℕ → Fin nT → ℕ) (j₀ j₁ : ℕ → ℕ)
    (hj : ∀ᶠ W : ℕ in atTop, ε * W ≤ j₀ W ∧ t₀ * W < j₀ W + 1 ∧ j₀ W ≤ j₁ W ∧
      (j₁ W : ℝ) ≤ T * W ∧ ∀ a, k W a < j₀ W)
    (ξ : (W : ℕ) → GrowthPath W → ℂ) (hξm : ∀ W, StronglyMeasurable[growthSigma W (j₀ W)] (ξ W))
    {B : ℝ} (hξ4 : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ‖ξ W ω‖ₑ ^ 4 ∂growthPathLaw W b ≤ ENNReal.ofReal B)
    (hξK : ∀ K : ℝ, ∃ BK : ℝ, 0 ≤ BK ∧ ∀ᶠ W : ℕ in atTop, ∀ᵐ ω ∂growthPathLaw W b,
      ω ∈ alive b E (k W) q K ε W (j₀ W) → ‖ξ W ω‖ ≤ BK) :
    Tendsto (fun W : ℕ => ∫ ω, ξ W ω * (polyValue b E (k W) q W (j₁ W) ω Φ -
      polyValue b E (k W) q W (j₀ W) ω Φ - ∑ j ∈ Ico (j₀ W) (j₁ W),
        (W : ℂ)⁻¹ * polyValue b E (k W) q W j ω (wordGenerator b E q (t₀ + 1) Φ))
          ∂growthPathLaw W b) atTop (𝓝 0) := by
  have hRo := isOrdinaryPoly_of_mem (rePart_mem hΦ)
  have hIo := isOrdinaryPoly_of_mem (imPart_mem hΦ)
  obtain ⟨CX, WX, hCX0, hCX⟩ := lintegral_polyValue_pow_le hMT hGA hLp hSR hb0 hb hE1 hE2 hq hε
    hεT (mem_ordPoly_of_isOrdinaryPoly hΦ) 2
  obtain ⟨Cg, Wg, hCg0, hCg⟩ := lintegral_polyValue_pow_le hMT hGA hLp hSR hb0 hb hE1 hE2 hq hε
    hεT (wordGenerator_mem hΦ b E q (t₀ + 1)) 2
  obtain ⟨CR, WR, hCR0, hCR⟩ := lintegral_polyValue_pow_le hMT hGA hLp hSR hb0 hb hE1 hE2 hq hε
    hεT (wordCarre_mem hRo b E) 1
  obtain ⟨CI, WI, hCI0, hCI⟩ := lintegral_polyValue_pow_le hMT hGA hLp hSR hb0 hb hE1 hE2 hq hε
    hεT (wordCarre_mem hIo b E) 1
  obtain ⟨Ct, hCt⟩ := hFS.tail b hb0 hb E hE1 hE2 nT nI q hq ε T hε hεT
  rw [Metric.tendsto_nhds]
  intro η hη
  set B' := max B 0
  have hB' : 0 ≤ B' := le_max_right _ _
  set L := 6 * CX + 3 * (T ^ 2 * Cg) + 4 * (2 + T * (CR + CI))
  have hT0 : 0 < T := hε.trans hεT
  have hL : 0 ≤ L := by positivity
  set lam := η / (5 * (L + 1))
  have hlam : 0 < lam := by positivity
  set kap := 4 * lam * η / (5 * (B' + 1))
  have hkap : 0 < kap := by positivity
  set K := 5 * (|Ct| + 1) / (4 * lam * kap * η)
  have hK : 0 < K := by positivity
  obtain ⟨BK, hBK0, hBK⟩ := hξK K
  obtain ⟨C₁, W₁, hC₁⟩ := hES b hb0 hb E hE1 hE2 nT nI q hq Φ hΦ ε T K hε hεT
  obtain ⟨C₂, W₂, hC₂⟩ := hES b hb0 hb E hE1 hE2 nT nI q hq (rePart Φ) hRo ε T K hε hεT
  obtain ⟨C₃, W₃, hC₃⟩ := hES b hb0 hb E hE1 hE2 nT nI q hq (imPart Φ) hIo ε T K hε hεT
  have hCtK : Ct / K < (|Ct| + 1) / K := div_lt_div_of_pos_right (by linarith [le_abs_self Ct]) hK
  have hstop : ∀ᶠ W : ℕ in atTop, (⨆ k' : Fin nT → ℕ, growthPathLaw W b {ω | ∃ j : ℕ,
      ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧ K < traceLoad b E k' q W j ω}) <
        ENNReal.ofReal ((|Ct| + 1) / K) :=
    eventually_lt_of_limsup_lt ((hCt K hK).trans_lt
      (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hCtK, by positivity⟩))
  set e : ℕ → ℝ := fun W => 1 / Real.sqrt W + 1 / (W : ℝ)
  have he0 : ∀ W, 0 ≤ e W := fun W => by positivity
  have hlim := tendsto_err
  have h1 : ∀ᶠ W : ℕ in atTop, BK * (max C₁ 0 * e W) < η / 5 := by
    have := (hlim.const_mul (max C₁ 0)).const_mul BK
    simp only [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  have h2 : ∀ᶠ W : ℕ in atTop, max C₂ 0 * e W < 1 := by
    have := hlim.const_mul (max C₂ 0)
    simp only [mul_zero] at this
    exact this.eventually (gt_mem_nhds one_pos)
  have h3 : ∀ᶠ W : ℕ in atTop, max C₃ 0 * e W < 1 := by
    have := hlim.const_mul (max C₃ 0)
    simp only [mul_zero] at this
    exact this.eventually (gt_mem_nhds one_pos)
  filter_upwards [hj, hξ4, hBK, hstop, h1, h2, h3,
    eventually_ge_atTop (max (max (max WX Wg) (max WR WI)) (max (max W₁ W₂) (max W₃ 1)))]
    with W hjW hξW hBKW hstopW h1W h2W h3W hWge
  obtain ⟨hε₀, ht₀, hj01, hj₁, hka⟩ := hjW
  simp only [max_le_iff] at hWge
  obtain ⟨⟨⟨hWX, hWg⟩, hWR, hWI⟩, ⟨hW₁, hW₂⟩, hW₃, hW1⟩ := hWge
  have hξ2 := memLp_two_of_lintegral_four
    ((hξm W).mono (growthSigma_le' W _)).aestronglyMeasurable hξW
  have key := tested_le hW1 hq hq0 hΦ (k W) K ε T hε₀ ht₀ hj01 hj₁ hCX0 hCg0 hCR0 hCI0
    (fun j h1 h2 => hCX W hWX (k W) j h1 h2) (fun j h1 h2 => hCg W hWg (k W) j h1 h2)
    (fun j h1 h2 => hCR W hWR (k W) j h1 h2) (fun j h1 h2 => hCI W hWI (k W) j h1 h2)
    (hξm W) hξ2 hBK0 hBKW hlam hkap
  -- the window sums are among the `EarlySummed` steps
  have hsub : Ico (j₀ W) (j₁ W) ⊆ (range ⌊T * W⌋₊).filter fun j : ℕ => j₀ W ≤ j := by
    intro j hjm
    have h := Finset.mem_Ico.mp hjm
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le h.2 ?_), h.1⟩
    exact Nat.le_floor hj₁
  have hS1 : driftSum b E (k W) q K ε W Φ (j₀ W) (j₁ W) ≤ ENNReal.ofReal (max C₁ 0 * e W) :=
    ((Finset.sum_le_sum_of_subset hsub).trans (hC₁ W hW₁ (k W) (j₀ W) hε₀ hka).1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (he0 W)))
  have hS2 : carreSum b E (k W) q K ε W (rePart Φ) (j₀ W) (j₁ W) ≤ ENNReal.ofReal 1 :=
    ((Finset.sum_le_sum_of_subset hsub).trans (hC₂ W hW₂ (k W) (j₀ W) hε₀ hka).2).trans
      (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_max_left _ _) (he0 W)).trans
        h2W.le))
  have hS3 : carreSum b E (k W) q K ε W (imPart Φ) (j₀ W) (j₁ W) ≤ ENNReal.ofReal 1 :=
    ((Finset.sum_le_sum_of_subset hsub).trans (hC₃ W hW₃ (k W) (j₀ W) hε₀ hka).2).trans
      (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_max_left _ _) (he0 W)).trans
        h3W.le))
  have hP : growthPathLaw W b (stopEvent b E (k W) q K ε T W) ≤
      ENNReal.ofReal ((|Ct| + 1) / K) :=
    (le_iSup (fun k' : Fin nT → ℕ => growthPathLaw W b {ω | ∃ j : ℕ,
      ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧ K < traceLoad b E k' q W j ω}) (k W)).trans hstopW.le
  have hξB : ∫⁻ ω, ‖ξ W ω‖ₑ ^ 4 ∂growthPathLaw W b ≤ ENNReal.ofReal B' :=
    hξW.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the four terms
  have t1 : ENNReal.ofReal BK * driftSum b E (k W) q K ε W Φ (j₀ W) (j₁ W) ≤
      ENNReal.ofReal (η / 5) := by
    refine (mul_le_mul' le_rfl hS1).trans ?_
    rw [← ENNReal.ofReal_mul hBK0]; exact ENNReal.ofReal_le_ofReal h1W.le
  have t2 : ENNReal.ofReal lam * (ENNReal.ofReal (6 * CX + 3 * (T ^ 2 * Cg)) +
      4 * (carreSum b E (k W) q K ε W (rePart Φ) (j₀ W) (j₁ W) +
        carreSum b E (k W) q K ε W (imPart Φ) (j₀ W) (j₁ W) + ENNReal.ofReal (T * (CR + CI)))) ≤
      ENNReal.ofReal (η / 5) := by
    have hin : ENNReal.ofReal (6 * CX + 3 * (T ^ 2 * Cg)) +
        4 * (carreSum b E (k W) q K ε W (rePart Φ) (j₀ W) (j₁ W) +
          carreSum b E (k W) q K ε W (imPart Φ) (j₀ W) (j₁ W) + ENNReal.ofReal (T * (CR + CI))) ≤
        ENNReal.ofReal L := by
      calc _ ≤ ENNReal.ofReal (6 * CX + 3 * (T ^ 2 * Cg)) +
            4 * (ENNReal.ofReal 1 + ENNReal.ofReal 1 + ENNReal.ofReal (T * (CR + CI))) := by
            gcongr
        _ = ENNReal.ofReal L := by
            rw [← ENNReal.ofReal_add zero_le_one zero_le_one,
              ← ENNReal.ofReal_add (by norm_num) (by positivity), ← ENNReal.ofReal_ofNat 4,
              ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
                (by positivity)]
            norm_num [L]
    refine (mul_le_mul' le_rfl hin).trans ?_
    rw [← ENNReal.ofReal_mul hlam.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : lam * L = η / 5 * (L / (L + 1)) := by simp only [lam]; field_simp
    rw [this]
    have : L / (L + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  have t3 : ENNReal.ofReal (1 / (4 * lam * kap)) *
      growthPathLaw W b (stopEvent b E (k W) q K ε T W) ≤ ENNReal.ofReal (η / 5) := by
    refine (mul_le_mul' le_rfl hP).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    simp only [K]; field_simp
  have t4 : ENNReal.ofReal (kap / (4 * lam)) * ∫⁻ ω, ‖ξ W ω‖ₑ ^ 4 ∂growthPathLaw W b ≤
      ENNReal.ofReal (η / 5) := by
    refine (mul_le_mul' le_rfl hξB).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : kap / (4 * lam) * B' = η / 5 * (B' / (B' + 1)) := by simp only [kap]; field_simp
    rw [this]
    have : B' / (B' + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  have htot := key.trans (add_le_add (add_le_add (add_le_add t1 t2) t3) t4)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ofReal_norm] at htot
  rw [dist_zero_right]
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htot
  linarith

end BlockBand.SourceProcess.FullSourceGenerator
