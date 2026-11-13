module

public import BlockBand.SourceProcess.FullSourceStops.Interface

/-!
# The field `compensatorUI`, from second moments of the coefficients

For `X = Σ_{j ∈ steps} W⁻¹a_j` with at most `TW` steps and `E a_j² ≤ C`, Cauchy–Schwarz gives
`E X² ≤ (#steps/W)² C ≤ T²C`, and `E[X; X > M] ≤ E X²/M ≤ η` for `M = T²C/η + 1`. Jensen's
inequality in time then gives the uniform integrability of the time integrals.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- `E[X; X > M] ≤ E X²/M`. -/
theorem lintegral_indicator_gt_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ≥0∞) {M : ℝ} (hM : 0 < M) :
    ∫⁻ ω, {ω | ENNReal.ofReal M < X ω}.indicator X ω ∂μ ≤
      (∫⁻ ω, X ω ^ 2 ∂μ) / ENNReal.ofReal M := by
  have hM0 : ENNReal.ofReal M ≠ 0 := by simpa using hM
  rw [ENNReal.div_eq_inv_mul, ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hM0)]
  refine lintegral_mono fun ω => ?_
  by_cases h : ω ∈ {ω | ENNReal.ofReal M < X ω}
  · rw [Set.indicator_of_mem h, ← ENNReal.div_eq_inv_mul,
      ENNReal.le_div_iff_mul_le (Or.inl hM0) (Or.inl ENNReal.ofReal_ne_top), sq]
    exact mul_le_mul_right (le_of_lt h) _
  · rw [Set.indicator_of_notMem h]; exact bot_le

/-- **Uniform integrability of a time sum** from second moments of its terms. -/
theorem lintegral_timeSum_gt_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (W : ℕ)
    (hW : 1 ≤ W) (s : Finset ℕ) {T : ℝ} (hsT : (s.card : ℝ) ≤ T * W) (a : ℕ → Ω → ℝ≥0∞)
    (ha : ∀ j ∈ s, Measurable (a j)) {C : ℝ} (hC : ∀ j ∈ s, ∫⁻ ω, a j ω ^ 2 ∂μ ≤ ENNReal.ofReal C)
    {M : ℝ} (hM : 0 < M) :
    ∫⁻ ω, {ω | ENNReal.ofReal M < ∑ j ∈ s, (W : ℝ≥0∞)⁻¹ * a j ω}.indicator
        (fun ω => ∑ j ∈ s, (W : ℝ≥0∞)⁻¹ * a j ω) ω ∂μ ≤
      ENNReal.ofReal (T ^ 2 * max C 0 / M) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hT : 0 ≤ T := by
    have := (Nat.cast_nonneg s.card).trans hsT
    exact nonneg_of_mul_nonneg_left this hW0
  refine (lintegral_indicator_gt_le μ _ hM).trans ?_
  have hsq : ∫⁻ ω, (∑ j ∈ s, (W : ℝ≥0∞)⁻¹ * a j ω) ^ 2 ∂μ ≤ ENNReal.ofReal (T ^ 2 * max C 0) := by
    have hpt : ∀ ω, (∑ j ∈ s, (W : ℝ≥0∞)⁻¹ * a j ω) ^ 2 ≤
        (s.card : ℝ≥0∞) * ∑ j ∈ s, ((W : ℝ≥0∞)⁻¹ * a j ω) ^ 2 := fun ω => by
      have := ENNReal.rpow_sum_le_const_mul_sum_rpow s (fun j => (W : ℝ≥0∞)⁻¹ * a j ω)
        (by norm_num : (1 : ℝ) ≤ 2)
      simp only [ENNReal.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at this
      exact this
    calc ∫⁻ ω, (∑ j ∈ s, (W : ℝ≥0∞)⁻¹ * a j ω) ^ 2 ∂μ
        ≤ ∫⁻ ω, (s.card : ℝ≥0∞) * ∑ j ∈ s, ((W : ℝ≥0∞)⁻¹ * a j ω) ^ 2 ∂μ := lintegral_mono hpt
      _ = (s.card : ℝ≥0∞) * ∑ j ∈ s, ((W : ℝ≥0∞)⁻¹) ^ 2 * ∫⁻ ω, a j ω ^ 2 ∂μ := by
          rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j hj =>
            ((ha j hj).const_mul ((W : ℝ≥0∞)⁻¹)).pow_const 2), lintegral_finsetSum' _ fun j hj =>
            (((ha j hj).const_mul ((W : ℝ≥0∞)⁻¹)).pow_const 2).aemeasurable]
          congr 1
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [mul_pow]
          exact lintegral_const_mul _ ((ha j hj).pow_const 2)
      _ ≤ (s.card : ℝ≥0∞) * ∑ _j ∈ s, ((W : ℝ≥0∞)⁻¹) ^ 2 * ENNReal.ofReal (max C 0) := by
          gcongr with j hj
          exact (hC j hj).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ((s.card : ℝ≥0∞) * (W : ℝ≥0∞)⁻¹) ^ 2 * ENNReal.ofReal (max C 0) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ENNReal.ofReal T ^ 2 * ENNReal.ofReal (max C 0) := by
          gcongr
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast W,
            ← ENNReal.ofReal_inv_of_pos hW0, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← div_eq_mul_inv, div_le_iff₀ hW0]; exact hsT
      _ = ENNReal.ofReal (T ^ 2 * max C 0) := by
          rw [← ENNReal.ofReal_pow hT, ← ENNReal.ofReal_mul (by positivity)]
  calc (∫⁻ ω, (∑ j ∈ s, (W : ℝ≥0∞)⁻¹ * a j ω) ^ 2 ∂μ) / ENNReal.ofReal M
      ≤ ENNReal.ofReal (T ^ 2 * max C 0) / ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (T ^ 2 * max C 0 / M) := (ENNReal.ofReal_div_of_pos hM).symm

/-- **The field `compensatorUI`**, from the hypothesis `CompensatorCoefficientMoments`. -/
theorem compensatorUI_of (h : CompensatorCoefficientMoments) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ → ∀ ε T η : ℝ, 0 < ε → ε < T → 0 < η →
    ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ k : Fin nT → ℕ,
      let steps := (Finset.range ⌊T * W⌋₊).filter fun j : ℕ => ε * W ≤ (j : ℝ)
      let drift : GrowthPath W → ℝ≥0∞ := fun ω => ∑ j ∈ steps, (W : ℝ≥0∞)⁻¹ *
        ‖polyValue b E k q W j ω (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)‖ₑ
      let qv : GrowthPath W → ℝ≥0∞ := fun ω => ∑ j ∈ steps, (W : ℝ≥0∞)⁻¹ *
        ‖polyValue b E k q W j ω (wordCarre b E Φ)‖ₑ
      ∫⁻ ω, {ω | ENNReal.ofReal M < drift ω}.indicator drift ω ∂growthPathLaw W b ≤
          ENNReal.ofReal η ∧
        ∫⁻ ω, {ω | ENNReal.ofReal M < qv ω}.indicator qv ω ∂growthPathLaw W b ≤
          ENNReal.ofReal η := by
  intro b hb0 hb κI hκ nT nI q hq Φ hΦ ε T η hε hεT hη
  obtain ⟨C, W₀, hC⟩ := h b hb0 hb κI hκ nT nI q hq Φ hΦ ε T hε hεT
  have hT : 0 < T := hε.trans hεT
  set M := T ^ 2 * max C 0 / η + 1
  have hM : 0 < M := by positivity
  have hMη : T ^ 2 * max C 0 / M ≤ η := by
    rw [div_le_iff₀ hM]
    have : T ^ 2 * max C 0 = T ^ 2 * max C 0 / η * η := by field_simp
    nlinarith
  refine ⟨M, max W₀ 1, fun W hW E hE k => ?_⟩
  have hW0 : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  set s := (Finset.range ⌊T * W⌋₊).filter fun j : ℕ => ε * W ≤ (j : ℝ)
  have hsT : (s.card : ℝ) ≤ T * W := by
    have h1 : s.card ≤ ⌊T * W⌋₊ := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
  have hjs : ∀ j ∈ s, ε * W ≤ j ∧ (j : ℝ) ≤ T * W := fun j hj => by
    rw [Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨hj.2, (Nat.cast_le.mpr hj.1.le).trans (Nat.floor_le (by positivity))⟩
  have hCj := fun j (hj : j ∈ s) => hC W hW0 E hE k j (hjs j hj).1 (hjs j hj).2
  refine ⟨(lintegral_timeSum_gt_le _ W hW1 s hsT _ (fun j hj => (hCj j hj).1.enorm)
      (fun j hj => (hCj j hj).2.2.1) hM).trans (ENNReal.ofReal_le_ofReal hMη),
    (lintegral_timeSum_gt_le _ W hW1 s hsT _ (fun j hj => (hCj j hj).2.1.enorm)
      (fun j hj => (hCj j hj).2.2.2) hM).trans (ENNReal.ofReal_le_ofReal hMη)⟩

end BlockBand.SourceProcess.FullSourceStops
