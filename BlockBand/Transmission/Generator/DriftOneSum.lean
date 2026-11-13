module

public import BlockBand.Transmission.Generator.DriftOne
public import BlockBand.Transmission.Generator.Moments

/-!
# `PowerDriftSummable` at `k = 1`

`powerDriftSummable_one`: along every moving energy `e`, `Σ_{εW ≤ r ≤ TW} E|𝓡_r| → 0` for the
`k = 1` drift errors `𝓡_r`. Uses `e W → E` (`tendsto_movingEnergy`) and `D₀(e W) → D₀(E)`
(`tendsto_transportD0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal

/-- `e W → E` along a moving energy. -/
theorem tendsto_movingEnergy {E Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) :
    Tendsto e atTop (𝓝 E) := by
  have h0 : Tendsto (fun W : ℕ => Ce / (W : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp
      tendsto_natCast_atTop_atTop)
  have h1 : Tendsto (fun W : ℕ => e W - E) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_gt_atTop 0] with W hW
    rw [Real.norm_eq_abs]; exact he W hW
  have := h1.add_const E
  simpa using this

/-- `D₀(e W) → D₀(E)`. -/
theorem tendsto_transportD0 {b E Ce : ℝ} {e : ℕ → ℝ} (hE1 : -2 < E) (hE2 : E < 2)
    (he : IsMovingEnergy E Ce e) :
    Tendsto (fun W => |transportD0 b E - transportD0 b (e W)|) atTop (𝓝 0) := by
  have hne : b * (4 - E ^ 2) ≠ 0 ∨ b = 0 := by
    by_cases hb : b = 0
    · exact Or.inr hb
    · left; exact mul_ne_zero hb (by nlinarith)
  have hc : ContinuousAt (transportD0 b) E := by
    rcases hne with h | h
    · unfold transportD0
      exact continuousAt_const.div (continuousAt_const.mul
        (continuousAt_const.sub (continuousAt_id.pow 2))) h
    · have : transportD0 b = fun _ => 0 := by funext x; simp [transportD0, h]
      rw [this]; exact continuousAt_const
  have := (hc.tendsto.comp (tendsto_movingEnergy he))
  have h2 := (tendsto_const_nhds (x := transportD0 b E)).sub this
  simpa using h2.abs

/-- **`PowerDriftSummable`, `k = 1`.** -/
theorem powerDriftSummable_one (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hMix : PassiveSourceMixingBulk) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e → ∀ ε T : ℝ, 0 < ε → ε < T →
        Tendsto (fun W : ℕ => ∑ r ∈ lengthWindow ε T W,
          eLpNorm (driftError b E (e W) W 1 r) 2 (growthPathLaw W b)) atTop (𝓝 0) := by
  intro b hb0 hb E hE1 hE2 Ce e he ε T hε hεT
  obtain ⟨hκ, -⟩ := mem_bulk_min hE1 hE2
  set κI := min (2 + E) (2 - E)
  obtain ⟨K₁, K₂, W₀, hK₁, hK₂, hL⟩ := driftError_one_L2 hMT hGA hLp hMix (κ := κI / 2)
    (ε := ε / 2) (T := T) hb0 hb (by positivity) (by positivity) (by linarith)
  set Δ := fun W : ℕ => |transportD0 b E - transportD0 b (e W)|
  set U := fun W : ℕ => ENNReal.ofReal (T * (K₁ * (Real.sqrt W)⁻¹ + K₂ * Δ W))
  have hT0 : 0 < T := by linarith
  have hU : Tendsto U atTop (𝓝 0) := by
    have hs : Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    have h := ((hs.const_mul K₁).add ((tendsto_transportD0 (b := b) hE1 hE2 he).const_mul K₂)).const_mul T
    simp only [mul_zero, add_zero] at h
    simpa [U, Δ] using ENNReal.tendsto_ofReal h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop (max W₀ (max (EnergyUniform.windowWidth κI Ce) ⌈2 / ε⌉₊))]
    with W hW
  simp only [max_le_iff] at hW
  obtain ⟨hW0, hW1, hW2⟩ := hW
  have hmem := along_mem_bulk hE1 hE2 he hW1
  have hWε : 2 / ε ≤ (W : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hW2)
  have hεW : 2 ≤ ε * W := by rw [div_le_iff₀ hε] at hWε; linarith
  have hWpos : (0 : ℝ) < W := by nlinarith
  have hb' : ∀ r ∈ lengthWindow ε T W, eLpNorm (driftError b E (e W) W 1 r) 2 (growthPathLaw W b)
      ≤ ENNReal.ofReal (K₁ / Real.sqrt W ^ 3 + K₂ * Δ W / W) := by
    intro r hr
    rw [lengthWindow, Finset.mem_Ico] at hr
    have h1 := Nat.lt_floor_add_one ((W : ℝ) * ε)
    have h2 : (⌊(W : ℝ) * ε⌋₊ : ℝ) ≤ r := by exact_mod_cast hr.1
    have hr2 : ε / 2 * W ≤ r := by nlinarith
    have hr1 : 1 ≤ r := by
      have : (1 : ℝ) ≤ r := by nlinarith
      exact_mod_cast this
    have hr3 : (r : ℝ) ≤ T * W := by
      have h3 : (r : ℝ) < ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast hr.2
      have h4 := Nat.floor_le (mul_nonneg hWpos.le hT0.le)
      linarith
    exact hL W hW0 (e W) hmem E r hr1 hr2 hr3
  refine (Finset.sum_le_sum hb').trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hB0 : 0 ≤ K₁ / Real.sqrt W ^ 3 + K₂ * Δ W / W := by
    have : 0 ≤ Δ W := abs_nonneg _
    positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard : ((lengthWindow ε T W).card : ℝ) ≤ T * W := by
    rw [lengthWindow, Nat.card_Ico]
    have h4 := Nat.floor_le (mul_nonneg hWpos.le hT0.le)
    have : ((⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * ε⌋₊ : ℕ) : ℝ) ≤ (⌊(W : ℝ) * T⌋₊ : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    linarith
  have hsW : Real.sqrt W ^ 3 = W * Real.sqrt W := by
    rw [pow_succ, Real.sq_sqrt hWpos.le]
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  calc ((lengthWindow ε T W).card : ℝ) * (K₁ / Real.sqrt W ^ 3 + K₂ * Δ W / W)
      ≤ T * W * (K₁ / Real.sqrt W ^ 3 + K₂ * Δ W / W) := mul_le_mul_of_nonneg_right hcard hB0
    _ = T * (K₁ * (Real.sqrt W)⁻¹ + K₂ * Δ W) := by rw [hsW]; field_simp

end BlockBand.Transmission.Generator
