module

public import BlockBand.Transmission.LawForced.AbsL1
public import BlockBand.Transmission.LawForced.RatioSum
public import BlockBand.Transmission.LawForced.ForcingRate

/-!
# `RatioDriftSummable` for every admissible profile, from the absorbed moment bounds

* `tendsto_time_shift`: for continuous `h`, `Σ_{⌊εW⌋ ≤ r < ⌊TW⌋} |h(r/W) − h((r+1)/W)|/W → 0`
  (uniform continuity on `[0, T+1]`): the block added at step `r + 1` carries
  `κ((r+1)/W)/W²`, while `RatioDriftSummable` uses `h(r/W)`;
* **`ratioDriftSummable_of_pins hMT hGA hLp hP hJ hMix : RatioDriftSummable`**, with `hJ`,
  `hMix` the hypotheses `Absorbed.AbsorbedJetMoments`, `Absorbed.AbsorbedSourceMixingBulk`:
  `Σ_r E|ratioDriftError_r| ≤ T·C/√W + R·Σ_r|h(r/W) − h((r+1)/W)|/W → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Generator BlockBand.Transmission.LawDuality

theorem card_Ico_floor_le {W : ℕ} {ε T : ℝ} (hT : 0 ≤ T) :
    ((Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊).card : ℝ) ≤ T * W := by
  rw [Nat.card_Ico]
  have h4 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg W) hT)
  have : ((⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * ε⌋₊ : ℕ) : ℝ) ≤ (⌊(W : ℝ) * T⌋₊ : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  linarith

/-- **The time shift is `o(1)` after summation.** -/
theorem tendsto_time_shift {h : ℝ → ℝ} (hc : Continuous h) {ε T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun W : ℕ => ∑ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
      |h ((r : ℝ) / W) - h (((r : ℝ) + 1) / W)| / W) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hU := (isCompact_Icc (a := (0 : ℝ)) (b := T + 1)).uniformContinuousOn_of_continuous
    hc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hU
  obtain ⟨ρ, hρ, hUρ⟩ := hU (δ / (2 * (T + 1))) (by positivity)
  refine ⟨max 1 (⌈ρ⁻¹⌉₊ + 1), fun W hW => ?_⟩
  simp only [max_le_iff] at hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW.1
  have hW0 : (0 : ℝ) < W := by linarith
  have hWρ : ρ⁻¹ < W := by
    have := Nat.le_ceil ρ⁻¹
    have : ((⌈ρ⁻¹⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW.2
    push_cast at this; linarith
  have hterm : ∀ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
      |h ((r : ℝ) / W) - h (((r : ℝ) + 1) / W)| / W ≤ δ / (2 * (T + 1)) / W := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hrT : (r : ℝ) < W * T := by
      have h3 : (r : ℝ) < ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast hr.2
      exact h3.trans_le (Nat.floor_le (mul_nonneg hW0.le hT))
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have m1 : (r : ℝ) / W ∈ Set.Icc 0 (T + 1) := by
      refine ⟨div_nonneg hr0 hW0.le, ?_⟩
      rw [div_le_iff₀ hW0]; nlinarith
    have m2 : ((r : ℝ) + 1) / W ∈ Set.Icc 0 (T + 1) := by
      refine ⟨div_nonneg (by linarith) hW0.le, ?_⟩
      rw [div_le_iff₀ hW0]; nlinarith
    have hd : dist ((r : ℝ) / W) (((r : ℝ) + 1) / W) < ρ := by
      rw [Real.dist_eq, show (r : ℝ) / W - ((r : ℝ) + 1) / W = -(1 / W) by field_simp; ring,
        abs_neg, abs_of_pos (by positivity), one_div]
      rw [inv_lt_comm₀ hW0 hρ]; exact hWρ
    have := hUρ _ m1 _ m2 hd
    rw [Real.dist_eq] at this
    exact div_le_div_of_nonneg_right this.le hW0.le
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard := card_Ico_floor_le (W := W) (ε := ε) hT
  have h0 : 0 ≤ ∑ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
      |h ((r : ℝ) / W) - h (((r : ℝ) + 1) / W)| / W :=
    Finset.sum_nonneg fun _ _ => div_nonneg (abs_nonneg _) hW0.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  have hk : 0 ≤ δ / (2 * (T + 1)) / W := by positivity
  have := mul_le_mul_of_nonneg_right hcard hk
  have e : T * W * (δ / (2 * (T + 1)) / W) = T * δ / (2 * (T + 1)) := by field_simp
  have hlt : T * δ / (2 * (T + 1)) < δ := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  linarith

theorem drift_D_eq {b E : ℝ} (hb : b < 1) (hE : E ^ 2 ≤ 4) (κ : ℝ → ℝ) {W : ℕ} (hW : (0 : ℝ) < W)
    (r : ℕ) : |absorptionRate E κ ((r : ℝ) / W) / W -
      4 * etaZ b E * dStar b * layerAbsorption W κ (r + 1) 0 * W| =
      |absorptionRate E κ ((r : ℝ) / W) - absorptionRate E κ (((r : ℝ) + 1) / W)| / W := by
  have hl : layerAbsorption W κ (r + 1) 0 = κ (((r : ℝ) + 1) / W) / (W : ℝ) ^ 2 := by
    simp [layerAbsorption]
  rw [hl, absorptionRate_eq_injection hb hE κ (((r : ℝ) + 1) / W)]
  rw [show absorptionRate E κ ((r : ℝ) / W) / W - 4 * etaZ b E * dStar b *
      (κ (((r : ℝ) + 1) / W) / (W : ℝ) ^ 2) * W = (absorptionRate E κ ((r : ℝ) / W) -
        4 * etaZ b E * dStar b * κ (((r : ℝ) + 1) / W)) / W by field_simp,
    abs_div, abs_of_pos hW]

/-- **`RatioDriftSummable` for every admissible profile**, from the input hypotheses and the two
absorbed moment bounds `Absorbed.AbsorbedJetMoments` and `Absorbed.AbsorbedSourceMixingBulk`. -/
theorem ratioDriftSummable_of_pins (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hJ : Absorbed.AbsorbedJetMoments) (hMix : Absorbed.AbsorbedSourceMixingBulk) :
    RatioDriftSummable := by
  intro b hb0 hb E hE1 hE2 κ hκ p z hz ε T hε hεT
  obtain ⟨hκI, hEb⟩ := mem_bulk_min hE1 hE2
  obtain ⟨C, W₀, hC0, hL⟩ := ratioDriftError_abs_L1 hMT hGA hLp hP hJ hMix
    (κI := min (2 + E) (2 - E)) (ε := ε / 2) (T := T + 1) hb0 hb hκI (by positivity)
    (by linarith) hκ hz
  have hT0 : 0 < T := by linarith
  have hb1 : b < 1 := by linarith
  have hE4 : E ^ 2 ≤ 4 := by nlinarith
  have hzr := IsRatioParameter.isRatioRange hz
  have hR : 0 ≤ ∑ i, (z.1 i + z.2 i) := Finset.sum_nonneg fun i _ => by
    have := hzr.1 i; have := (hzr.2 i).1; linarith
  have hhc : Continuous (absorptionRate E κ) := continuous_const.mul hκ.1
  have hts := tendsto_time_shift hhc (ε := ε) hT0.le
  have hU : Tendsto (fun W : ℕ => T * C * (Real.sqrt W)⁻¹ + (∑ i, (z.1 i + z.2 i)) *
      ∑ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
        |absorptionRate E κ ((r : ℝ) / W) - absorptionRate E κ (((r : ℝ) + 1) / W)| / W)
      atTop (𝓝 0) := by
    have hs : Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    simpa using (hs.const_mul (T * C)).add (hts.const_mul (∑ i, (z.1 i + z.2 i)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ =>
      abs_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (max W₀ ⌈2 / ε⌉₊)] with W hW
  simp only [max_le_iff] at hW
  obtain ⟨hW0, hW2⟩ := hW
  have hWε : 2 / ε ≤ (W : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hW2)
  have hεW : 2 ≤ ε * W := by rw [div_le_iff₀ hε] at hWε; linarith
  have hWpos : (0 : ℝ) < W := by nlinarith
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  have hb' : ∀ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
      ∫ ω, |ratioDriftError b E κ W z r ω| ∂growthPathLaw W b ≤
        C * (Real.sqrt W)⁻¹ ^ 3 + (∑ i, (z.1 i + z.2 i)) *
          (|absorptionRate E κ ((r : ℝ) / W) - absorptionRate E κ (((r : ℝ) + 1) / W)| / W) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have h1 := Nat.lt_floor_add_one ((W : ℝ) * ε)
    have h2 : (⌊(W : ℝ) * ε⌋₊ : ℝ) ≤ r := by exact_mod_cast hr.1
    have hr2 : ε / 2 * W ≤ r := by nlinarith
    have hr1 : 1 ≤ r := by
      have : (1 : ℝ) ≤ r := by nlinarith
      exact_mod_cast this
    have hr3 : (r : ℝ) ≤ (T + 1) * W := by
      have h3 : (r : ℝ) < ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast hr.2
      have h4 := Nat.floor_le (mul_nonneg hWpos.le hT0.le)
      nlinarith
    have := hL W hW0 E hEb r hr1 hr2 hr3
    rwa [drift_D_eq hb1 hE4 κ hWpos r] at this
  refine (Finset.sum_le_sum hb').trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hcard := card_Ico_floor_le (W := W) (ε := ε) hT0.le
  have hK0 : 0 ≤ C * (Real.sqrt W)⁻¹ ^ 3 := by positivity
  have hsW : (W : ℝ) * (Real.sqrt W)⁻¹ ^ 3 = (Real.sqrt W)⁻¹ := by
    set q := Real.sqrt W
    have h2 : (W : ℝ) = q ^ 2 := (Real.sq_sqrt hWpos.le).symm
    rw [h2]
    have hq : q ≠ 0 := hs0.ne'
    field_simp
  have := mul_le_mul_of_nonneg_right hcard hK0
  have e : T * W * (C * (Real.sqrt W)⁻¹ ^ 3) = T * C * ((W : ℝ) * (Real.sqrt W)⁻¹ ^ 3) := by ring
  rw [hsW] at e
  linarith

end BlockBand.Transmission.LawForced
