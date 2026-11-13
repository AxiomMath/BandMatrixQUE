module

public import BlockBand.Endpoints.Clock.ClockMixingEnergyUniform

/-!
# `b`-uniform deterministic constants of the energy-uniform chains

The energy-uniform chains (`OpenInputsEnergyUniform*`, `ClockMixingEnergyUniform`) fix `b`
before their deterministic scalars `etaLow b κ`, `gapLow b κ`, `kHigh b κ`, `thetaMax b κ`,
`kappaBulk b κ`, `dStar b`. Here `b` ranges over the compact set `Icc β (1/2-β)` (`0 < β`; the
set is empty unless `β ≤ 1/4`) and `0 < κ ≤ 1`. Each scalar is bounded by an explicit function of
`(β, κ)`, factor by factor (none of them is assumed monotone in `b`):
* `etaLowB β κ = (1/2+β) y_κ ≤ (1-b) y_κ = etaLow b κ`, from `1-b ≥ 1/2+β`;
* `kHigh b κ ≤ (1-b)² - (1-2b)b²κ ≤ (1-β)²` (`kHigh_le_sub`, `kHigh_le_B`);
* `gapLow b κ ≥ (1-2b)b²κ ≥ gapLowB β κ = 2β³κ` (`gapLow_ge`, `gapLowB_le`): the factor
  `1-2b ≥ 2β` and the factor `b² ≥ β²` are bounded separately (`(1-2b)b²` is not monotone);
* `thetaMax b κ = b/(b + g) ≤ (1/2-β)/((1/2-β) + gapLowB β κ) = thetaMaxB β κ < 1`;
* `kappaBulk b κ ≥ kappaBulkB β κ = min β (4-(2-κ)²) > 0`, and `zeParam (kappaBulkB β κ) b E`
  for every `b ∈ Icc β (1/2-β)`, `E ∈ bulkInterval κ` (`zeParam_bulkB`);
* `1 ≤ dStar b ≤ dStarB β = 1/(1/2+β) ≤ 2`;
* `iotaC b E ≥ etaLowB β κ / 2`, and the deterministic jet and injection bounds `fBound_le`,
  `jetBound_le` of the chains, at `etaLowB`.

The stability constant `CavityMean.stabConst b c η M a_*` of `cavity_stability` is bounded by
`stabConstB β c₀ η M a_*` for `β ≤ b ≤ 1`, `c₀ ≤ c ≤ 1` (`stabConst_le_B`), each factor
separately; hence one constant serves all such `(b, c)` (`cavity_stability_unifB`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix.Norms.L2Operator

namespace MovingEnergy

open OpenInputsProof CavityMeanProb ZeroEntranceProb CavityMean

variable {β κ b E : ℝ}

/-!
## The scalars of the energy-uniform chains
-/

/-- `η_β = (1/2+β) y_κ`, a lower bound of `etaLow b κ` on `b ∈ Icc β (1/2-β)`. -/
def etaLowB (β κ : ℝ) : ℝ := (1 / 2 + β) * yLow κ

/-- `g_β = 2β³κ`, a lower bound of `gapLow b κ` on `b ∈ Icc β (1/2-β)`, `κ ≤ 1`. -/
def gapLowB (β κ : ℝ) : ℝ := 2 * β ^ 3 * κ

/-- `θ_β = (1/2-β)/((1/2-β) + g_β)`, an upper bound of `thetaMax b κ`. -/
def thetaMaxB (β κ : ℝ) : ℝ := (1 / 2 - β) / ((1 / 2 - β) + gapLowB β κ)

/-- `κ'_β = min(β, 4-(2-κ)²)`, a lower bound of `kappaBulk b κ`. -/
def kappaBulkB (β κ : ℝ) : ℝ := min β (4 - (2 - κ) ^ 2)

/-- `r_β = (1-β)²`, an upper bound of `kHigh b κ`. -/
def kHighB (β : ℝ) : ℝ := (1 - β) ^ 2

/-- `d_β = 1/(1/2+β)`, an upper bound of `dStar b = 1/(1-b)`. -/
def dStarB (β : ℝ) : ℝ := 1 / (1 / 2 + β)

/-- Elementary facts on `b ∈ Icc β (1/2-β)`. -/
theorem mem_IccB_facts (hβ : 0 < β) (hb : b ∈ Set.Icc β (1 / 2 - β)) :
    0 < b ∧ b < 1 / 2 ∧ β ≤ b ∧ b ≤ 1 / 2 - β ∧ 2 * β ≤ 1 - 2 * b ∧ 1 / 2 + β ≤ 1 - b ∧
      β ≤ 1 / 4 := by
  obtain ⟨h1, h2⟩ := hb
  exact ⟨by linarith, by linarith, h1, h2, by linarith, by linarith, by linarith⟩

theorem etaLowB_pos (hβ : 0 < β) (hκ : 0 < κ) (hκ4 : κ < 4) : 0 < etaLowB β κ := by
  unfold etaLowB; have := yLow_pos hκ hκ4; positivity

theorem etaLowB_le (hβ : 0 < β) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : b ∈ Set.Icc β (1 / 2 - β)) :
    etaLowB β κ ≤ etaLow b κ := by
  obtain ⟨-, -, -, -, -, h, -⟩ := mem_IccB_facts hβ hb
  unfold etaLowB etaLow
  exact mul_le_mul_of_nonneg_right h (yLow_pos hκ hκ4).le

theorem etaLowB_le_yLow (hβ4 : β ≤ 1 / 4) (hκ : 0 < κ) (hκ4 : κ < 4) :
    etaLowB β κ ≤ yLow κ := by
  have := yLow_pos hκ hκ4
  unfold etaLowB; nlinarith

theorem etaLowB_le_im (hβ : 0 < β) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : b ∈ Set.Icc β (1 / 2 - β))
    (hE : E ∈ bulkInterval κ) : etaLowB β κ ≤ (boundaryZ b E).im :=
  (etaLowB_le hβ hκ hκ4 hb).trans (etaLow_le_im (mem_IccB_facts hβ hb).2.1 hκ hE)

theorem dStar_le_B (hβ : 0 < β) (hb : b ∈ Set.Icc β (1 / 2 - β)) :
    1 ≤ dStar b ∧ dStar b ≤ dStarB β ∧ dStarB β ≤ 2 := by
  obtain ⟨hb0, -, -, -, -, h, -⟩ := mem_IccB_facts hβ hb
  have h1b : 0 < 1 - b := by linarith
  refine ⟨?_, one_div_le_one_div_of_le (by positivity) h, ?_⟩
  · unfold dStar; rw [le_div_iff₀ h1b]; linarith
  · unfold dStarB; rw [div_le_iff₀ (by positivity)]; linarith

/-- `kHigh b κ ≤ (1-b)² - (1-2b)b²κ` for `0 ≤ b ≤ 1/2`, `0 ≤ κ ≤ 1`. -/
theorem kHigh_le_sub (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    kHigh b κ ≤ (1 - b) ^ 2 - (1 - 2 * b) * b ^ 2 * κ := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have ht0 : 0 ≤ (1 - 2 * b) * b ^ 2 * κ := by positivity
  have hcκ : (1 - 2 * b) * κ ≤ 1 := by
    have := mul_le_mul (by linarith : 1 - 2 * b ≤ 1) hκ1 hκ0 zero_le_one
    linarith
  have htb : (1 - 2 * b) * b ^ 2 * κ ≤ b ^ 2 := by
    have := mul_le_mul_of_nonneg_left hcκ (sq_nonneg b)
    calc (1 - 2 * b) * b ^ 2 * κ = b ^ 2 * ((1 - 2 * b) * κ) := by ring
      _ ≤ b ^ 2 * 1 := this
      _ = b ^ 2 := mul_one _
  have hbb : b ^ 2 ≤ (1 - b) ^ 2 := pow_le_pow_left₀ hb0 (by linarith) 2
  have hR0 : 0 ≤ (1 - b) ^ 2 - (1 - 2 * b) * b ^ 2 * κ := by linarith
  have h1 : 0 ≤ 1 - (1 - b) ^ 2 := by nlinarith
  unfold kHigh
  calc Real.sqrt ((1 - b) ^ 4 - 2 * (1 - 2 * b) * b ^ 2 * κ)
      ≤ Real.sqrt (((1 - b) ^ 2 - (1 - 2 * b) * b ^ 2 * κ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have e : ((1 - b) ^ 2 - (1 - 2 * b) * b ^ 2 * κ) ^ 2 -
            ((1 - b) ^ 4 - 2 * (1 - 2 * b) * b ^ 2 * κ) =
            2 * ((1 - 2 * b) * b ^ 2 * κ) * (1 - (1 - b) ^ 2) +
              ((1 - 2 * b) * b ^ 2 * κ) ^ 2 := by ring
        have : 0 ≤ 2 * ((1 - 2 * b) * b ^ 2 * κ) * (1 - (1 - b) ^ 2) +
            ((1 - 2 * b) * b ^ 2 * κ) ^ 2 := by positivity
        linarith
    _ = (1 - b) ^ 2 - (1 - 2 * b) * b ^ 2 * κ := Real.sqrt_sq hR0

/-- `kHigh b κ ≤ (1-β)² ≤ 1` on `b ∈ Icc β (1/2-β)`, `0 ≤ κ ≤ 1`. -/
theorem kHigh_le_B (hβ : 0 < β) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hb : b ∈ Set.Icc β (1 / 2 - β)) :
    kHigh b κ ≤ kHighB β ∧ kHighB β ≤ 1 := by
  obtain ⟨hb0, hb1, hβb, -, -, -, hβ4⟩ := mem_IccB_facts hβ hb
  have h := kHigh_le_sub hb0.le hb1.le hκ0 hκ1
  have ht0 : 0 ≤ (1 - 2 * b) * b ^ 2 * κ := by
    have : 0 ≤ 1 - 2 * b := by linarith
    positivity
  have h2 : (1 - b) ^ 2 ≤ (1 - β) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  refine ⟨by unfold kHighB; linarith, ?_⟩
  unfold kHighB; nlinarith

/-- `gapLow b κ ≥ (1-2b)b²κ` for `0 < b < 1/2`, `0 ≤ κ ≤ 1`. -/
theorem gapLow_ge (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    (1 - 2 * b) * b ^ 2 * κ ≤ gapLow b κ := by
  have h1b : 0 < 1 - b := by linarith
  have hk := kHigh_le_sub hb0.le hb1.le hκ0 hκ1
  have ht0 : 0 ≤ (1 - 2 * b) * b ^ 2 * κ := by
    have : 0 ≤ 1 - 2 * b := by linarith
    positivity
  have h1 : kHigh b κ * dStar b ≤ ((1 - b) ^ 2 - (1 - 2 * b) * b ^ 2 * κ) / (1 - b) := by
    unfold dStar; rw [mul_one_div]; exact div_le_div_of_nonneg_right hk h1b.le
  have e : ((1 - b) ^ 2 - (1 - 2 * b) * b ^ 2 * κ) / (1 - b) =
      (1 - b) - (1 - 2 * b) * b ^ 2 * κ / (1 - b) := by
    rw [sub_div, pow_two, mul_div_assoc, div_self h1b.ne', mul_one]
  have h2 : (1 - 2 * b) * b ^ 2 * κ ≤ (1 - 2 * b) * b ^ 2 * κ / (1 - b) := by
    rw [le_div_iff₀ h1b]
    have := mul_le_mul_of_nonneg_left (by linarith : 1 - b ≤ 1) ht0
    linarith
  unfold gapLow
  linarith

theorem gapLowB_pos (hβ : 0 < β) (hκ : 0 < κ) : 0 < gapLowB β κ := by
  unfold gapLowB; positivity

/-- `gapLowB β κ ≤ gapLow b κ` on `b ∈ Icc β (1/2-β)`, `0 < κ ≤ 1`: the factors `1-2b ≥ 2β`
and `b² ≥ β²` are bounded separately. -/
theorem gapLowB_le (hβ : 0 < β) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hb : b ∈ Set.Icc β (1 / 2 - β)) :
    gapLowB β κ ≤ gapLow b κ := by
  obtain ⟨hb0, hb1, hβb, -, hc, -, -⟩ := mem_IccB_facts hβ hb
  refine le_trans ?_ (gapLow_ge hb0 hb1 hκ.le hκ1)
  have h2 : β ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hβ.le hβb 2
  have h3 : (2 * β) * β ^ 2 ≤ (1 - 2 * b) * b ^ 2 :=
    mul_le_mul hc h2 (by positivity) (by linarith)
  have h4 := mul_le_mul_of_nonneg_right h3 hκ.le
  unfold gapLowB
  calc 2 * β ^ 3 * κ = (2 * β) * β ^ 2 * κ := by ring
    _ ≤ _ := h4

/-- `gapLowB β κ ≤ gapC b E` on `b ∈ Icc β (1/2-β)`, `E ∈ bulkInterval κ`. -/
theorem gapLowB_le_gapC (hβ : 0 < β) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hb : b ∈ Set.Icc β (1 / 2 - β))
    (hE : E ∈ bulkInterval κ) : gapLowB β κ ≤ gapC b E := by
  obtain ⟨hb0, hb1, -⟩ := mem_IccB_facts hβ hb
  exact (gapLowB_le hβ hκ hκ1 hb).trans (gapLow_le_gapC hb0 hb1 hκ hE)

/-- `‖kMinus b E‖ ≤ 1` on `b ∈ Icc β (1/2-β)`, `E ∈ bulkInterval κ`, `0 < κ ≤ 1`. -/
theorem norm_kMinus_le_one (hβ : 0 < β) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hb : b ∈ Set.Icc β (1 / 2 - β)) (hE : E ∈ bulkInterval κ) : ‖kMinus b E‖ ≤ 1 := by
  obtain ⟨-, hb1, -⟩ := mem_IccB_facts hβ hb
  obtain ⟨h1, h2⟩ := kHigh_le_B hβ hκ.le hκ1 hb
  exact (norm_kMinus_le_kHigh hb1 hκ hE).trans (h1.trans h2)

theorem thetaMaxB_nonneg (hβ : 0 < β) (hβ4 : β ≤ 1 / 4) (hκ : 0 < κ) : 0 ≤ thetaMaxB β κ := by
  have := gapLowB_pos hβ hκ
  have : 0 ≤ 1 / 2 - β := by linarith
  unfold thetaMaxB; positivity

theorem thetaMaxB_lt_one (hβ : 0 < β) (hβ4 : β ≤ 1 / 4) (hκ : 0 < κ) : thetaMaxB β κ < 1 := by
  have := gapLowB_pos hβ hκ
  unfold thetaMaxB
  rw [div_lt_one (by linarith)]
  linarith

/-- `thetaMax b κ ≤ thetaMaxB β κ` on `b ∈ Icc β (1/2-β)`, `0 < κ ≤ 1`: `b ≤ 1/2-β` and
`gapLow b κ ≥ gapLowB β κ` are used separately. -/
theorem thetaMax_le_B (hβ : 0 < β) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hb : b ∈ Set.Icc β (1 / 2 - β)) :
    thetaMax b κ ≤ thetaMaxB β κ := by
  obtain ⟨hb0, hb1, -, hbu, -, -, -⟩ := mem_IccB_facts hβ hb
  have hg := gapLowB_le hβ hκ hκ1 hb
  have hg0 := gapLowB_pos hβ hκ
  unfold thetaMax thetaMaxB
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : b * gapLowB β κ ≤ (1 / 2 - β) * gapLow b κ :=
    mul_le_mul hbu hg hg0.le (by linarith)
  nlinarith

/-- `‖θ_*(E, s)‖ ≤ thetaMaxB β κ`, uniformly in `b ∈ Icc β (1/2-β)`, `E ∈ bulkInterval κ` and
the stationary jet `s`. -/
theorem norm_thetaStar_le_thetaMaxB (hβ : 0 < β) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hb : b ∈ Set.Icc β (1 / 2 - β)) (hE : E ∈ bulkInterval κ) {s : ℂ}
    (hs : IsStationaryJet b E s) : ‖thetaStar b E s‖ ≤ thetaMaxB β κ := by
  obtain ⟨hb0, hb1, -⟩ := mem_IccB_facts hβ hb
  exact (norm_thetaStar_le_thetaMax hb0 hb1 hκ hE hs).trans (thetaMax_le_B hβ hκ hκ1 hb)

theorem kappaBulkB_pos (hβ : 0 < β) (hκ : 0 < κ) (hκ4 : κ < 4) : 0 < kappaBulkB β κ :=
  lt_min hβ (BlockBand.Layers.four_sub_sq_pos hκ hκ4)

theorem kappaBulkB_le (hβ : 0 < β) (hb : b ∈ Set.Icc β (1 / 2 - β)) :
    kappaBulkB β κ ≤ kappaBulk b κ := by
  obtain ⟨-, -, hβb, -, hc, -, -⟩ := mem_IccB_facts hβ hb
  exact min_le_min (le_min hβb (by linarith)) le_rfl

/-- The compact zero-entrance parameter `kappaBulkB β κ` covers every
`b ∈ Icc β (1/2-β)` and every `E ∈ bulkInterval κ`. -/
theorem zeParam_bulkB (hβ : 0 < β) (hκ : 0 < κ) (hκ4 : κ < 4) :
    0 < kappaBulkB β κ ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ E ∈ bulkInterval κ,
      zeParam (kappaBulkB β κ) b E := by
  refine ⟨kappaBulkB_pos hβ hκ hκ4, fun b hb E hE => ?_⟩
  obtain ⟨hb0, hb1, -⟩ := mem_IccB_facts hβ hb
  obtain ⟨h1, h2, h3⟩ := (zeParam_bulk hb0 hb1 hκ hκ4).2 E hE
  have h := kappaBulkB_le (κ := κ) hβ hb
  exact ⟨h.trans h1, h.trans h2, h.trans h3⟩

/-- `ι₀ = (1-b) y / 2 ≥ etaLowB β κ / 2` on `b ∈ Icc β (1/2-β)`, `E ∈ bulkInterval κ`. -/
theorem iotaC_ge_B (hβ : 0 < β) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : b ∈ Set.Icc β (1 / 2 - β))
    (hE : E ∈ bulkInterval κ) : etaLowB β κ / 2 ≤ iotaC b E := by
  obtain ⟨-, -, -, -, -, h, -⟩ := mem_IccB_facts hβ hb
  have hy := yLow_le_yA hE
  have hy0 := yLow_pos hκ hκ4
  unfold etaLowB iotaC
  have : (1 / 2 + β) * yLow κ ≤ (1 - b) * yA E :=
    mul_le_mul h hy hy0.le (by linarith)
  linarith

/-- The deterministic bound of `f` in the clock-mixing lemma, uniformly in `b`:
`(Im z)⁻¹ + |c₀| ≤ 2/etaLowB β κ`. -/
theorem fBound_le_B (hβ : 0 < β) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : b ∈ Set.Icc β (1 / 2 - β))
    (hE : E ∈ bulkInterval κ) :
    (boundaryZ b E).im⁻¹ + ‖cZero b E‖ ≤ 2 / etaLowB β κ := by
  obtain ⟨-, hb1, -⟩ := mem_IccB_facts hβ hb
  refine (fBound_le hb1 hκ hκ4 hE).trans ?_
  exact div_le_div_of_nonneg_left zero_le_two (etaLowB_pos hβ hκ hκ4) (etaLowB_le hβ hκ hκ4 hb)

/-- The entrance bound `1/Im z + 1 ≤ 1/etaLowB β κ + 1` of `clock_moment_unif`. -/
theorem entranceBound_le_B (hβ : 0 < β) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : b ∈ Set.Icc β (1 / 2 - β)) (hE : E ∈ bulkInterval κ) :
    1 / (boundaryZ b E).im + 1 ≤ 1 / etaLowB β κ + 1 := by
  have := one_div_le_one_div_of_le (etaLowB_pos hβ hκ hκ4) (etaLowB_le_im hβ hκ hκ4 hb hE)
  linarith

/-- The deterministic jet bound `B(E)` of `openInputsMomentsEnergyUniform_core`, uniformly in `b`:
`1/Im z + 1 + λ(1/(Im z)² + d_*) ≤ 1/η_β + 1 + λ(1/η_β² + d_β)`. -/
theorem jetBound_le_B (hβ : 0 < β) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : b ∈ Set.Icc β (1 / 2 - β))
    (hE : E ∈ bulkInterval κ) {lam : ℝ} (hlam : 0 ≤ lam) :
    1 / (boundaryZ b E).im + 1 + lam * (1 / (boundaryZ b E).im ^ 2 + dStar b) ≤
      1 / etaLowB β κ + 1 + lam * (1 / etaLowB β κ ^ 2 + dStarB β) := by
  have h1 := jetBound_le (d := dStar b) (etaLowB_pos hβ hκ hκ4) (etaLowB_le_im hβ hκ hκ4 hb hE)
    hlam
  have h2 := mul_le_mul_of_nonneg_left (dStar_le_B hβ hb).2.1 hlam
  nlinarith

/-!
## The stability constant of `cavity_stability`, uniformly in `(b, c)`
-/

/-- `S_β = β η a²`. -/
def stabSB (β η a : ℝ) : ℝ := β * η * a ^ 2
/-- `V_β = S_β⁻¹ + 1`. -/
def stabVB (β η a : ℝ) : ℝ := 1 / stabSB β η a + 1
/-- `P_η = 1 + η⁻²`. -/
def stabPB (η : ℝ) : ℝ := 1 + (1 / η) ^ 2
/-- `β₀,β = β η (M + V_β)⁻²`. -/
def stabBetaB (β η M a : ℝ) : ℝ := β * η / (M + stabVB β η a) ^ 2
/-- `D_β = 1 + S_β⁻²`. -/
def stabDB (β η a : ℝ) : ℝ := 1 + 1 / stabSB β η a ^ 2
/-- `γ₂,β = β₀,β / (2 (P_η V_β + β₀,β))`. -/
def stabGammaB (β η M a : ℝ) : ℝ :=
  stabBetaB β η M a / (2 * (stabPB η * stabVB β η a + stabBetaB β η M a))
/-- `ε₀,β = min(1, β₀,β/(2 P_η D_β))`. -/
def stabEpsB (β η M a : ℝ) : ℝ := min 1 (stabBetaB β η M a / (2 * stabPB η * stabDB β η a))
/-- `δ_β = β η (M + c₀^{-1/2})⁻² / (1 + η⁻¹)`, a lower bound of `cavityGapConst b c η M`. -/
def gapConstB (β c₀ η M : ℝ) : ℝ :=
  β * η / ((M + 1 / Real.sqrt c₀) ^ 2 * (1 + 1 / η))
/-- `C₁,β = (1 + S_β⁻¹ c₀^{-1/2}) / min(δ_β, γ₂,β)`. -/
def stabC1B (β c₀ η M a : ℝ) : ℝ :=
  (1 + 1 / stabSB β η a * (1 / Real.sqrt c₀)) / min (gapConstB β c₀ η M) (stabGammaB β η M a)
/-- `B_β = S_β⁻¹ + c₀^{-1/2} + 2/η`. -/
def stabBB (β c₀ η a : ℝ) : ℝ := 1 / stabSB β η a + 1 / Real.sqrt c₀ + 2 / η
/-- The uniform stability constant. -/
def stabConstB (β c₀ η M a : ℝ) : ℝ :=
  (stabC1B β c₀ η M a * (1 + (1 / η) ^ 2) + 1) + (1 + stabBB β c₀ η a / stabEpsB β η M a)

section StabB

variable {c₀ c η M a : ℝ}

theorem stabB_pos (hβ : 0 < β) (hc₀ : 0 < c₀) (hη : 0 < η) (hM : 0 ≤ M) (ha : 0 < a) :
    0 < stabSB β η a ∧ 0 < stabVB β η a ∧ 0 < stabPB η ∧ 0 < stabBetaB β η M a ∧
      0 < stabDB β η a ∧ 0 < stabGammaB β η M a ∧ 0 < stabEpsB β η M a ∧
      0 < gapConstB β c₀ η M ∧ 0 < stabC1B β c₀ η M a ∧ 0 < stabBB β c₀ η a ∧
      0 < stabConstB β c₀ η M a := by
  have hsc := Real.sqrt_pos.mpr hc₀
  have hS : 0 < stabSB β η a := by unfold stabSB; positivity
  have hV : 0 < stabVB β η a := by unfold stabVB; positivity
  have hP : 0 < stabPB η := by unfold stabPB; positivity
  have hβ₀ : 0 < stabBetaB β η M a := by unfold stabBetaB; positivity
  have hD : 0 < stabDB β η a := by unfold stabDB; positivity
  have hγ : 0 < stabGammaB β η M a := by unfold stabGammaB; positivity
  have hε : 0 < stabEpsB β η M a := lt_min one_pos (by positivity)
  have hδ : 0 < gapConstB β c₀ η M := by unfold gapConstB; positivity
  have hC : 0 < stabC1B β c₀ η M a := by
    unfold stabC1B; have := lt_min hδ hγ; positivity
  have hB : 0 < stabBB β c₀ η a := by unfold stabBB; positivity
  refine ⟨hS, hV, hP, hβ₀, hD, hγ, hε, hδ, hC, hB, ?_⟩
  unfold stabConstB; positivity

/-- **The stability constant is bounded uniformly** for `β ≤ b ≤ 1`, `c₀ ≤ c ≤ 1`:
`stabConst b c η M a ≤ stabConstB β c₀ η M a`, factor by factor. -/
theorem stabConst_le_B (hβ : 0 < β) (hc₀ : 0 < c₀) (hη : 0 < η) (hM : 0 ≤ M) (ha : 0 < a)
    (hβb : β ≤ b) (hb1 : b ≤ 1) (hc₀c : c₀ ≤ c) (hc1 : c ≤ 1) :
    stabConst b c η M a ≤ stabConstB β c₀ η M a := by
  have hb : 0 < b := hβ.trans_le hβb
  have hc : 0 < c := hc₀.trans_le hc₀c
  obtain ⟨hS, hV, hP, hβ₀, hD, hγ, hε, -, -, -⟩ := stab_pos hb hc hη hM ha
  obtain ⟨hSB, hVB, hPB, hβ₀B, hDB, hγB, hεB, hδB, hC1B, hBB, -⟩ :=
    stabB_pos (c₀ := c₀) hβ hc₀ hη hM ha
  have hδ := cavityGapConst_pos hb hc hη hM
  have hsc := Real.sqrt_pos.mpr hc
  have hsc₀ := Real.sqrt_pos.mpr hc₀
  -- the elementary factors
  have hSle : stabSB β η a ≤ stabS b η a := by
    unfold stabSB stabS
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβb hη.le) (sq_nonneg a)
  have hiS : 1 / stabS b η a ≤ 1 / stabSB β η a := one_div_le_one_div_of_le hSB hSle
  have hiS2 : 1 / stabS b η a ^ 2 ≤ 1 / stabSB β η a ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hSB.le hSle 2)
  have hVle : stabV b η a ≤ stabVB β η a := by unfold stabV stabVB; linarith
  have hbV : b * stabV b η a ≤ stabVB β η a := by
    have := mul_le_mul_of_nonneg_right hb1 hV.le
    linarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hPle : stabP b c η ≤ stabPB η := by
    unfold stabP stabPB
    have := mul_le_mul_of_nonneg_right hb2 (sq_nonneg (1 / η))
    linarith
  have hisc : 1 / Real.sqrt c ≤ 1 / Real.sqrt c₀ :=
    one_div_le_one_div_of_le hsc₀ (Real.sqrt_le_sqrt hc₀c)
  have hbsc : b / Real.sqrt c ≤ 1 / Real.sqrt c₀ :=
    (div_le_div_of_nonneg_right hb1 hsc.le).trans hisc
  have hsc1 : Real.sqrt c ≤ 1 := Real.sqrt_le_one.mpr hc1
  have hbη : b / η ≤ 1 / η := div_le_div_of_nonneg_right hb1 hη.le
  -- `β₀`, `D`, `γ₂`, `ε₀`, `δ`
  have hβ₀le : stabBetaB β η M a ≤ stabBeta b η M a := by
    unfold stabBetaB stabBeta
    refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hβb hη.le) (by positivity) ?_
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hDle : stabD b η a ≤ stabDB β η a := by
    unfold stabD stabDB
    have := mul_le_mul_of_nonneg_right hb1 (by positivity : (0 : ℝ) ≤ 1 / stabS b η a ^ 2)
    linarith
  have hPV : stabP b c η * stabV b η a ≤ stabPB η * stabVB β η a :=
    mul_le_mul hPle hVle hV.le hPB.le
  have hγle : stabGammaB β η M a ≤ stabGamma b c η M a := by
    unfold stabGammaB stabGamma
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul hβ₀le hPV (by positivity) hβ₀.le
    nlinarith
  have hεle : stabEpsB β η M a ≤ stabEps b c η M a := by
    unfold stabEpsB stabEps
    refine min_le_min le_rfl (div_le_div₀ hβ₀.le hβ₀le (by positivity) ?_)
    have := mul_le_mul hPle hDle hD.le hPB.le
    nlinarith
  have hδle : gapConstB β c₀ η M ≤ cavityGapConst b c η M := by
    unfold gapConstB cavityGapConst
    refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hβb hη.le) (by positivity) ?_
    refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by linarith)
      (by positivity) (by positivity)
  -- `C₁`, `B`, and the final constant
  have hC1le : stabC1 b c η M a ≤ stabC1B β c₀ η M a := by
    unfold stabC1 stabC1B
    refine div_le_div₀ (by positivity) ?_ (lt_min hδB hγB) (min_le_min hδle hγle)
    have h1 : b * (1 / stabS b η a) ≤ 1 / stabSB β η a := by
      have := mul_le_mul_of_nonneg_right hb1 (by positivity : (0 : ℝ) ≤ 1 / stabS b η a)
      linarith
    have := mul_le_mul h1 hisc (by positivity) (by positivity)
    linarith
  have hBle : stabB b c η a ≤ stabBB β c₀ η a := by
    unfold stabB stabBB; linarith
  have hC1 : 0 ≤ stabC1 b c η M a := (stab_pos hb hc hη hM ha).2.2.2.2.2.2.2.1.le
  have hB : 0 ≤ stabB b c η a := (stab_pos hb hc hη hM ha).2.2.2.2.2.2.2.2.1.le
  unfold stabConst stabConstB
  have h1 : stabC1 b c η M a * (1 + b * (1 / η) ^ 2) ≤
      stabC1B β c₀ η M a * (1 + (1 / η) ^ 2) := by
    refine mul_le_mul hC1le ?_ (by positivity) hC1B.le
    have := mul_le_mul_of_nonneg_right hb1 (sq_nonneg (1 / η))
    linarith
  have h2 : stabB b c η a / stabEps b c η M a ≤ stabBB β c₀ η a / stabEpsB β η M a :=
    div_le_div₀ hBB.le hBle hεB hεle
  linarith

/-- **`cavity_stability` with one constant for all `β ≤ b ≤ 1`, `c₀ ≤ c ≤ 1`** (the deterministic
part of the cavity-mean lemma, made uniform in the compact parameter set; `η, M, a_*` fixed). -/
theorem cavity_stability_unifB {β c₀ η M astar : ℝ} (hβ : 0 < β) (hc₀ : 0 < c₀) (hη : 0 < η)
    (hM : 0 ≤ M) (ha : 0 < astar) :
    ∃ C : ℝ, 0 < C ∧ ∀ b c : ℝ, β ≤ b → b ≤ 1 → c₀ ≤ c → c ≤ 1 →
      ∀ (ι : Type) [Fintype ι] (p x : ι → ℝ) (e : ℝ) (z' v u vbar ubar : ℂ) (ε : ℝ),
      IsCavityWeights p → η ≤ z'.im → ‖z'‖ ≤ M →
      IsCavitySolution p x b c e z' v u → vbar.im ≤ 0 → astar ≤ ‖ubar‖ →
      η * ‖ubar‖ ^ 2 ≤ -ubar.im →
      ‖vbar - cavityStieltjes p x (-e - c * vbar - b * ubar)‖ ≤ ε →
      ‖ubar - (z' - b * vbar)⁻¹‖ ≤ ε →
      ‖vbar - v‖ + ‖ubar - u‖ ≤ C * ε := by
  refine ⟨stabConstB β c₀ η M astar, (stabB_pos hβ hc₀ hη hM ha).2.2.2.2.2.2.2.2.2.2, ?_⟩
  intro b c hβb hb1 hc₀c hc1 ι _ p x e z' v u vbar ubar ε hp hz hM' hsol hvb hua hport h1 h2
  have hb : 0 < b := hβ.trans_le hβb
  have hc : 0 < c := hc₀.trans_le hc₀c
  refine (cavity_stability_of hp hb hc hη ha hz hM' hsol hvb hua hport h1 h2).trans ?_
  exact mul_le_mul_of_nonneg_right (stabConst_le_B hβ hc₀ hη hM ha hβb hb1 hc₀c hc1)
    ((norm_nonneg _).trans h1)

end StabB

end MovingEnergy

end BlockBand.Endpoints.Clock
