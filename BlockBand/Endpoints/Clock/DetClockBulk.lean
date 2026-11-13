module

public import BlockBand.Endpoints.Clock.DetClockEpsUniform
public import BlockBand.Endpoints.Clock.DetClockBulkStep
public import BlockBand.Endpoints.Clock.DetClockBulkMixing
public import BlockBand.Endpoints.Clock.MovingEnergyLabels

/-!
# The deterministic-clock lemma on compact parameter sets

We prove `MovingEnergy.DetClockEvolutionDBulk` (`detClockEvolutionDBulk_of`): `β, κ, T, q` first;
then `ε > 0`; for each `b ∈ [β, 1/2-β]` and `K ≥ 1` a sequence `δ_{W,j}` bounding `|r^D_{W,j}(a)|`
for every `E ∈ bulkInterval κ`, every Hermitian `‖D‖ ≤ ε`, `j₀ ≤ j ≤ TW`, `a ∈ [K⁻¹, K]`, with
`Σ_{j=j₀}^{⌊TW⌋} δ_{W,j} → 0`.

## The radius `ε` (uniform in `b`)
`ε = min ε₉ ε₁₈`, with `ε₉`, `ε₁₈` the radii of `OpenInputsMomentsBulk` at moment orders `9` and
`18 = 2·9` (they depend only on `β, κ, T, q`). The deterministic clock uses the input moments
`OpenInputsMomentsBulk` at order `9` and clock mixing at order `9`. Clock mixing uses the input
moments at order `2·9`, and its radius is their radius (`DetClockBulk.clockMixing_core`, which
takes those bounds at radius `ε₁₈` as an explicit hypothesis). So one `ε` serves every `b ∈ [β, 1/2-β]`.

## The majorants `δ` (uniform in `E` and `D`)
`DetClockBulk.detClockBulk_core` follows the proof of `detClockStep_core` with:
* the one-step bound from `DetClockBulk.stepDefect_le_unif`, whose `C_s, W_s` depend only on
  `(b, κ, K, K_q)` and which holds for every `E ∈ bulkInterval κ` and every stationary jet;
* the input-moment and clock-mixing bounds (at order `9`) with constants uniform in `E`;
* the stationary jet at each `E` from `PassiveSourceMixingContract.oneStepMean` (jet-existence
  conjunct only);
* for `W < W₀` the trivial bound `2 + D₀ W + d_* K_q K`, with `D₀ = transportD0 b E` replaced by
  `D₀^max = 2/(bκ'(4-κ'))`, `κ' = min κ 1` (`transportD0_le_bulk`).
`transportD0 b E` itself appears in the remainder `detClockRemainderD` at the energy `E`; the
proof handles it through the one-step identity `remainder_eq_integral` at that `E`, and its only
other appearances are the two bounds above.

## Hypotheses of `detClockEvolutionDBulk_of`
* `PassiveCovarianceEnergyUniformHyp`, used for the covariance identities;
* `TransmissionUniform3.PassiveSourceMixingEnergyUniformContract` (`oneStepMean`,
  `oneStepFluctuation`);
* `PassiveSourceMixingContract`: only the jet-existence conjunct of `oneStepMean`;
* `GaussianAbsorptionContract`, `LayersOnePort.OnePortWeightedCovarianceContract`;
* `OpenInputsMomentsBulk`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

namespace MovingEnergy

namespace DetClockBulk

open DetClockProof ClockMixingAlg ClockMixingProb
open BlockBand.Internal.Contracts.TransmissionUniform3

/-- **The deterministic-clock step on `bulkInterval κ₀`**: the proof of `detClockStep_core` with the
input-moment bounds (`C₁, W₁`) and the clock-mixing bounds (`C₂, W₂`) at moment order `9`, for Hermitian `‖D‖ ≤ ε`, uniform in `E ∈ bulkInterval κ₀`, as
explicit hypotheses; the one-step bound from `stepDefect_le_unif`. The majorants `δ` do not
depend on `E` or `D`. -/
theorem detClockBulk_core (hPSMU : PassiveSourceMixingEnergyUniformContract)
    (hPCU : PassiveCovarianceEnergyUniformHyp) (hPSM : PassiveSourceMixingContract)
    (hGA : GaussianAbsorptionContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract)
    {b κ₀ T ε C₁ C₂ : ℝ} {q : ℝ → ℝ} {W₁ W₂ : ℕ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hκ₀ : 0 < κ₀) (hq : IsClockWeight q)
    (hOI' : ∀ W : ℕ, W₁ ≤ W → ∀ E ∈ bulkInterval κ₀, ∀ D : Matrix (Fin W) (Fin W) ℂ,
      D.IsHermitian → ‖D‖ ≤ ε →
      (∀ s : ℂ, IsStationaryJet b E s → ∀ j : ℕ, openEntranceTime W ≤ j →
          (j : ℝ) ≤ T * W →
          eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal 9)
              (oneEndedLaw W b j) +
            eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal 9)
              (oneEndedLaw W b j) ≤ ENNReal.ofReal (C₁ / W)) ∧
      ∀ j : ℕ, (j : ℝ) ≤ T * W →
        eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) ≤
          ENNReal.ofReal (C₁ * ((j : ℝ) + 1) / W))
    (hCM : ∀ W : ℕ, W₂ ≤ W → ∀ E ∈ bulkInterval κ₀, ∀ D : Matrix (Fin W) (Fin W) ℂ,
      D.IsHermitian → ‖D‖ ≤ ε →
      ∀ j : ℕ, openEntranceTime W ≤ j → (j : ℝ) ≤ T * W →
        eLpNorm (openClockZ b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) +
            eLpNorm (openClockSqrtS b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) ≤
          ENNReal.ofReal (C₂ / Real.sqrt W)) :
    ∀ K : ℝ, 1 ≤ K → ∃ δ : ℕ → ℕ → ℝ,
      (∀ W j, ∀ E ∈ bulkInterval κ₀, ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian →
        ‖D‖ ≤ ε → openEntranceTime W ≤ j → (j : ℝ) ≤ T * W → ∀ a ∈ Icc K⁻¹ K,
          |detClockRemainderD W b E q D j a| ≤ δ W j) ∧
      Tendsto (fun W => ∑ j ∈ Finset.Icc (openEntranceTime W) ⌊T * W⌋₊, δ W j) atTop
        (𝓝 0) := by
  intro K hK
  obtain ⟨_hqc, hq0, Kq, hqK⟩ := hq
  have hKq : 0 ≤ Kq := (hq0 0).trans (hqK 0)
  have hK0 : 0 < K := by linarith
  obtain ⟨Cs, Ws, hCs0, hstep⟩ := stepDefect_le_unif hPSMU hPCU hGA hWC hb0 hb1 hκ₀ hK hKq
  set κ := min κ₀ 1 with hκdef
  have hκ : 0 < κ := lt_min hκ₀ one_pos
  have hκ1 : κ ≤ 1 := min_le_right _ _
  have hκ4 : κ < 4 := by linarith
  set D0m := transportD0Max b κ with hD0m
  have hD0m0 : 0 ≤ D0m := transportD0Max_nonneg hb0 hκ hκ4
  have hd := (dStar_pos (by linarith : b < 1)).le
  set C₁' := max C₁ 0 with hC₁'
  set C₂' := max C₂ 0 with hC₂'
  have hC₁0 : 0 ≤ C₁' := le_max_right _ _
  have hC₂0 : 0 ≤ C₂' := le_max_right _ _
  set B := (1 + C₁' * (|T| + 1) + C₁' + C₂') ^ 9 with hB
  have hB0 : 0 ≤ B := by positivity
  set W₀ := max (max Ws W₁) (max W₂ 1) with hW₀
  let δ : ℕ → ℕ → ℝ := fun W _ => if W₀ ≤ W then Cs * B * ((Real.sqrt W)⁻¹) ^ 3
    else 2 + D0m * W + dStar b * Kq * K
  refine ⟨δ, ?_, ?_⟩
  · intro W j E hE₀ D hD' hDε hj0 hjT a ha
    have hE : E ∈ bulkInterval κ := bulkInterval_mono (min_le_left κ₀ 1) hE₀
    obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hE
    have hD := (transportD0_pos hb0 hE0 hE1).le
    have hDle : transportD0 b E ≤ D0m := transportD0_le_bulk hb0 hκ (by linarith) hE
    obtain ⟨⟨s, hs⟩, -⟩ := hPSM.oneStepMean b hb0 hb1 E hE0 hE1
    have ha0 : 0 < a := lt_of_lt_of_le (inv_pos.mpr hK0) ha.1
    obtain ⟨hint, heq⟩ := remainder_eq_integral b E hq0 D j ha0
    rw [heq]
    have hqv : q (((j + 1 : ℕ) : ℝ) / W) ∈ Icc 0 Kq := ⟨hq0 _, hqK _⟩
    by_cases hW : W₀ ≤ W
    · simp only [δ, hW, ite_true]
      have hWs : Ws ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
      have hW1' : W₁ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
      have hW2' : W₂ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
      have hWpos : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
      have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
      have hW0 : (0 : ℝ) < W := by linarith
      obtain ⟨hjet, hgam⟩ := hOI' W hW1' E hE₀ D hD' hDε
      have hδ := hjet s hs j hj0 hjT
      have hγ := hgam j hjT
      have hZS := hCM W hW2' E hE₀ D hD' hDε j hj0 hjT
      have hγ' : eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) ≤
          ENNReal.ofReal (C₁' * (|T| + 1)) := by
        refine hγ.trans (ENNReal.ofReal_le_ofReal ?_)
        have ht := time_le hW1 hjT
        calc C₁ * ((j : ℝ) + 1) / W ≤ C₁' * (((j : ℝ) + 1) / W) := by
              rw [mul_div_assoc]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ C₁' * (|T| + 1) := mul_le_mul_of_nonneg_left ht hC₁0
      have hδ' : eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal 9)
            (oneEndedLaw W b j) +
          eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal 9)
            (oneEndedLaw W b j) ≤ ENNReal.ofReal (C₁' / W) :=
        hδ.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _)
          hW0.le))
      have hZS' : eLpNorm (openClockZ b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) +
          eLpNorm (openClockSqrtS b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) ≤
          ENNReal.ofReal (C₂' / Real.sqrt W) :=
        hZS.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _)
          (Real.sqrt_nonneg _)))
      obtain ⟨hΛi, hΛ⟩ := pastWeight_moment (s := s) hq0 hW0 (by positivity) hC₁0 hC₂0 hγ' hδ'
        hZS'
      have hae : ∀ᵐ ω ∂oneEndedLaw W b j,
          |stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
            (oneEndedQ b E q D j ω)| ≤
          Cs * pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω) ^ 9 *
            ((Real.sqrt W)⁻¹) ^ 3 := by
        filter_upwards [ae_blocks_isHermitian (W := W) b j] with ω hω
        exact hstep W hWs E hE₀ s hs (oneEndedX E D j ω) (X_isHermitian E hD' j ω hω)
          (oneEndedQ b E q D j ω) (Q_posSemidef b E hq0 D j ω) a ha _ hqv
      have hbi : Integrable (fun ω => Cs * pastWeight W b E s (oneEndedX E D j ω)
          (oneEndedQ b E q D j ω) ^ 9 * ((Real.sqrt W)⁻¹) ^ 3) (oneEndedLaw W b j) :=
        (hΛi.const_mul Cs).mul_const _
      calc |∫ ω, stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
            (oneEndedQ b E q D j ω) ∂oneEndedLaw W b j|
          ≤ ∫ ω, |stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
            (oneEndedQ b E q D j ω)| ∂oneEndedLaw W b j := abs_integral_le_integral_abs
        _ ≤ ∫ ω, Cs * pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω) ^ 9 *
            ((Real.sqrt W)⁻¹) ^ 3 ∂oneEndedLaw W b j := integral_mono_ae hint.abs hbi hae
        _ = Cs * (∫ ω, pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω) ^ 9
            ∂oneEndedLaw W b j) * ((Real.sqrt W)⁻¹) ^ 3 := by
          rw [integral_mul_const, integral_const_mul]
        _ ≤ Cs * B * ((Real.sqrt W)⁻¹) ^ 3 := by
          gcongr
    · simp only [δ, hW, ite_false]
      refine (abs_integral_le_integral_abs).trans ?_
      have hcst : ∀ ω, |stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
          (oneEndedQ b E q D j ω)| ≤ 2 + D0m * W + dStar b * Kq * K := fun ω => by
        have h0 := stepDefect_trivial (W := W) (b := b) (E := E) (X := oneEndedX E D j ω)
          (Q_posSemidef b E hq0 D j ω) ha0.le ha.2 hqv.1 hqv.2 hD hd
        have h1 := mul_le_mul_of_nonneg_right hDle (Nat.cast_nonneg (α := ℝ) W)
        linarith
      calc ∫ ω, |stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
            (oneEndedQ b E q D j ω)| ∂oneEndedLaw W b j
          ≤ ∫ _ω, (2 + D0m * W + dStar b * Kq * K) ∂oneEndedLaw W b j :=
            integral_mono hint.abs (integrable_const _) hcst
        _ = 2 + D0m * W + dStar b * Kq * K := by simp
  · -- the sum tends to zero
    have hsq : Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hlim : Tendsto (fun W : ℕ => (|T| + 1) * (Cs * B) * (Real.sqrt W)⁻¹) atTop (𝓝 0) := by
      have := hsq.const_mul ((|T| + 1) * (Cs * B))
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun W => ?_) ?_ hlim
    · refine Finset.sum_nonneg fun j _ => ?_
      simp only [δ]
      split_ifs
      · positivity
      · have : (0 : ℝ) ≤ W := Nat.cast_nonneg W
        positivity
    · filter_upwards [eventually_ge_atTop W₀] with W hW
      have hWpos : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
      have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
      have hW0 : (0 : ℝ) < W := by linarith
      have hsW0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
      have hδW : ∀ j, δ W j = Cs * B * ((Real.sqrt W)⁻¹) ^ 3 := fun j => by
        simp only [δ, hW, ite_true]
      rw [Finset.sum_congr rfl (fun j _ => hδW j), Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Icc (openEntranceTime W) ⌊T * W⌋₊).card : ℝ) ≤ (|T| + 1) * W := by
        rw [Nat.card_Icc]
        have h1 : ((⌊T * W⌋₊ + 1 - openEntranceTime W : ℕ) : ℝ) ≤ (⌊T * W⌋₊ : ℝ) + 1 := by
          have : ⌊T * W⌋₊ + 1 - openEntranceTime W ≤ ⌊T * W⌋₊ + 1 := Nat.sub_le _ _
          exact_mod_cast this
        have h2 : (⌊T * W⌋₊ : ℝ) ≤ |T| * W := by
          by_cases hx : 0 ≤ T * W
          · exact (Nat.floor_le hx).trans (mul_le_mul_of_nonneg_right (le_abs_self T) hW0.le)
          · rw [Nat.floor_of_nonpos (le_of_not_ge hx), Nat.cast_zero]; positivity
        have h3 : (|T| + 1) * (W : ℝ) = |T| * W + W := by ring
        linarith
      have hw : (W : ℝ) * ((Real.sqrt W)⁻¹) ^ 3 = (Real.sqrt W)⁻¹ := by
        have h : Real.sqrt W ^ 2 = (W : ℝ) := Real.sq_sqrt hW0.le
        have hne : Real.sqrt W ≠ 0 := hsW0.ne'
        calc (W : ℝ) * ((Real.sqrt W)⁻¹) ^ 3 = Real.sqrt W ^ 2 * ((Real.sqrt W)⁻¹) ^ 3 := by
              rw [h]
          _ = (Real.sqrt W)⁻¹ := by field_simp
      have hCB : 0 ≤ Cs * B * ((Real.sqrt W)⁻¹) ^ 3 := by positivity
      calc ((Finset.Icc (openEntranceTime W) ⌊T * W⌋₊).card : ℝ) * (Cs * B * ((Real.sqrt W)⁻¹) ^ 3)
          ≤ (|T| + 1) * W * (Cs * B * ((Real.sqrt W)⁻¹) ^ 3) :=
            mul_le_mul_of_nonneg_right hcard hCB
        _ = (|T| + 1) * (Cs * B) * ((W : ℝ) * ((Real.sqrt W)⁻¹) ^ 3) := by ring
        _ = (|T| + 1) * (Cs * B) * (Real.sqrt W)⁻¹ := by rw [hw]

end DetClockBulk

/-- **The deterministic-clock lemma on compact parameter sets** (`DetClockEvolutionDBulk`), from
`PassiveCovarianceEnergyUniformHyp`, `TransmissionUniform3.PassiveSourceMixingEnergyUniformContract`,
`PassiveSourceMixingContract` (jet existence only), `GaussianAbsorptionContract`,
`LayersOnePort.OnePortWeightedCovarianceContract` and `OpenInputsMomentsBulk`. Here
`ε = min ε₉ ε₁₈` (the `OpenInputsMomentsBulk` radii at orders `9` and `18`).
-/
theorem detClockEvolutionDBulk_of (hPCU : PassiveCovarianceEnergyUniformHyp)
    (hPSMU :
      BlockBand.Internal.Contracts.TransmissionUniform3.PassiveSourceMixingEnergyUniformContract)
    (hPSM : PassiveSourceMixingContract) (hGA : GaussianAbsorptionContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract)
    (hOIB : OpenInputsMomentsBulk) : DetClockEvolutionDBulk := by
  intro β κ hβ hβ4 hκ T q hq
  obtain ⟨ε₉, hε₉, hOI9⟩ := hOIB β κ hβ hβ4 hκ T q hq 9 (by norm_num)
  obtain ⟨ε₁₈, hε₁₈, hOI18⟩ := hOIB β κ hβ hβ4 hκ T q hq (2 * 9) (by norm_num)
  refine ⟨min ε₉ ε₁₈, lt_min hε₉ hε₁₈, fun b hb K hK => ?_⟩
  have hb0 : 0 < b := lt_of_lt_of_le hβ hb.1
  have hb1 : b < 1 / 2 := by linarith [hb.2]
  obtain ⟨C₁, W₁, hC₁⟩ := hOI9 b hb
  obtain ⟨Co, Wo, hCo⟩ := hOI18 b hb
  obtain ⟨C₂, W₂, hCM⟩ := DetClockBulk.clockMixing_core hPSMU hPSM hGA hb0 hb1 hκ hq
    (by norm_num : (1 : ℝ) ≤ 9) hCo
  exact DetClockBulk.detClockBulk_core hPSMU hPCU hPSM hGA hWC hb0 hb1 hκ hq
    (fun W hW E hE D hD hDε => hC₁ W hW E hE D hD (hDε.trans (min_le_left _ _)))
    (fun W hW E hE D hD hDε => hCM W hW E hE D hD (hDε.trans (min_le_right _ _))) K hK

end MovingEnergy

end BlockBand.Endpoints.Clock
