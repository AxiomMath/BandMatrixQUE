module

public import BlockBand.Endpoints.Clock.DetClockProof
public import BlockBand.Endpoints.Clock.ClockMixingEnergyUniform

/-!
# The deterministic-clock lemma with the initial radius `ε` uniform in the energy

* `MovingEnergy.DetClockEvolutionDEpsUniform`: the body of `DetClockEvolutionD` with the energy
  quantifier `-2 < E < 2` replaced by `κ > 0` before `ε` and `E ∈ bulkInterval κ` after `ε`. The
  sequence `δ` (and its `W₀`) may depend on `E` and on `K`; `ε` depends only on `b, κ, T, q`.
* `MovingEnergy.detClockStep_core`: the proof of `detClockEvolutionD_of` at one fixed energy,
  with the open-inputs bounds and the clock-mixing bounds at that energy (for `‖D‖ ≤ ε`, moment
  order `9`) as explicit hypotheses.
* `MovingEnergy.detClockEvolutionDEpsUniform_of`: `ε = min ε₁ ε₂`, with `ε₁` from
  `OpenInputsMomentsEnergyUniform` and `ε₂` from `ClockMixingEnergyUniformBound`, both at order
  `9`; then `detClockStep_core` at each `E ∈ bulkInterval κ` (so `-2 < E < 2`, `mem_bulk_lt`),
  with the stationary jet `s` from `PassiveCovarianceContract` at that `E`.
* `MovingEnergy.detClockEvolutionDEpsUniform_of_contracts`: the composite through
  `openInputsMomentsEnergyUniform_of` and `clockMixingEnergyUniform_of_contracts`.
* `MovingEnergy.detClockEvolutionD_of_epsUniform`: the uniform form implies the fixed-energy
  `DetClockEvolutionD` (with `κ` from `MovingEnergy.exists_kappa`).

The hypotheses are `PassiveSourceMixingContract`, `PassiveCovarianceContract` (both used at the
fixed `E`), `GaussianAbsorptionContract`, `LayersOnePort.OnePortWeightedCovarianceContract`,
`OpenInputsMomentsEnergyUniform` and `ClockMixingEnergyUniformBound`; for the composite,
`TransmissionUniform3.PassiveSourceMixingEnergyUniformContract`, `TraceMatrixContract` and
`WeightedLayerContract` replace the last two.
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

/-- **The deterministic-clock lemma with `ε` uniform in `E ∈ bulkInterval κ`** (`b` fixed).
`DetClockEvolutionD` with `κ > 0` before `ε` and `E ∈ bulkInterval κ` after it; `δ` may depend on
`E` and `K`. -/
def DetClockEvolutionDEpsUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (T : ℝ) (q : ℝ → ℝ), IsClockWeight q →
    ∃ ε : ℝ, 0 < ε ∧ ∀ E ∈ bulkInterval κ, ∀ K : ℝ, 1 ≤ K → ∃ δ : ℕ → ℕ → ℝ,
      (∀ W j (D : Matrix (Fin W) (Fin W) ℂ), D.IsHermitian → ‖D‖ ≤ ε →
        openEntranceTime W ≤ j → (j : ℝ) ≤ T * W → ∀ a ∈ Icc K⁻¹ K,
          |detClockRemainderD W b E q D j a| ≤ δ W j) ∧
      Tendsto (fun W => ∑ j ∈ Finset.Icc (openEntranceTime W) ⌊T * W⌋₊, δ W j) atTop (𝓝 0)

open DetClockProof ClockMixingAlg ClockMixingProb

/-- The proof of `detClockEvolutionD_of` at one fixed energy `E`, with the
open-inputs bounds (`C₁`, `W₁`) and the clock-mixing bounds (`C₂`, `W₂`) at that `E`, for
Hermitian `‖D‖ ≤ ε` and moment order `9`, as explicit hypotheses. -/
theorem detClockStep_core (hPSM : PassiveSourceMixingContract)
    (hPC : PassiveCovarianceContract) (hGA : GaussianAbsorptionContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract)
    {b E T ε C₁ C₂ : ℝ} {q : ℝ → ℝ} {W₁ W₂ : ℕ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hE0 : -2 < E) (hE1 : E < 2) (hq : IsClockWeight q)
    (hOI' : ∀ W : ℕ, W₁ ≤ W → ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
      (∀ s : ℂ, IsStationaryJet b E s → ∀ j : ℕ, openEntranceTime W ≤ j →
          (j : ℝ) ≤ T * W →
          eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal 9)
              (oneEndedLaw W b j) +
            eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal 9)
              (oneEndedLaw W b j) ≤ ENNReal.ofReal (C₁ / W)) ∧
      ∀ j : ℕ, (j : ℝ) ≤ T * W →
        eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) ≤
          ENNReal.ofReal (C₁ * ((j : ℝ) + 1) / W))
    (hCM : ∀ W : ℕ, W₂ ≤ W → ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
      ∀ j : ℕ, openEntranceTime W ≤ j → (j : ℝ) ≤ T * W →
        eLpNorm (openClockZ b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) +
            eLpNorm (openClockSqrtS b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) ≤
          ENNReal.ofReal (C₂ / Real.sqrt W)) :
    ∀ K : ℝ, 1 ≤ K → ∃ δ : ℕ → ℕ → ℝ,
      (∀ W j (D : Matrix (Fin W) (Fin W) ℂ), D.IsHermitian → ‖D‖ ≤ ε →
        openEntranceTime W ≤ j → (j : ℝ) ≤ T * W → ∀ a ∈ Icc K⁻¹ K,
          |detClockRemainderD W b E q D j a| ≤ δ W j) ∧
      Tendsto (fun W => ∑ j ∈ Finset.Icc (openEntranceTime W) ⌊T * W⌋₊, δ W j) atTop
        (𝓝 0) := by
  intro K hK
  obtain ⟨⟨s, hs⟩, -⟩ := hPC b hb0 hb1 E hE0 hE1
  obtain ⟨_hqc, hq0, Kq, hqK⟩ := hq
  have hKq : 0 ≤ Kq := (hq0 0).trans (hqK 0)
  have hK0 : 0 < K := by linarith
  obtain ⟨Cs, Ws, hCs0, hstep⟩ := stepDefect_le hPSM hPC hGA hWC hb0 hb1 hE0 hE1 hs hK hKq
  have hD := (transportD0_pos hb0 hE0 hE1).le
  have hd := (dStar_pos (by linarith : b < 1)).le
  set C₁' := max C₁ 0 with hC₁'
  set C₂' := max C₂ 0 with hC₂'
  have hC₁0 : 0 ≤ C₁' := le_max_right _ _
  have hC₂0 : 0 ≤ C₂' := le_max_right _ _
  set B := (1 + C₁' * (|T| + 1) + C₁' + C₂') ^ 9 with hB
  have hB0 : 0 ≤ B := by positivity
  set W₀ := max (max Ws W₁) (max W₂ 1) with hW₀
  let δ : ℕ → ℕ → ℝ := fun W _ => if W₀ ≤ W then Cs * B * ((Real.sqrt W)⁻¹) ^ 3
    else 2 + transportD0 b E * W + dStar b * Kq * K
  refine ⟨δ, ?_, ?_⟩
  · intro W j D hD' hDε hj0 hjT a ha
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
      obtain ⟨hjet, hgam⟩ := hOI' W hW1' D hD' hDε
      have hδ := hjet s hs j hj0 hjT
      have hγ := hgam j hjT
      have hZS := hCM W hW2' D hD' hDε j hj0 hjT
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
        exact hstep W hWs (oneEndedX E D j ω) (X_isHermitian E hD' j ω hω)
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
          (oneEndedQ b E q D j ω)| ≤ 2 + transportD0 b E * W + dStar b * Kq * K := fun ω =>
        stepDefect_trivial (Q_posSemidef b E hq0 D j ω) ha0.le ha.2 hqv.1 hqv.2 hD hd
      calc ∫ ω, |stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
            (oneEndedQ b E q D j ω)| ∂oneEndedLaw W b j
          ≤ ∫ _ω, (2 + transportD0 b E * W + dStar b * Kq * K) ∂oneEndedLaw W b j :=
            integral_mono hint.abs (integrable_const _) hcst
        _ = 2 + transportD0 b E * W + dStar b * Kq * K := by simp
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

/-- **The deterministic-clock lemma with `ε` uniform in `E ∈ bulkInterval κ`**
(`DetClockEvolutionDEpsUniform`), from `PassiveSourceMixingContract`, `PassiveCovarianceContract`,
`GaussianAbsorptionContract`, `LayersOnePort.OnePortWeightedCovarianceContract`,
`OpenInputsMomentsEnergyUniform` and `ClockMixingEnergyUniformBound`. Here `ε = min ε₁ ε₂` with
`ε₁`, `ε₂` the radii of the last two hypotheses at moment order `9`.
-/
theorem detClockEvolutionDEpsUniform_of (hPSM : PassiveSourceMixingContract)
    (hPC : PassiveCovarianceContract) (hGA : GaussianAbsorptionContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract)
    (hOIU : OpenInputsMomentsEnergyUniform) (hCMU : ClockMixingEnergyUniformBound) :
    DetClockEvolutionDEpsUniform := by
  intro b hb0 hb1 κ hκ T q hq
  obtain ⟨ε₁, C₁, W₁, hε₁, hOI⟩ := hOIU b hb0 hb1 κ hκ T q hq 9 (by norm_num)
  obtain ⟨ε₂, C₂, W₂, hε₂, hCM⟩ := hCMU b hb0 hb1 κ hκ T q hq 9 (by norm_num)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun E hE => ?_⟩
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hE
  exact detClockStep_core hPSM hPC hGA hWC hb0 hb1 hE0 hE1 hq
    (fun W hW D hD hDε => hOI W hW E hE D hD (hDε.trans (min_le_left _ _)))
    (fun W hW D hD hDε => hCM W hW E hE D hD (hDε.trans (min_le_right _ _)))

/-- **The deterministic-clock lemma with `ε` uniform in `E ∈ bulkInterval κ`**, from
`TransmissionUniform3.PassiveSourceMixingEnergyUniformContract`,
`PassiveSourceMixingContract`, `PassiveCovarianceContract`, `GaussianAbsorptionContract`,
`TraceMatrixContract`, `WeightedLayerContract`, `LayersOnePort.OnePortWeightedCovarianceContract`
(through `openInputsMomentsEnergyUniform_of` and `clockMixingEnergyUniform_of_contracts`).
-/
theorem detClockEvolutionDEpsUniform_of_contracts
    (hPSMU :
      BlockBand.Internal.Contracts.TransmissionUniform3.PassiveSourceMixingEnergyUniformContract)
    (hPSM : PassiveSourceMixingContract) (hPC : PassiveCovarianceContract)
    (hGA : GaussianAbsorptionContract) (hTM : TraceMatrixContract)
    (hWL : WeightedLayerContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract) :
    DetClockEvolutionDEpsUniform :=
  detClockEvolutionDEpsUniform_of hPSM hPC hGA hWC (openInputsMomentsEnergyUniform_of hGA hTM hWL)
    (clockMixingEnergyUniform_of_contracts hPSMU hPSM hGA hTM hWL)

/-- `DetClockEvolutionDEpsUniform` implies the fixed-energy `DetClockEvolutionD`
(with `κ` from `MovingEnergy.exists_kappa`). -/
theorem detClockEvolutionD_of_epsUniform (h : DetClockEvolutionDEpsUniform) :
    DetClockEvolutionD := by
  intro b hb0 hb1 E hE0 hE1 T q hq
  obtain ⟨κ, hκ, hE⟩ := exists_kappa hE0 hE1
  obtain ⟨ε, hε, hK⟩ := h b hb0 hb1 κ hκ T q hq
  exact ⟨ε, hε, hK E hE⟩

end MovingEnergy

end BlockBand.Endpoints.Clock
