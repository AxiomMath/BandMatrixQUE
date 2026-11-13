module

public import BlockBand.SourceProcess.FullSourceStops.Interface
public import BlockBand.SourceProcess.FullSourceStops.TagSupWidth
public import BlockBand.SourceProcess.FullSource.Main
public import BlockBand.SourceProcess.FullSource.DeltaHolds

/-!
# `TagSupBulk`: supremum moments of one tag, uniformly in the birth index and the energy

`tagSupBulk_holds`: the supremum over `j ≤ TW` of one tag mass has every positive moment,
uniformly in the birth index and on the bulk.

Proof: `n = max 1 ⌈p⌉`, weight exponent `2n`, `N = ⌊max T 0 · W⌋`. On the stop (`lintegral_good_le`)
the constant is `1 + 4e^{αT₀}(1 + Kd)B_{2n}`; off the stop (`lintegral_bad_le`)
`((N+1)C_q^{2n}P)^{1/2} ≤ 1` once `W ≥ W₀`, with the superexponential exit probability
`P = ⌊T₀W⌋e^{-cW log W}` (`superexp_absorbs` at `m = W`, `A = 2`, since `N + 1 ≤ (T₀+1)2^W`).
Inputs: the one-layer bounds (`FullSourceEstimates`, `PassiveMeanStep`, `PassiveFluctuationStep`),
`SuperexpExit`, `TagBirthMoments` and `TagPropagationBulk`, all uniform on `bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.FullSource
open scoped ENNReal

/-- **`TagSupBulk`** from the bulk-uniform tag bounds. -/
theorem tagSupBulk_of (hFS : FullSourceEstimates) (hMS : PassiveMeanStep)
    (hFl : PassiveFluctuationStep) (hSX : SuperexpExit) (hBirth : TagBirthMoments)
    (hProp : TagPropagationBulk) : TagSupBulk := by
  intro b hb0 hb κ T p hκ hp
  set T₀ := max T 0
  have hT₀ : 0 ≤ T₀ := le_max_right _ _
  set n : ℕ := max 1 ⌈p⌉₊
  have hn : 1 ≤ n := le_max_left _ _
  have hpn : p ≤ n := (Nat.le_ceil p).trans (by exact_mod_cast le_max_right 1 ⌈p⌉₊)
  obtain ⟨Ca, C₂, Cn, CN₂, CN, Cf, Cm, ρ, d₀, WL, hCa, hC₂, hCn, hCN, hCf, hCm, hρ0, hρ1, hd₀,
    hL⟩ := tagLayerBounds_of hFS hMS hFl hb0 hb hκ (show 2 ≤ 2 * n by omega)
  obtain ⟨Bm, Wbm, hBm, hbm⟩ := hBirth b hb0 hb κ hκ (2 * n) (by omega)
  obtain ⟨Cq, hCq⟩ := hProp b hb0 hb κ T₀ ((2 * n : ℕ) : ℝ) hκ
    (by exact_mod_cast (show 1 ≤ 2 * n by omega))
  obtain ⟨Wq, hWq⟩ := hCq T₀
  set L := lcoef Ca (2 * n)
  have hL0 : 0 ≤ L := lcoef_nonneg hCa _
  set K := 2 * L / (1 - ρ)
  have hK : 0 ≤ K := div_nonneg (by linarith) (by linarith)
  have hKL : L ≤ K * (1 - ρ) / 2 := by
    simp only [K]; rw [div_mul_cancel₀ _ (by linarith : (1 - ρ) ≠ 0)]; linarith
  set d := min (min d₀ 1) ((1 - ρ) / (2 * (ρ * L + 1)))
  have hden : 0 < 2 * (ρ * L + 1) := by nlinarith [mul_nonneg hρ0 hL0]
  have hd0 : 0 < d := lt_min (lt_min hd₀ one_pos) (div_pos (by linarith) hden)
  have hd1 : d ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hdd₀ : d ≤ d₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρLd : ρ * L * d ≤ (1 - ρ) / 2 := by
    have h1 : d ≤ (1 - ρ) / (2 * (ρ * L + 1)) := min_le_right _ _
    have h2 : ρ * L * d ≤ ρ * L * ((1 - ρ) / (2 * (ρ * L + 1))) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hρ0 hL0)
    have h3 : ρ * L * ((1 - ρ) / (2 * (ρ * L + 1))) ≤ (1 - ρ) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
      nlinarith [mul_nonneg hρ0 hL0]
    linarith
  set α := alphaW K Cm Ca C₂ Cn Cf CN (2 * n)
  have hα : 0 ≤ α := alphaW_nonneg hK hCm hCa hCn hCN _
  set Mc := (max Cq 0) ^ (2 * n)
  have hMc : 0 ≤ Mc := pow_nonneg (le_max_right _ _) _
  obtain ⟨c, Ws, hc, hSup⟩ := hSX b hb0 hb κ T₀ hκ d hd0
  obtain ⟨W₃, hW₃⟩ := superexp_absorbs (A := 2) (B := (T₀ + 1) * Mc) (c := c) (T := T₀) (R := 1)
    (by norm_num) (by positivity) hc
  set X := Real.exp (α * T₀) * ((1 + K * d) * Bm)
  have hX : 0 ≤ X := by positivity
  refine ⟨3 + 4 * X, max (max (max WL Wbm) (max Wq Ws)) (max W₃ 1), fun W hW E hE k => ?_⟩
  have hWL : WL ≤ W := le_trans (by simp) hW
  have hWbm : Wbm ≤ W := le_trans (by simp) hW
  have hWq' : Wq ≤ W := le_trans (by simp) hW
  have hWs : Ws ≤ W := le_trans (by simp) hW
  have hW3 : W₃ ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := le_trans (by simp) hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  obtain ⟨hE1, hE2⟩ := bulk_bounds hκ hE
  set μ := growthPathLaw W b
  set N := ⌊T₀ * W⌋₊
  have hNR : (N : ℝ) ≤ T₀ * W := Nat.floor_le (by positivity)
  set P := (⌊T₀ * W⌋₊ : ℝ) * Real.exp (-(c * W * Real.log W))
  have hP0 : 0 ≤ P := by positivity
  have hP : μ (stopEv b E W k d N)ᶜ ≤ ENNReal.ofReal P :=
    (measure_mono (stopEv_compl_subset b E k d T₀ hNR)).trans (hSup W hWs E hE)
  have hmom : ∀ j, j ≤ N → ∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω) ^ (2 * n) ∂μ ≤
      ENNReal.ofReal Mc := by
    intro j hj
    have hjT : (j : ℝ) ≤ T₀ * W := (Nat.cast_le.mpr hj).trans hNR
    by_cases hkj : k < j
    · have hjR : (j : ℝ) ≤ k + T₀ * W + 1 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have h := hWq W hWq' E hE j k hkj hjT hjR
      refine (lintegral_tagMass_pow_le b E j k (2 * n) (by omega)
        (h.trans (ENNReal.ofReal_le_ofReal (le_max_left Cq 0)))).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_pow (le_max_right _ _)]
    · have h0 : ∀ ω, ENNReal.ofReal (tagMass b E W j k ω) ^ (2 * n) = 0 := fun ω => by
        rw [tagMass_eq_zero_of_le b E (not_lt.mp hkj) ω, ENNReal.ofReal_zero,
          zero_pow (by omega)]
      simp only [h0, lintegral_zero]
      exact bot_le
  have hgood := lintegral_good_le hb0 hb hE1 hE2 hW1 hn (k := k) (hL W hWL E hE) hCa hC₂ hCn
    hCN hCf hCm hK hρ0 hρ1 hKL hd1 hρLd hdd₀ hd0.le hNR (hbm W hWbm E hE k)
  have hbad := lintegral_bad_le b E k N n hn d hmom hP
  have hbad1 : ENNReal.ofReal (((N : ℝ) + 1) * Mc) ^ (1 / 2 : ℝ) *
      ENNReal.ofReal P ^ (1 / 2 : ℝ) ≤ 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.rpow_le_one (ENNReal.ofReal_le_one.mpr ?_) (by norm_num)
    have h3 := hW₃ W hW3 W (by simp)
    have hWp : (W : ℝ) + 1 ≤ 2 ^ W := by exact_mod_cast Nat.lt_two_pow_self (n := W)
    have hN1 : (N : ℝ) + 1 ≤ (T₀ + 1) * 2 ^ W := by nlinarith
    calc ((N : ℝ) + 1) * Mc * P ≤ ((T₀ + 1) * 2 ^ W) * Mc * P := by gcongr
      _ = P * (2 ^ W * ((T₀ + 1) * Mc)) := by ring
      _ ≤ 1 := h3
  have hsplit : ∫⁻ ω, tagSup b E W k N ω ^ n ∂μ =
      ∫⁻ ω, (stopEv b E W k d N).indicator (fun ω => tagSup b E W k N ω ^ n) ω ∂μ +
        ∫⁻ ω, (stopEv b E W k d N)ᶜ.indicator (fun ω => tagSup b E W k N ω ^ n) ω ∂μ := by
    rw [← lintegral_add_left (((measurable_tagSup b E k N).pow_const n).indicator
      (measurableSet_stopEv b E k d N))]
    congr 1; funext ω; rw [Set.indicator_self_add_compl_apply]
  calc ∫⁻ ω, (⨆ (j : ℕ) (_ : (j : ℝ) ≤ T * W),
          ENNReal.ofReal ((W : ℝ)⁻¹ * (tagResponse b E W j k ω).trace.re)) ^ p ∂μ
      ≤ ∫⁻ ω, tagSup b E W k N ω ^ p ∂μ := by
        refine lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hp.le
        refine iSup₂_mono' fun j hj => ⟨j, Nat.le_floor (hj.trans
          (mul_le_mul_of_nonneg_right (le_max_left T 0) hW0.le)), le_rfl⟩
    _ ≤ ∫⁻ ω, (1 + tagSup b E W k N ω ^ n) ∂μ :=
        lintegral_mono fun ω => rpow_le_one_add_pow _ hp.le hpn
    _ = 1 + ∫⁻ ω, tagSup b E W k N ω ^ n ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ((1 + 4 * ENNReal.ofReal X) + 1) := by
        rw [hsplit]; gcongr; exact hbad.trans hbad1
    _ = ENNReal.ofReal (3 + 4 * X) := by
        rw [ENNReal.ofReal_add (by norm_num) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat,
          ENNReal.ofReal_ofNat]
        ring

/-- **`TagSupBulk` from the input hypotheses** `GaussianAbsorptionContract`,
`ScalarRecursionContract` and `GaussianLpGradient`.
-/
theorem tagSupBulk_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : TagSupBulk := by
  have hFS := fullSourceEstimates_holds hGA hLp
  exact tagSupBulk_of hFS (passiveMeanStep_holds (passiveBounds_holds hGA hLp))
    (passiveFluctuationStep_holds hGA hLp) (superexpExit_of hSR) (tagBirthMoments_of hFS hGA)
    (tagPropagationBulk_holds hFS hGA hLp hSR)

end BlockBand.SourceProcess.FullSourceStops
