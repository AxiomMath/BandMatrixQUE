module

public import BlockBand.Endpoints.Response.RemoteHigherWindowMoment
public import BlockBand.Endpoints.Response.RemoteHigherWindowLength
public import BlockBand.Endpoints.Response.RemoteHigherExit

/-!
# The uniform remote higher-order clock theorem

This file proves `RhNearHigherLimsupDecayUniform` and the uniform statement
`RemoteHigherUniformStatement` by two reductions: the fixed-energy chain at every length sequence
`m_W/W → t₁+R+s` (`RhwNearHigherLimsupDecayLength`, `rhw_nearHigherLimsupDecay_length`), and the
transfer from the fixed energy `E` to energies in the window `|e_W - E| ≤ K/W²` through the
energy-uniform moment contract.

## Main results

* `rhNearHigherLimsupDecayUniform_of_length (hU) (hLen)`;
* `rhNearHigherLimsupDecayUniform_of_contracts`;
* `remoteHigherUniform_of_contracts`: `RemoteHigherUniformStatement`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.Inputs
  BlockBand.Internal.Contracts.LayersOnePort BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

/-!
## A limsup lemma
-/

/-- If eventually `X_W ≤ C Y_W^{1/a} + 1/W`, then `limsup X ≤ C (limsup Y)^{1/a}`. -/
theorem rhw_limsup_le_of_transfer {X Y : ℕ → ℝ≥0∞} {C a : ℝ} (ha : 0 < a)
    (h : ∀ᶠ W : ℕ in atTop, X W ≤ ENNReal.ofReal C * Y W ^ (1 / a) + ENNReal.ofReal (1 / W)) :
    limsup X atTop ≤ ENNReal.ofReal C * (limsup Y atTop) ^ (1 / a) := by
  have ha' : 0 ≤ 1 / a := le_of_lt (one_div_pos.mpr ha)
  have hmono : Monotone fun x : ℝ≥0∞ => x ^ (1 / a) := fun x y hxy => ENNReal.rpow_le_rpow hxy ha'
  have hcont : ContinuousAt (fun x : ℝ≥0∞ => x ^ (1 / a)) (limsup Y atTop) :=
    (ENNReal.continuous_rpow_const).continuousAt
  have hcomm := hmono.map_limsup_of_continuousAt Y hcont
  set G : ℕ → ℝ≥0∞ := fun W => ENNReal.ofReal C * Y W ^ (1 / a)
  have hG : limsup G atTop = ENNReal.ofReal C * (limsup Y atTop) ^ (1 / a) := by
    rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top, hcomm]
    rfl
  rw [← hG]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have h1 : ∀ᶠ W : ℕ in atTop, ENNReal.ofReal (1 / (W : ℝ)) ≤ (ε : ℝ≥0∞) := by
    have ht : Tendsto (fun W : ℕ => 1 / (W : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε by exact_mod_cast hε))]
      with W hW
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hW.le
  have hmono2 : Monotone fun x : ℝ≥0∞ => x + (ε : ℝ≥0∞) := fun x y hxy => by
    simp only; gcongr
  have hcont2 : ContinuousAt (fun x : ℝ≥0∞ => x + (ε : ℝ≥0∞)) (limsup G atTop) :=
    (continuous_id.add continuous_const).continuousAt
  have hcomm2 := hmono2.map_limsup_of_continuousAt G hcont2
  calc limsup X atTop ≤ limsup (fun W => G W + (ε : ℝ≥0∞)) atTop := by
        refine limsup_le_limsup ?_
        filter_upwards [h, h1] with W hW h1W
        exact hW.trans (by gcongr)
    _ = limsup G atTop + ε := by rw [hcomm2]; rfl

/-!
## The uniform near-clock decay
-/

/-- **`RhNearHigherLimsupDecayUniform`** from
`FullSourceMomentsEnergyUniformContract` and the fixed-energy decay at general
lengths `RhwNearHigherLimsupDecayLength` (derived in `rhw_nearHigherLimsupDecay_length`).
Exponent `a = (1 + 1/(pr))/2`, so `pra < 1`; rate `c'/a`.
-/
theorem rhNearHigherLimsupDecayUniform_of_length (hU : FullSourceMomentsEnergyUniformContract)
    (hLen : RhwNearHigherLimsupDecayLength) : RhNearHigherLimsupDecayUniform := by
  intro b hb hb' E hE hE' p r hp hp1 hr hpr K hK
  have hpr0 : 0 < p * r := by positivity
  set a := (1 + 1 / (p * r)) / 2 with ha_def
  have hinv : 1 < 1 / (p * r) := by rw [lt_div_iff₀ hpr0]; linarith
  have ha1 : 1 < a := by rw [ha_def]; linarith
  have ha0 : 0 < a := by linarith
  have hpra : p * (r * a) < 1 := by
    have : p * (r * a) = (p * r + 1) / 2 := by
      rw [ha_def]; field_simp
    rw [this]; linarith
  have hra : 1 ≤ r * a := by nlinarith
  have hHC := Real.HolderConjugate.conjExponent ha1
  obtain ⟨C', hC'⟩ := hLen b hb hb' E hE hE' p (r * a) hp hp1 hra hpra
  set c' := transportD0 b E * (r * a) * p * (1 - r * a * p) / 2 with hc'def
  have hc' : 0 < c' := by
    have := ns_transportD0_pos hb hE hE'
    have : 0 < 1 - r * a * p := by nlinarith
    positivity
  obtain ⟨C₁, hC₁⟩ := rhw_window_moment_bound hU hb hb' hE hE' hK hp hp1.le hr hHC
  refine ⟨max C₁ 0 * (max C' 0) ^ (1 / a), c' / a, by positivity,
    fun t₁ R q hq s hs e m he hm => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC₁ (t₁ + R + s + 1)
  have hq0 : ∀ x, 0 ≤ q x := ns_isUnitSource_nonneg hq
  have hq1 : ∀ x, q x ≤ 1 := hq.2.2.2.2
  have hts : 1 ≤ t₁ + R + s := by linarith [hq.1, hq.2.1]
  have hm1 : ∀ᶠ W : ℕ in atTop, 1 ≤ m W := by
    have hev := hm.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < t₁ + R + s by linarith))
    filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1
    have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
    rw [lt_div_iff₀ hW0] at hW
    have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    have : (0 : ℝ) < m W := by linarith
    have : 0 < m W := by exact_mod_cast this
    omega
  have hmT : ∀ᶠ W : ℕ in atTop, (m W : ℝ) ≤ (t₁ + R + s + 1) * W := by
    have hev := hm.eventually (gt_mem_nhds (show t₁ + R + s < t₁ + R + s + 1 by linarith))
    filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1
    have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
    rw [div_lt_iff₀ hW0] at hW
    linarith
  have htr : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
      (fracTrace p (nearClock b (e W) W (m W) q ω)) ^ r ∂growthPathLaw W b ≤
      ENNReal.ofReal (max C₁ 0) * (∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E W (m W) q ω)) ^ (r * a) ∂growthPathLaw W b) ^ (1 / a) +
      ENNReal.ofReal (1 / W) := by
    filter_upwards [he, hm1, hmT, eventually_ge_atTop W₀] with W h1 h2 h3 h4
    refine (hW₀ W h4 (e W) h1 (m W) h2 h3 q hq0 hq1).trans ?_
    gcongr
    exact le_max_left _ _
  refine (rhw_limsup_le_of_transfer ha0 htr).trans ?_
  have hY := hC' t₁ R q hq s hs m hm
  calc ENNReal.ofReal (max C₁ 0) * (limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E W (m W) q ω)) ^ (r * a) ∂growthPathLaw W b) atTop) ^ (1 / a)
      ≤ ENNReal.ofReal (max C₁ 0) *
          ENNReal.ofReal (max C' 0 * Real.exp (-(c' * s))) ^ (1 / a) := by
        gcongr
        refine hY.trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (max C₁ 0 * (max C' 0) ^ (1 / a) * Real.exp (-(c' / a * s))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (le_max_right _ _)]
        congr 1
        rw [Real.mul_rpow (le_max_right _ _) (Real.exp_pos _).le, ← Real.exp_mul]
        have he : Real.exp (-(c' * s) * (1 / a)) = Real.exp (-(c' / a * s)) := by
          congr 1; ring
        rw [he, mul_assoc]

/-- **`RhNearHigherLimsupDecayUniform` from the contracts**: the inputs of
`remoteHigher_of_contracts` and `FullSourceMomentsEnergyUniformContract`.
-/
theorem rhNearHigherLimsupDecayUniform_of_contracts (hCount : ConditionalBlockGUECount)
    (hTL : TransmissionLawContract) (hPC : PassiveCovarianceContract)
    (hPSM : PassiveSourceMixingContract) (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hPM : OnePortPassiveMeanContract)
    (hOM : OnePortOperatorMomentsContract)
    (hPSC : BlockBand.Internal.Contracts.TransmissionUniform2.PassiveScalarContractionContract)
    (hCW : ContractingWordsContract) (hStops : FullSourceStopsContract)
    (hGen : FullSourceGeneratorContract) (hU : FullSourceMomentsEnergyUniformContract) :
    RhNearHigherLimsupDecayUniform :=
  rhNearHigherLimsupDecayUniform_of_length hU
    (rhw_nearHigherLimsupDecay_length
      (rhn_higherLater_of_recursion (rhnHigherWeightedRecursion_of_oneStep hECM hTLU
        (rhcHigherOneStep_of_onePort_fixed hCount hTL hPC hPSM hPM hOM
          (onePortJetContractionFixed_of_contracts hPSC))))
      (rhl_higherLimitDecay_of_onePort_fixed hCount hTL hPC hPSM hECM hTLU hPM hOM
        (onePortJetContractionFixed_of_contracts hPSC)
        (rhlFiniteTraceGenerator_holds hCW hStops hCount hGen) hGen)
      hGen (nsCriticalClockLimitsExist_of_contracts hGen))

/-- **The energy-uniform remote higher-order theorem** (`RemoteHigherUniformStatement`) from the
contracts: `remoteHigherUniform_holds` with `rhNearHigherLimsupDecayUniform_of_contracts`.
-/
theorem remoteHigherUniform_of_contracts (hCount : ConditionalBlockGUECount)
    (hTL : TransmissionLawContract) (hPC : PassiveCovarianceContract)
    (hPSM : PassiveSourceMixingContract) (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hPM : OnePortPassiveMeanContract)
    (hOM : OnePortOperatorMomentsContract)
    (hPSC : BlockBand.Internal.Contracts.TransmissionUniform2.PassiveScalarContractionContract)
    (hCW : ContractingWordsContract) (hStops : FullSourceStopsContract)
    (hGen : FullSourceGeneratorContract) (hU : FullSourceMomentsEnergyUniformContract) :
    RemoteHigherUniformStatement :=
  remoteHigherUniform_holds (rhNearHigherLimsupDecayUniform_of_contracts hCount hTL hPC hPSM hECM
    hTLU hPM hOM hPSC hCW hStops hGen hU)

end BlockBand.Endpoints
