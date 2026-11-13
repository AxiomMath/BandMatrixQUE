module

public import BlockBand.Endpoints.Response.JetFixedBridge
public import BlockBand.Endpoints.Response.RemoteHigherLimit

/-!
# The remote higher-order clock theorem with the fixed-moment jet contraction

This file reproves the compositions leading to `RemoteHigherStatement` with
`OnePortJetContractionFixed` in place of `OnePortJetContraction`.

* `clockHigherOneLayer_of_fixed`: the weighted higher one-layer step, via `rhc_weighted_det`.
* `rhcHigherOneStep_of_onePort_fixed`, `remoteHigher_of_onePort_fixed`, `rhl_higherLimitDecay_of_onePort_fixed`,
  `remoteHigher_of_onePort'_fixed`: the same compositions as `rhcHigherOneStep_of_onePort`,
  `remoteHigher_of_onePort`, `rhl_higherLimitDecay_of_onePort` and `remoteHigher_of_onePort'`.
* `remoteHigher_of_scalarContraction`: `RemoteHigherStatement` with the jet contraction obtained from
  `PassiveScalarContractionContract`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.Inputs
  BlockBand.Internal.Contracts.LayersOnePort BlockBand.Internal.Contracts.TransmissionUniform

/-- **`ClockHigherOneLayer` from the higher logistic inequality, fixed-moment (c)**. As
`clockHigherOneLayer_of`, with the one-port input (c) in the form `OnePortJetContractionFixed`
(used at `r = 2` through `jfx_two`). Hypotheses: `TransmissionLawContract` (existence of the
stationary jet), `ClockLayerHigherLogistic` and `OnePortOperatorMoments` (`r = 2`). The weight is `K = 2C/(1-ρ)`, the jet radius
`≤ 1/(K+1)`, and the slack `e = 0`.
-/
theorem clockHigherOneLayer_of_fixed (hTL : TransmissionLawContract)
    (hLog : ClockLayerHigherLogistic) (hb : OnePortOperatorMoments)
    (hc : OnePortJetContractionFixed) : ClockHigherOneLayer := by
  intro b hb0 hb' E hE hE' p r hp hp' hr hpr s₀ s₂ hs₀ hs₀₂
  obtain ⟨s, hs⟩ := (hTL.jetGap b hb0 hb' E hE hE').1
  obtain ⟨CL, cL, dL, WL, hCL, hcL, hdL, hLogW⟩ := hLog b hb0 hb' E hE hE' p r hp hp' hr hpr s hs
  obtain ⟨db, hdb, hbr⟩ := hb b hb0 hb' E hE hE' s hs
  obtain ⟨C₄, Wb, hb4⟩ := hbr 2
  obtain ⟨ρ, Cc, dc, Wc, hρ0, hρ1, hCc, hdc, hWc1, hcW⟩ := jfx_two hc hb0 hb' hE hE' hs
  set K := 2 * CL / (1 - ρ) with hKdef
  have h1ρ : 0 < 1 - ρ := by linarith
  have hK0 : 0 ≤ K := div_nonneg (by linarith) h1ρ.le
  have hK : K * ρ + 2 * CL ≤ K := by
    have : K * (1 - ρ) = 2 * CL := by rw [hKdef]; field_simp
    nlinarith
  set d := min (min dL db) (min dc (1 / (K + 1)))
  have hd0 : 0 < d := lt_min (lt_min hdL hdb) (lt_min hdc (by positivity))
  have hdK : K * d ≤ 1 := by
    have h1 : d ≤ 1 / (K + 1) := (min_le_right _ _).trans (min_le_right _ _)
    calc K * d ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left h1 hK0
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  set C₄' := max C₄ 0
  set C' := rhc_weightC K ρ CL Cc d ((Cc * Real.sqrt 2) ^ 2 + (1 + C₄')) with hC'
  have hC'0 : 0 ≤ C' := by
    have : 0 ≤ C₄' := le_max_right _ _
    simp only [hC', rhc_weightC]; positivity
  refine ⟨K, C', cL, d, s, hK0, hC'0, hcL, hd0, hs, fun t₁ R q hq => ?_⟩
  refine ⟨fun _ => 0, by simp, max (max WL Wb) Wc, fun W hW j _ _ => ?_⟩
  filter_upwards [ae_growthPath_isHermitian W b] with ω hω hD
  have hWL : WL ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWb : Wb ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWc : Wc ≤ W := le_trans (le_max_right _ _) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans hWc1 hWc
  obtain ⟨hD1, hD2, hD3⟩ := hD
  have hXd : cel_InJetDomain b E s d (pathX b E W j ω) :=
    ⟨cel_pathX_passive (by linarith) hE hE' j hω, hD1, hD2, hD3⟩
  have hA := ce_nearClock_posSemidef b E W j hq.2.2.2.1.1 ω
  have hdLd : d ≤ dL := (min_le_left _ _).trans (min_le_left _ _)
  have hdbd : d ≤ db := (min_le_left _ _).trans (min_le_right _ _)
  have hdcd : d ≤ dc := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨ξ, hξm, hξ, hξ2⟩ := hcW W hWc _ (hXd.mono hdcd)
  have hL4 : ∫⁻ ν, ENNReal.ofReal (‖freshL b E (pathX b E W j ω) ν‖ ^ 4) ∂freshLaw W b ≤
      ENNReal.ofReal C₄' :=
    (hb4 W hWb _ (hXd.mono hdbd)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hlog := hLogW W hWL _ (hXd.mono hdLd) _ hA
  have key := rhc_weighted_det hp hr hpr.le hA hW1 hK0 hρ0 hρ1.le hCc hCL (le_max_right _ _) hK
    hXd.2.1 hdK hξm hξ hξ2 hL4 hlog
  simp only [ENNReal.ofReal_zero, add_zero]
  exact key

/-- **`RhcHigherOneStep` from the one-port contracts and the fixed-moment (c)**: as
`rhcHigherOneStep_of_onePort`, with `OnePortJetContractionFixed` in place of
`OnePortJetContraction`.
-/
theorem rhcHigherOneStep_of_onePort_fixed (hCount : ConditionalBlockGUECount)
    (hTL : TransmissionLawContract) (hPC : PassiveCovarianceContract)
    (hPSM : PassiveSourceMixingContract) (hPM : OnePortPassiveMeanContract)
    (hOM : OnePortOperatorMomentsContract) (hJet : OnePortJetContractionFixed) :
    RhcHigherOneStep :=
  rhcHigherOneStep_of_oneLayer hCount
    (clockHigherOneLayer_of_fixed hTL
      (clockLayerHigherLogistic_of
        (clockLayerLogistic_of_jensenGap
          (clockLayerJensenGap_of_taylor hPC hTL hPSM fractionalTraceJensenGap_holds
            (onePortPassiveMean_of_contract hPM) (onePortOperatorMoments_of_contract hOM))
          (onePortPassiveMean_of_contract hPM))
        (onePortPassiveMean_of_contract hPM) (onePortOperatorMoments_of_contract hOM) hPSM)
      (onePortOperatorMoments_of_contract hOM) hJet)

/-- `RemoteHigherStatement` as in `remoteHigher_of_onePort` (from `RhHigherLimitDecay`), with
`OnePortJetContractionFixed` in place of `OnePortJetContraction`. -/
theorem remoteHigher_of_onePort_fixed (hCount : ConditionalBlockGUECount)
    (hTL : TransmissionLawContract) (hPC : PassiveCovarianceContract)
    (hPSM : PassiveSourceMixingContract) (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hPM : OnePortPassiveMeanContract)
    (hOM : OnePortOperatorMomentsContract) (hJet : OnePortJetContractionFixed)
    (hL : RhHigherLimitDecay) (hGen : FullSourceGeneratorContract) : RemoteHigherStatement :=
  remoteHigher_of_recursion
    (rhnHigherWeightedRecursion_of_oneStep hECM hTLU
      (rhcHigherOneStep_of_onePort_fixed hCount hTL hPC hPSM hPM hOM hJet))
    hL hGen (nsCriticalClockLimitsExist_of_contracts hGen)

/-- The higher clock decay at critical limits, as in `rhl_higherLimitDecay_of_onePort`, with
`OnePortJetContractionFixed` in place of `OnePortJetContraction`. -/
theorem rhl_higherLimitDecay_of_onePort_fixed (hCount : ConditionalBlockGUECount)
    (hTL : TransmissionLawContract) (hPC : PassiveCovarianceContract)
    (hPSM : PassiveSourceMixingContract) (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hPM : OnePortPassiveMeanContract)
    (hOM : OnePortOperatorMomentsContract) (hJet : OnePortJetContractionFixed)
    (hFin : RhlFiniteTraceGenerator) (hGen : FullSourceGeneratorContract) :
    RhHigherLimitDecay :=
  rhl_limitDecay
    (rhn_higherLater_of_recursion (rhnHigherWeightedRecursion_of_oneStep hECM hTLU
      (rhcHigherOneStep_of_onePort_fixed hCount hTL hPC hPSM hPM hOM hJet)))
    (rhl_regularizedLimitGenerator hFin hCount hGen.moments)

/-- `RemoteHigherStatement` with the finite-width generator, as in `remoteHigher_of_onePort'`, with
`OnePortJetContractionFixed` in place of `OnePortJetContraction`. -/
theorem remoteHigher_of_onePort'_fixed (hCount : ConditionalBlockGUECount)
    (hTL : TransmissionLawContract) (hPC : PassiveCovarianceContract)
    (hPSM : PassiveSourceMixingContract) (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hPM : OnePortPassiveMeanContract)
    (hOM : OnePortOperatorMomentsContract) (hJet : OnePortJetContractionFixed)
    (hFin : RhlFiniteTraceGenerator) (hGen : FullSourceGeneratorContract) :
    RemoteHigherStatement :=
  remoteHigher_of_onePort_fixed hCount hTL hPC hPSM hECM hTLU hPM hOM hJet
    (rhl_higherLimitDecay_of_onePort_fixed hCount hTL hPC hPSM hECM hTLU hPM hOM hJet hFin hGen) hGen

open BlockBand.Internal.Contracts.TransmissionUniform2 in

/-- **`RemoteHigherStatement` with the one-port input (c) from
`PassiveScalarContractionContract`** (through `onePortJetContractionFixed_of_contracts`). The
hypotheses are those of `remoteHigher_of_onePort'` with `OnePortJetContraction` replaced by
`PassiveScalarContractionContract`: `ConditionalBlockGUECount`, `TransmissionLawContract`,
`PassiveCovarianceContract`, `PassiveSourceMixingContract`, `EdgeClockMomentsContract`,
`TransmissionLengthUniformContract`, `OnePortPassiveMeanContract`,
`OnePortOperatorMomentsContract`, the finite-width `RhlFiniteTraceGenerator` and
`FullSourceGeneratorContract`.
-/
theorem remoteHigher_of_scalarContraction (hCount : ConditionalBlockGUECount)
    (hTL : TransmissionLawContract) (hPC : PassiveCovarianceContract)
    (hPSM : PassiveSourceMixingContract) (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hPM : OnePortPassiveMeanContract)
    (hOM : OnePortOperatorMomentsContract) (hPSC : PassiveScalarContractionContract)
    (hFin : RhlFiniteTraceGenerator) (hGen : FullSourceGeneratorContract) :
    RemoteHigherStatement :=
  remoteHigher_of_onePort'_fixed hCount hTL hPC hPSM hECM hTLU hPM hOM
    (onePortJetContractionFixed_of_contracts hPSC) hFin hGen

end BlockBand.Endpoints
