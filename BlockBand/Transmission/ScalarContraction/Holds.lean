module

public import BlockBand.Internal.Contracts.TransmissionUniform2
public import BlockBand.Transmission.PathScalar.MeanEqPort
public import BlockBand.Transmission.PathScalar.AbsorbedStep
public import BlockBand.Transmission.PathScalar.MeanStepLimit
public import BlockBand.Transmission.PassiveLayer.FlucMain
public import BlockBand.Transmission.PassiveLayer.TMMain

/-!
# The one-step predictable contraction of the scalar jet

The target is `TransmissionUniform2.PassiveScalarContractionContract`.

* `integrable_freshTrace`: the fresh near-port trace is integrable under `freshLaw W b`
  (measurable, and a.e. bounded by `η⁻¹`, `PathScalar.norm_freshPortTrace_le`).
* `passiveScalarContraction_of_steps (hMean) (hFl)`: the contract from
  `PathScalar.PassiveMeanStep` and `PathScalar.PassiveFluctuationStep`. The pointwise bound is the
  triangle inequality `|T - a| ≤ |E T - a| + |T - E T|`; the `L^r` bound is the fluctuation step
  after `eLpNorm_norm`.

* `passiveScalarContraction_holds (hGA) (hLp)`: the contract from
  `GaussianAbsorptionContract` and `GaussianLpGradient`, through
  `PathScalar.passiveMeanStep_holds (PassiveLayer.passiveBounds_holds hGA hLp)` and
  `PassiveLayer.passiveFluctuationStep_holds hGA hLp`.

`TransmissionUniform2.freshTrace` is definitionally `PathScalar.freshPortTrace`
(`freshTrace_eq_freshPortTrace`, `rfl`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.ScalarContraction

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform2
open BlockBand.Transmission.PathScalar
open scoped ComplexOrder

variable {W : ℕ}

/-- `TransmissionUniform2.freshTrace` is `PathScalar.freshPortTrace`. -/
theorem freshTrace_eq_freshPortTrace (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    freshTrace b E X = freshPortTrace b E X := rfl

/-- The fresh near-port trace is integrable under `freshLaw W b` at a passive input in the open
bulk: it is measurable and a.e. bounded by `(etaZ b E)⁻¹`. -/
theorem integrable_freshTrace {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    Integrable (freshTrace b E X) (freshLaw W b) := by
  refine Integrable.of_bound (C := (etaZ b E)⁻¹)
    (measurable_freshPortTrace_comp b E measurable_const measurable_id).aestronglyMeasurable ?_
  exact (ae_layer_herm b).mono fun ω hA => norm_freshPortTrace_le hb0 hb h1 h2 hY ω hA

/-- `scalarFluct` is integrable at a passive input in the open bulk. -/
theorem integrable_scalarFluct {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    Integrable (scalarFluct b E X) (freshLaw W b) :=
  (integrable_freshTrace hb0 hb h1 h2 hY).sub (integrable_const _)

/-- `scalarFluct` has mean zero under `freshLaw W b` (a probability measure). -/
theorem integral_scalarFluct {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ∫ ω, scalarFluct b E X ω ∂freshLaw W b = 0 := by
  simp only [scalarFluct]
  rw [integral_sub (integrable_freshTrace hb0 hb h1 h2 hY) (integrable_const _), integral_const,
    probReal_univ, one_smul, sub_self]

/-- The pointwise triangle inequality
`δ₀(X₊) ≤ |E W⁻¹Tr R₊ - a| + |ξ₊|`. -/
theorem jetDistance0_freshSchur_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    jetDistance0 b E (freshSchur E X ω) ≤
      ‖(∫ ω', freshPortTrace b E X ω' ∂freshLaw W b) - matchedA E‖ +
        ‖scalarFluct b E X ω‖ := by
  rw [jetDistance0_freshSchur]
  have e : freshPortTrace b E X ω - matchedA E =
      scalarFluct b E X ω + ((∫ ω', freshPortTrace b E X ω' ∂freshLaw W b) - matchedA E) := by
    simp only [scalarFluct, freshTrace_eq_freshPortTrace]; ring
  rw [e, add_comm ‖_ - matchedA E‖]
  exact norm_add_le _ _

/-- **`PassiveScalarContractionContract` from the passive mean and fluctuation steps.** -/
theorem passiveScalarContraction_of_steps (hMean : PassiveMeanStep)
    (hFl : PassiveFluctuationStep) : PassiveScalarContractionContract where
  contraction := by
    intro b hb0 hb κ hκ
    obtain ⟨d₀, ρ, C, W₀, hd₀, hρ0, hρ1, hC, hmean⟩ := hMean b hb0 hb κ hκ
    refine ⟨d₀, ρ, C, W₀, hd₀, hρ0, hρ1, hC, fun W hW E hE X hY hX => ?_⟩
    obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
    refine ⟨integrable_scalarFluct hb0 hb h1 h2 hY, integral_scalarFluct hb0 hb h1 h2 hY,
      fun ω => ?_⟩
    have hm := hmean W hW E hE X hY hX
    have ht := jetDistance0_freshSchur_le b E X ω
    linarith
  fluct := by
    intro b hb0 hb κ hκ r hr
    obtain ⟨C, W₀, hC, hfl⟩ := hFl b hb0 hb κ hκ r hr
    refine ⟨C, W₀, hC, fun W hW E hE X hY => ?_⟩
    obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
    rw [← eLpNorm_norm _ (integrable_scalarFluct hb0 hb h1 h2 hY).aestronglyMeasurable]
    exact hfl W hW E hE X hY

/-- **`PassiveScalarContractionContract`**, from `GaussianAbsorptionContract` and
`GaussianLpGradient` (explicit hypotheses). -/
theorem passiveScalarContraction_holds (hGA : GaussianAbsorptionContract)
    (hLp : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) :
    PassiveScalarContractionContract :=
  passiveScalarContraction_of_steps
    (passiveMeanStep_holds (PassiveLayer.passiveBounds_holds hGA hLp))
    (PassiveLayer.passiveFluctuationStep_holds hGA hLp)

end BlockBand.Transmission.ScalarContraction
