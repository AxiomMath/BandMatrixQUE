module

public import BlockBand.Endpoints.Poisson.PoissonEndpointLaplace
public import BlockBand.Endpoints.Poisson.PoissonEndpointLimit
public import BlockBand.Internal.Contracts.CriticalEntire

/-!
# The Poisson endpoint theorem for the original ring

**Statement** (`PoissonEndpointStatement`, in `PoissonEndpointDefs`). It has two clauses:
the Poisson Laplace limit (`PoissonEndpointLaplace`), and the convergence of every critical
family to the unit Poisson law as `τ → ∞` (`PoissonEndpointLimitClause`). The second clause is
exactly the last conjunct of `HasCriticalEndpoints`.

**Theorems.**
* `poissonEndpoint_of_sameVolume` proves both clauses from the following inputs (together with
  the density, ring-model, projected Wegner and block-count hypotheses):
  - the PSSS `SourceContract` (the factorial-moment bound of the counting theorem);
  - `PeSameVolumeLogError` (the same-volume log-error bound).
* `poissonEndpoint` replaces `PeSameVolumeLogError` by its derivation `PeSameVolumeDerivation`
  and the inputs of that derivation, among them the remote-higher theorem.
* `poissonEndpoint_jointRecovery`: under a joint-recovery hypothesis, the unique jointly
  recovered family converges to the unit Poisson law.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.InputsRing (RingBlockModels)
open BlockBand.Internal.Contracts.Critical (CollarKernelContract)
open BlockBand.Internal.Contracts.Layers (MatchedTracesContract)
open BlockBand.Internal.Contracts.TransmissionUniform (TransmissionLengthUniformContract)
open BlockBand.Internal.Contracts.CriticalEntire (JointRecoveryContract IsJointRecoveryFamily)

open BlockBand.External.PSSS in
/-- **The Poisson endpoint theorem, both clauses, from the same-volume log-error bound.**
Hypotheses include:
* the PSSS `SourceContract` (the counting theorem);
* `PeSameVolumeLogError`. -/
theorem poissonEndpoint_of_sameVolume (source : SourceContract.{0}) (hDens : CriticalDensity)
    (hRing : RingBlockModels) (hWegner : ProjectedWegner) (hCount : ConditionalBlockGUECount)
    (hSV : PeSameVolumeLogError) : PoissonEndpointStatement :=
  ⟨poissonEndpointLaplace_of_sameVolume source hDens.1 hRing hWegner hCount hSV,
    poissonEndpointLimit_of_laplace
      (poissonEndpointLaplace_of_sameVolume source hDens.1 hRing hWegner hCount hSV)⟩

open BlockBand.External.PSSS in
/-- **The Poisson endpoint theorem**, both clauses. Hypotheses include:
* the PSSS `SourceContract`;
* `hRH : RemoteHigherStatement` (the remote-higher theorem, full statement);
* `PeSameVolumeDerivation`. -/
theorem poissonEndpoint (source : SourceContract.{0}) (hDens : CriticalDensity)
    (hRing : RingBlockModels) (hWegner : ProjectedWegner) (hCount : ConditionalBlockGUECount)
    (hK : CollarKernelContract) (hMT : MatchedTracesContract)
    (hTU : TransmissionLengthUniformContract) (hPL : PassiveLog) (hSLM : SingularLogMoments)
    (hRH : RemoteHigherStatement) (hDer : PeSameVolumeDerivation) : PoissonEndpointStatement :=
  poissonEndpoint_of_sameVolume source hDens hRing hWegner hCount
    (hDer hK hMT hTU hPL hSLM hRH)

open BlockBand.External.PSSS in

/-- **The Poisson endpoint for the critical limit of `JointRecoveryContract`.** The unique joint-recovery family
converges to the unit Poisson law as `τ → ∞`, under the hypotheses of `poissonEndpoint_of_sameVolume`. -/
theorem poissonEndpoint_jointRecovery (source : SourceContract.{0}) (hDens : CriticalDensity)
    (hRing : RingBlockModels) (hWegner : ProjectedWegner) (hCount : ConditionalBlockGUECount)
    (hSV : PeSameVolumeLogError) (hJR : JointRecoveryContract) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
      ∃! family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsJointRecoveryFamily b E hb hb' family ∧
          ∀ poissonLaw : ProbabilityMeasure (VaguePointMeasure ℝ), IsUnitPoissonLaw poissonLaw →
            Tendsto (fun τ : PositiveRatio => spectralProjectionLaw (family τ)) atTop
              (𝓝 poissonLaw) := by
  intro b E hb hb' hE
  have hL := poissonEndpointLaplace_of_sameVolume source hDens.1 hRing hWegner hCount hSV
  obtain ⟨F, hF, huniq⟩ := hJR b E hb hb' hE
  exact ⟨F, ⟨hF, fun poissonLaw hpois => pe_tendsto_poisson_of_conv hL b hb hb' E hE.1 hE.2 F
    hF.convergence hF.unitIntensity poissonLaw hpois⟩, fun G hG => huniq G hG.1⟩

end BlockBand.Endpoints
