module

public import BlockBand.Endpoints.EndpointsFinalDiffusion
public import BlockBand.Endpoints.Transmission.AlongAssembly
public import BlockBand.Endpoints.Clock.MovingEnergyAdapters
public import BlockBand.Internal.ReducedInputs.NormalizationPsss
public import BlockBand.Internal.ReducedInputs.AnalyticChainGUEInputs
public import BlockBand.Internal.Composition.PSSSLayers
public import BlockBand.Native.PSSS.SourceContract
public import BlockBand.Native.PSSS.Consequences
public import BlockBand.Native.Johansson.SourceContractHolds
public import BlockBand.Native.Prekopa.SourceContract
public import BlockBand.Native.ErdosRiabov.Consequences
public import BlockBand.Native.CEH.Deterministic.Fields
public import BlockBand.Native.CEH.Deterministic.Eigenpairs
public import BlockBand.Native.CEH.LocalLaw.Holds
public import BlockBand.Native.CEH.ETH.Holds
public import BlockBand.GaussianCalculus.LpGradient
public import BlockBand.GaussianCalculus.Poincare
public import BlockBand.GaussianCalculus.MultivariateIBP
public import BlockBand.SourceProcess.Stochastic.Assembly.Contracts
public import BlockBand.SourceProcess.Stochastic.Assembly.ContractB
public import BlockBand.Palm.ConditionalMomentsHolds
public import BlockBand.Coarea.CoareaContract
public import BlockBand.Coarea.FreshPalmDensity
public import BlockBand.Coarea.PoleExclusion
public import BlockBand.Coarea.PairLawBridge
public import BlockBand.Coarea.CompressedLawBridge
public import BlockBand.Center.PhysicalCenterW0Holds
public import BlockBand.Center.CenterSupplyHolds
public import BlockBand.Layers.HeatMeanSquare
public import BlockBand.Layers.FreshCountMeanSquare
public import BlockBand.Layers.BUniformAbsorption
public import BlockBand.Layers.BUniformFluctuation
public import BlockBand.Layers.BUniformClockHolds
public import BlockBand.Layers.WeightedLayer
public import BlockBand.Layers.OnePortCovariance
public import BlockBand.Layers.OnePortSDHolds
public import BlockBand.Layers.OnePortMoments
public import BlockBand.Wegner.RingBlockModel
public import BlockBand.Foundations.RingSymmetry.Rotation
public import BlockBand.PointProcess.BlockAtom.Holds
public import BlockBand.Critical.PointDensity
public import BlockBand.Critical.CommonPort.MeanClause
public import BlockBand.Critical.Collar.Density.CondSchurIdentity
public import BlockBand.Endpoints.Normalization.RegularEventAssembly
public import BlockBand.Endpoints.Normalization.GaussianRatiosAssembly
public import BlockBand.Endpoints.Normalization.LeadFieldLaw
public import BlockBand.Endpoints.Normalization.VanishingBlockAtomAssembly
public import BlockBand.Endpoints.Clock.UniformTags
public import BlockBand.Endpoints.Clock.UniformTagsCommonPort
public import BlockBand.Endpoints.Clock.CommonPortRatios
public import BlockBand.Endpoints.Clock.CovarianceStability
public import BlockBand.SourceProcess.FullSource.DeltaHolds
public import BlockBand.SourceProcess.TagBirth.Main
public import BlockBand.SourceProcess.ContractingWords.WordsHolds
public import BlockBand.Transmission.EnergyUniform.Holds
public import BlockBand.Transmission.DualBoundary.Holds
public import BlockBand.Transmission.LengthUniform.ConductanceUniform
public import BlockBand.Transmission.CovarianceEnergyUniform.Holds
public import BlockBand.Transmission.MixingEnergyUniform.Holds
public import BlockBand.Transmission.FractionalBulk.Main
public import BlockBand.Transmission.LawForced.LawHolds
public import BlockBand.Transmission.PassiveCovariance.CovarianceHolds
public import BlockBand.Transmission.SourceMixing.Holds
public import BlockBand.Transmission.ScalarContraction.Holds

/-!
# The endpoints theorem without hypotheses

For every admissible `(b, E)`, every family satisfying `IsCriticalFamily` has the endpoint
behaviour `HasCriticalEndpoints`: the variance limit, its limit as the ratio tends to zero, and
the sine and Poisson spectral limits at the two ends of the ratio scale.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Composition

open MeasureTheory

/-- **The endpoints theorem**, with the variance limit, the small-variance limit and the spectral
endpoint limits.

The assertion applies to the already-characterized critical family. It gives a
single smoothing-independent variance, positivity for every positive ratio,
the right limit at zero, and the sine/Poisson spectral limits in that order of
limits. No diagonal `n/W → ∞` assertion is made. -/
theorem endpoints_unconditional
    (b E : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) :
    ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family →
        HasCriticalEndpoints b E hb hb' family := by
  -- inputs
  have source := BlockBand.Native.PSSS.sourceContract_holds_zero
  have hJ := BlockBand.Native.Johansson.sourceContract_holds
  have hELG := BlockBand.Native.CEH.externalLocalGUE_holds
  have hMDE := BlockBand.Native.CEH.mdeBranchIdentification_holds
  
  have hLp := BlockBand.GaussianCalculus.gaussianLpGradient_holds
  have hP := BlockBand.GaussianCalculus.gaussianPoincare_holds
  have hIBP := BlockBand.GaussianCalculus.multivariateGaussianIBP_holds
  have hcount := BlockBand.Native.PSSS.conditionalBlockGUECount_native
  have hPBC := BlockBand.Native.PSSS.physicalBlockConditionalCount_native
  have hES := BlockBand.Native.PSSS.externalSine_native hJ
  
  have hGA := BlockBand.Internal.Composition.gaussianAbsorption_native source
  have hTM := BlockBand.Internal.Composition.traceMatrix_native source
  have hLC := BlockBand.Internal.Composition.layerComparison_native source
  have hMT := BlockBand.Internal.Composition.matchedTraces_native source
  have hSR := BlockBand.Internal.Composition.scalarRecursion_native source
  
  have hpole := BlockBand.Coarea.PoleExclusion.pairPoleExclusionContract_holds
  have hFP := BlockBand.Palm.freshPalmContract_holds
    (fun d => (BlockBand.SourceProcess.Stochastic.Assembly.contractA_holds d).1)
    (BlockBand.SourceProcess.Stochastic.Assembly.contractA_holds 1).2
    BlockBand.SourceProcess.Stochastic.Assembly.contractB_holds
    hELG hMDE hLp hIBP
  have hFED := BlockBand.Coarea.FreshPalm.freshEigenpairDensityContract_holds
  
  have hPD := BlockBand.Critical.PointDensity.pointDensity_holds hES
  have hCPM := BlockBand.Critical.CommonPort.commonPortMean_holds hGA hLC
  
  have hSmall := BlockBand.Internal.ReducedInputs.smallCritical_of_center_gueInputs source
    BlockBand.Native.CEH.eigenpairs_exist BlockBand.Native.CEH.spacing_exists
    BlockBand.Native.Prekopa.sourceContract_holds hMDE BlockBand.Native.CEH.externalETH_holds hELG
    hLp hPBC hMT (BlockBand.Layers.ringCompensatedPhase_holds hcount hLp)
    (BlockBand.Layers.rankLocation_holds hcount hLp) (BlockBand.Layers.freshCount_holds hcount hLp)
    BlockBand.Coarea.coareaContract_holds hFP hFED hpole
    BlockBand.Coarea.LawBridge.pairGUELawBridge_holds
    BlockBand.Coarea.LawBridge.compressedGUELawBridge_holds
    BlockBand.Center.pairCenterFamily0 (BlockBand.Center.centerSupply_holds hcount hLp hpole)
    (fun b θ T hb hb' hθ _ => BlockBand.Center.physicalCenter_holds hcount hLp hpole b θ T hb hb' hθ)
  
  have hVBA := BlockBand.PointProcess.BlockAtom.vanishingBlockAtom_holds hSmall
  
  have hFSMU := BlockBand.Transmission.EnergyUniform.fullSourceMomentsEnergyUniform_holds hGA hLp hSR
  have hPCU :=
    BlockBand.Transmission.CovarianceEnergyUniform.passiveCovarianceEnergyUniform_holds hGA hLp hP
  have hGAU := BlockBand.Layers.gaussianAbsorptionUniform_holds hcount
  have hTFU := BlockBand.Layers.traceFluctuationUniform_holds hcount hLp
  have hCMU := BlockBand.Layers.clockMeanUniform_holds hcount
  have hPSMU :=
    BlockBand.Transmission.MixingEnergyUniform.passiveSourceMixingEnergyUniform_holds hGA hLp
  have hPSM := BlockBand.Transmission.SourceMixing.passiveSourceMixing_holds hMT hGA hLp
  have hWL := BlockBand.Layers.weightedLayer_holds hcount hLp
  have hWC := BlockBand.Layers.onePortWeightedCovariance_holds hcount
  exact BlockBand.Endpoints.endpoints_of_contracts
    (BlockBand.SourceProcess.FullSource.fullSourceMoments_holds hGA hLp hSR)
    (BlockBand.Endpoints.Transmission.transmissionLawEnergyUniform_holds hMT hGA hLp hP hSR)
    hFSMU
    (BlockBand.Transmission.DualBoundary.dualBoundaryStart_holds hMT hGA hLp hP)
    (BlockBand.Transmission.LengthUniform.transmissionLengthUniform_holds hMT hGA hLp)
    hcount
    (BlockBand.Internal.ReducedInputs.physicalLeadProfileContract_of_psss source hMT hPD hFP hCPM
      (BlockBand.Endpoints.Normalization.vanishingBlockAtom_of_psss source hSmall))
    (BlockBand.Endpoints.Clock.MovingEnergy.negativeClock_of_uniformContracts hFSMU hPCU hGAU hTFU hCMU hPSMU
      hPSM hGA hTM hWL hWC)
    hSmall
    source
    BlockBand.Native.ErdosRiabov.criticalDensity_native_er
    BlockBand.Wegner.ringBlockModels_holds
    BlockBand.Native.PSSS.projectedWegner_native
    hES
    BlockBand.Coarea.coareaContract_holds
    (BlockBand.Endpoints.Normalization.pairRegularEvent_of_inputs hMT hPBC)
    hPBC
    (BlockBand.Internal.ReducedInputs.exactPalmContract_holds_psss source)
    BlockBand.Foundations.RingSymmetry.ringRotationInvariance_holds
    hVBA
    (BlockBand.Internal.ReducedInputs.oneBlockPalmContract_holds_psss source)
    (BlockBand.Internal.ReducedInputs.oneBlockNormalizerContract_of_psss source hMT hPD)
    hFED
    (BlockBand.Endpoints.Clock.uniformClockTagsPalm_of_twoPositiveClocks
      (BlockBand.Endpoints.Normalization.twoPositiveClocksPalm_of_contracts hFP hPD hFED))
    BlockBand.Endpoints.Clock.clockCovarianceStability_holds
    (BlockBand.Endpoints.Normalization.blockRegularEvent_of_inputs hMT hPBC)
    BlockBand.Endpoints.Normalization.leadFieldIdentification_holds
    (BlockBand.Endpoints.Clock.uniformClockTagsCommonPort_of_twoPositiveClocks
      (BlockBand.Endpoints.Clock.twoPositiveClocksCommonPort_of_commonPortMean hCPM))
    hMT
    (BlockBand.Endpoints.Clock.MovingEnergy.clockSmallBall_of_uniformContracts hFSMU hPCU hGAU hTFU hCMU hPSMU
      hPSM hGA hTM hWL hWC)
    (BlockBand.SourceProcess.TagBirth.tagBirthValueEnergyUniform_holds hMT hGA hLp)
    (BlockBand.Transmission.FractionalBulk.fullSourceStopsEnergyUniform_holds hMT hGA hLp hSR hP)
    (BlockBand.SourceProcess.ContractingWords.contractingWordsEnergyUniform_holds hMT hGA hLp hSR hP)
    (BlockBand.Critical.Collar.Density.collarKernelContract_of_inputs hFP hPD hCPM hTM source)
    BlockBand.Native.PSSS.passiveLog_native
    (BlockBand.Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP)
    (BlockBand.Transmission.PassiveCovariance.passiveCovariance_holds hGA hLp hP)
    hPSM
    (BlockBand.SourceProcess.FullSource.edgeClockMoments_holds' hGA hLp hSR)
    (BlockBand.Layers.onePortPassiveMean_holds hcount hLp)
    (BlockBand.Layers.onePortOperatorMoments_holds hcount)
    (BlockBand.Transmission.ScalarContraction.passiveScalarContraction_holds hGA hLp)
    (BlockBand.SourceProcess.ContractingWords.contractingWords_holds hMT hGA hLp hSR hP)
    (BlockBand.Transmission.FractionalBulk.fullSourceStops_holds hMT hGA hLp hSR hP)
    (BlockBand.SourceProcess.ContractingWords.fullSourceGenerator_holds hMT hGA hLp hSR hP)
    b E hb hb' hE

end BlockBand.Internal.Composition
