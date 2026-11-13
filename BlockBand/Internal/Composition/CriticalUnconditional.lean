module

public import BlockBand.Critical.Assembly.CriticalOfDuhamel
public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.Holds
public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.Assembly
public import BlockBand.SourceProcess.Stochastic.Angular.CondMain
public import BlockBand.SourceProcess.LengthCont.OneLayer.Holds
public import BlockBand.SourceProcess.ComplexFreq.Assembly4
public import BlockBand.SourceProcess.PhysApprox.B3Final
public import BlockBand.SourceProcess.Kolmogorov.Main
public import BlockBand.Internal.Composition.PSSSLayers
public import BlockBand.Native.PSSS.SourceContract
public import BlockBand.Native.PSSS.Consequences
public import BlockBand.Native.Johansson.SourceContractHolds
public import BlockBand.Native.ErdosRiabov.Consequences
public import BlockBand.Native.CEH.Deterministic.Fields
public import BlockBand.Native.CEH.LocalLaw.Holds
public import BlockBand.GaussianCalculus.LpGradient
public import BlockBand.GaussianCalculus.Poincare
public import BlockBand.GaussianCalculus.MultivariateIBP
public import BlockBand.SourceProcess.Stochastic.Assembly.Contracts
public import BlockBand.SourceProcess.Stochastic.Assembly.ContractB
public import BlockBand.Palm.GoodEventHolds
public import BlockBand.Palm.RelativeLocalizationHolds
public import BlockBand.Palm.ConditionalMomentsHolds

/-!
# The critical joint-law theorem without hypotheses

For every admissible `(b, E)` (`0 < b < 1/2`, `-2 < E < 2`) there is a unique family of marked
point-process laws indexed by the positive ratio satisfying `IsCriticalFamily`. All inputs
(the PSSS and Gaussian-calculus theorems and the intermediate estimates) are discharged here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Composition

open MeasureTheory

/-- **The critical joint-law theorem**, with its limit and mean-intensity statements.

For every fixed admissible `(b,E)` there is a unique all-ratio family. Its
characterization includes convergence along every critical sequence, the full
marked vague topology, simple locations, both mean-intensity identities, and
both stationarities. There is no rate or subsequence parameter. -/
theorem critical_unconditional
    (b E : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) :
    ∃! family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family := by
  -- inputs
  have source := BlockBand.Native.PSSS.sourceContract_holds_zero
  
  have hLp := BlockBand.GaussianCalculus.gaussianLpGradient_holds
  have hP := BlockBand.GaussianCalculus.gaussianPoincare_holds
  have hIBP := BlockBand.GaussianCalculus.multivariateGaussianIBP_holds
  
  have hGA := BlockBand.Internal.Composition.gaussianAbsorption_native source
  have hTM := BlockBand.Internal.Composition.traceMatrix_native source
  have hLC := BlockBand.Internal.Composition.layerComparison_native source
  have hMT := BlockBand.Internal.Composition.matchedTraces_native source
  have hSR := BlockBand.Internal.Composition.scalarRecursion_native source
  exact BlockBand.Critical.Assembly.critical_of_duhamel
    (BlockBand.Critical.RelativeVectors.RelativeDuhamel.relativeDuhamel_holds
      BlockBand.SourceProcess.Stochastic.ComplexAngular.complexAngularContract_holds)
    BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint.referenceFlowStatement_holds
    BlockBand.Internal.Composition.coarseRelative_unconditional
    hLp
    (BlockBand.Palm.GoodEvent.spectralGoodEvent_holds hLp hIBP)
    (BlockBand.Palm.RelativeLocalization.relativeLocalization_holds
      (fun N => (BlockBand.SourceProcess.Stochastic.Assembly.contractA_holds (N + N)).1)
      (BlockBand.SourceProcess.Stochastic.Assembly.contractA_holds 1).2
      BlockBand.SourceProcess.Stochastic.Assembly.contractB_holds hLp hIBP)
    BlockBand.SourceProcess.Stochastic.Assembly.contractB_holds
    (BlockBand.SourceProcess.LengthCont.OneLayer.complexSourceLimitSequence_holds' hGA hLp hSR hMT)
    (BlockBand.SourceProcess.ComplexFreq.complexSourceLawContract_of_physFreq hMT hGA hLp hP hSR
      (BlockBand.SourceProcess.PhysApprox.complexPhysicalApproximationFreq_holds hMT hGA hSR hLp hP
        BlockBand.SourceProcess.Kolmogorov.kolmogorovConjugate_holds))
    (BlockBand.Palm.freshPalmContract_holds
      (fun d => (BlockBand.SourceProcess.Stochastic.Assembly.contractA_holds d).1)
      (BlockBand.SourceProcess.Stochastic.Assembly.contractA_holds 1).2
      BlockBand.SourceProcess.Stochastic.Assembly.contractB_holds
      BlockBand.Native.CEH.externalLocalGUE_holds BlockBand.Native.CEH.mdeBranchIdentification_holds
      hLp hIBP)
    hTM hMT hGA hLC
    (BlockBand.Native.PSSS.externalSine_native BlockBand.Native.Johansson.sourceContract_holds)
    BlockBand.Native.ErdosRiabov.criticalUnitIntensity_native_er
    BlockBand.Native.ErdosRiabov.criticalStationarity_native_er
    source
    b E hb hb' hE

end BlockBand.Internal.Composition
