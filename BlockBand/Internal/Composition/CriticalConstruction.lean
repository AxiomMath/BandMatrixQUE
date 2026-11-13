module

public import BlockBand.Internal.Composition.CriticalUnconditional
public import BlockBand.Critical.Assembly.CriticalOfRelativeVectors
public import BlockBand.Critical.JointRecovery.Assembly

/-!
# The construction clause of the critical joint-law theorem

The critical joint-law theorem ends with: "the construction in the entire-law theorem
determines this joint law". `BlockBand.critical` states existence and uniqueness of the critical
family but not this sentence. Its formal reading here: every family satisfying
`IsCriticalFamily b E hb hb'` satisfies, at every ratio `τ > 0` and for every finite nonnegative
continuous profile family `q_1, …, q_k` on `𝕋`, the root/derivative construction clause of the
joint recovery theorem, `RootDerivativeRule b E τ q (family τ)`. That is, a law with the
determining hierarchy of the entire-law theorem exists, and for every such law the Laplace
functional of the readout `Σ_α δ_{(u_α, (ν_α(q_a))_{a ≤ k})}` of `family τ` equals that of the
root/derivative extraction from it. The readout tests determine the marked law, so this
identifies `family τ` through the construction. The smoothed hierarchy is not addressed here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Composition

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.CriticalEntire

/-- **The entire-law theorem** (`EntireLawContract`) with no hypotheses: every input is
discharged by the theorem used for it in `critical_unconditional`. -/
theorem entireLaw_unconditional : EntireLawContract := by
  -- inputs
  have source := BlockBand.Native.PSSS.sourceContract_holds_zero
  have hES := BlockBand.Native.PSSS.externalSine_native BlockBand.Native.Johansson.sourceContract_holds
  
  have hLp := BlockBand.GaussianCalculus.gaussianLpGradient_holds
  have hP := BlockBand.GaussianCalculus.gaussianPoincare_holds
  have hIBP := BlockBand.GaussianCalculus.multivariateGaussianIBP_holds
  
  have hGA := BlockBand.Internal.Composition.gaussianAbsorption_native source
  have hTM := BlockBand.Internal.Composition.traceMatrix_native source
  have hLC := BlockBand.Internal.Composition.layerComparison_native source
  have hMT := BlockBand.Internal.Composition.matchedTraces_native source
  have hSR := BlockBand.Internal.Composition.scalarRecursion_native source
  -- `critical_of_duhamel`: the relative mixed vectors
  have hRMV := BlockBand.Critical.RelativeVectors.relativeMixedVectorsStatement_of_inputs
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
    source hES
  -- `critical_of_relativeVectors_sourceContract`: the complex source limit along sequences
  have hA := BlockBand.Critical.GlobalSource.complexSourceLimitAlongSequences_of_contract
    (BlockBand.SourceProcess.LengthCont.OneLayer.complexSourceLimitSequence_holds' hGA hLp hSR hMT)
  have hCS := BlockBand.SourceProcess.ComplexFreq.complexSourceLawContract_of_physFreq
    hMT hGA hLp hP hSR
    (BlockBand.SourceProcess.PhysApprox.complexPhysicalApproximationFreq_holds hMT hGA hSR hLp hP
      BlockBand.SourceProcess.Kolmogorov.kolmogorovConjugate_holds)
  have hFP := BlockBand.Palm.freshPalmContract_holds
    (fun d => (BlockBand.SourceProcess.Stochastic.Assembly.contractA_holds d).1)
    (BlockBand.SourceProcess.Stochastic.Assembly.contractA_holds 1).2
    BlockBand.SourceProcess.Stochastic.Assembly.contractB_holds
    BlockBand.Native.CEH.externalLocalGUE_holds BlockBand.Native.CEH.mdeBranchIdentification_holds
    hLp hIBP
  -- `critical_of_relativeVectors`: the entire law
  exact BlockBand.Critical.EntireLaw.entireLaw_of_matrixClosing
    (BlockBand.Critical.GlobalSource.globalGaussianSource_holds_of_sourceLimit hCS hA)
    (BlockBand.Critical.MatrixClosing.Poles.matrixClosing_of_relativeVectors hRMV hFP
      (BlockBand.Critical.PointDensity.pointDensity_holds hES)
      (BlockBand.Critical.CommonPort.commonPortMean_holds hGA hLC) hTM source)
    source hMT

/-- **The joint recovery theorem** (`JointRecoveryContract`) with no hypotheses: `jointRecovery_of_entireLaw`
applied to `entireLaw_unconditional`, the PSSS source statement `sourceContract_holds_zero` and the critical
unit intensity `criticalUnitIntensity_native_er`. -/
theorem jointRecovery_unconditional : JointRecoveryContract :=
  BlockBand.Critical.JointRecovery.jointRecovery_of_entireLaw entireLaw_unconditional
    BlockBand.Native.PSSS.sourceContract_holds_zero
    BlockBand.Native.ErdosRiabov.criticalUnitIntensity_native_er

/-- The construction clause of the critical joint-law theorem: the construction of the entire
law determines the joint law.

Every family satisfying `IsCriticalFamily` satisfies, at every ratio and for every finite
nonnegative continuous profile family, the root/derivative construction clause of the joint
recovery theorem: a law with the determining hierarchy of the entire-law theorem exists, and the
marked readout of the family equals the root/derivative extraction from every such law. -/
theorem critical_construction_unconditional
    (b E : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) :
    ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family →
        ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q →
          RootDerivativeRule b E τ q (family τ) := by
  intro family hfam τ k q hq
  have := BlockBand.Model.Construction.markedPointMeasureLaw_t2Space
  obtain ⟨F, hF, -⟩ := jointRecovery_unconditional b E hb hb' hE
  obtain ⟨s⟩ := BlockBand.Critical.Assembly.exists_criticalSequence τ.1 τ.2
  let R : ∀ j, FiniteRealization (s.parameters b hb hb' j) := fun j =>
    (BlockBand.Model.Construction.nonempty_finiteRealization _).some
  have heq : family τ = F τ :=
    tendsto_nhds_unique (hfam.2.2.1 τ s R) (hF.convergence τ s R)
  rw [heq]
  exact hF.construction τ k q hq

end BlockBand.Internal.Composition
