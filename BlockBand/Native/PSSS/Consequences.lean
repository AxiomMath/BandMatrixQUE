module

public import BlockBand.Native.PSSS.SourceContract
public import BlockBand.Wegner.ProjectedWegner
public import BlockBand.Wegner.SingularLogMoments
public import BlockBand.Wegner.PassiveLog
public import BlockBand.Wegner.PhysicalConditionalCount
public import BlockBand.Density.CouplingEstimate
public import BlockBand.Stationarity.Critical
public import BlockBand.GaussianBulk.ExternalSineFinal

/-!
# Consequences of the PSSS eigenvalue-count theorem

The results that use the PSSS eigenvalue-count theorem as an input, with that input discharged by
the proof `sourceContract_holds_zero`.

| Result | Remaining hypotheses |
|---|---|
| `ProjectedWegner` (the projected Wegner lemma) | none |
| `SingularLogMoments` (the singular log-moment lemma) | none |
| `PassiveLog` (the passive-log lemma) | none |
| `ConditionalBlockGUECount`, `PhysicalBlockConditionalCount` | none |
| `CriticalDensity` (the critical density theorem) | Erdős–Riabov source |
| `CriticalStationarity`, `CriticalMeanSpatialIntensity` (stationarity) | Erdős–Riabov source |
| `ExternalSine` (the external sine-kernel theorem) | Johansson source |
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Native.PSSS

open BlockBand.External

/-- The projected Wegner lemma, all four clauses, with no hypothesis. -/
theorem projectedWegner_native : Internal.Contracts.Inputs.ProjectedWegner :=
  BlockBand.Wegner.projectedWegner_holds sourceContract_holds_zero

/-- The singular log-moment lemma, with no hypothesis. -/
theorem singularLogMoments_native : Internal.Contracts.Inputs.SingularLogMoments :=
  BlockBand.Wegner.singularLogMoments_holds sourceContract_holds_zero

/-- The passive-log lemma, all three clauses, with no hypothesis. -/
theorem passiveLog_native : Internal.Contracts.Inputs.PassiveLog :=
  BlockBand.Wegner.passiveLog_holds sourceContract_holds_zero

/-- Conditional fresh-block PSSS count, with no hypothesis. -/
theorem conditionalBlockGUECount_native : Internal.Contracts.Inputs.ConditionalBlockGUECount :=
  BlockBand.Wegner.conditionalBlockGUECount_holds sourceContract_holds_zero

/-- Physical block-conditional PSSS count, with no
hypothesis.
-/
theorem physicalBlockConditionalCount_native :
    Internal.Contracts.Inputs.PhysicalBlockConditionalCount :=
  BlockBand.Wegner.physicalBlockConditionalCount_holds sourceContract_holds_zero

/-- The critical density theorem (estimate and unit intensity) from the Erdős–Riabov source
alone. -/
theorem criticalDensity_native (hER : ErdosRiabov.SourceContract.{0}) :
    Internal.Contracts.Inputs.CriticalDensity :=
  BlockBand.Density.criticalDensity_of_meanResolventBound sourceContract_holds_zero
    (BlockBand.Density.meanResolventBound_holds hER)

/-- The stationarity proposition, mean-intensity clause, from the Erdős–Riabov source alone. -/
theorem criticalMeanSpatialIntensity_native (hER : ErdosRiabov.SourceContract.{0}) :
    Internal.Contracts.Inputs.CriticalMeanSpatialIntensity :=
  BlockBand.Stationarity.criticalMeanSpatialIntensity_of_unitIntensity sourceContract_holds_zero
    (criticalDensity_native hER).2

/-- The stationarity proposition, all three clauses, from the Erdős–Riabov source alone. -/
theorem criticalStationarity_native (hER : ErdosRiabov.SourceContract.{0}) :
    Internal.Contracts.Inputs.CriticalStationarity :=
  BlockBand.Stationarity.criticalStationarity_of_unitIntensity sourceContract_holds_zero
    (criticalDensity_native hER).2

/-- The external sine-kernel theorem from the Johansson source alone. -/
theorem externalSine_native (hJ : Johansson.SourceContract) :
    Internal.Contracts.Inputs.ExternalSine :=
  BlockBand.GaussianBulk.externalSine_holds hJ sourceContract_holds_zero

end BlockBand.Native.PSSS
