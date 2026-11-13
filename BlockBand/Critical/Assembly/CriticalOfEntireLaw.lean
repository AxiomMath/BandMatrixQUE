module

public import BlockBand.Critical.Assembly.CriticalOfContracts
public import BlockBand.Critical.JointRecovery

/-!
# The critical theorem from the entire law

The critical theorem follows from `EntireLawContract` (the entire-law theorem), the external
PSSS input, and the unit-intensity and stationarity inputs, by composing
`JointRecovery.jointRecovery_of_entireLaw` with `critical_of_contracts`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Critical.Assembly

open MeasureTheory BlockBand.Internal.Contracts

/-- The critical theorem, conditional on the entire law. -/
theorem critical_of_entireLaw (hEL : CriticalEntire.EntireLawContract)
    (source : BlockBand.External.PSSS.SourceContract.{0})
    (hUI : Inputs.CriticalUnitIntensity) (hS : Inputs.CriticalStationarity)
    (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) :
    ∃! family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family :=
  critical_of_contracts (JointRecovery.jointRecovery_of_entireLaw hEL source hUI) hS b E hb hb' hE

end BlockBand.Critical.Assembly
