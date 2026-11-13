module

public import BlockBand.SourceProcess.PhysApprox.B3Reduce
public import BlockBand.SourceProcess.PhysApprox.Assembly
public import BlockBand.SourceProcess.ComplexSplit.Holds
public import BlockBand.Transmission.LawForced.LawHolds

/-!
# The identification from the capped conditional limit

The closed limit identification and the closed limit laws follow from `ComplexCapCondLimit`, and the
composition of `complexPhysicalApproximationFreq_of_targets` goes through with `ComplexCapCondLimit`
in place of the closed limit law (b3).

* `complexPhysicalApproximationFreq_of_capCond`: the frequent-`h` physical approximation from
  `TargetT1`–`TargetT7`, the hypotheses and `ComplexCapCondLimit`, without `TargetT8`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct

/-- R1 with the input hypotheses: `ComplexCapCondLimit` ⇒ (b2). -/
theorem complexClosedLimitIdentification_of_capCond_baseContracts (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hLp : Inputs.GaussianLpGradient)
    (hP : Inputs.GaussianPoincare) (hEx : ComplexModelExists) (hC : ComplexCapCondLimit) :
    ComplexClosedLimitIdentification :=
  complexClosedLimitIdentification_of_capCond
    (Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP) hEx
    ComplexSplit.complexFiniteUniqueness_holds hC

/-- (b3, stopped) from `ComplexCapCondLimit` and the input hypotheses. -/
theorem complexClosedLimitLawStopped_of_capCond_baseContracts (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hLp : Inputs.GaussianLpGradient)
    (hP : Inputs.GaussianPoincare) (hEx : ComplexModelExists) (hC : ComplexCapCondLimit) :
    ComplexClosedLimitLawStopped :=
  complexClosedLimitLawStopped_of_identification
    (complexClosedLimitIdentification_of_capCond_baseContracts hMT hGA hLp hP hEx hC)

/-- (b3) from `ComplexCapCondLimit`, `ComplexTestedOfFinite` and the input hypotheses. -/
theorem complexClosedLimitLaw_of_capCond_baseContracts (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hLp : Inputs.GaussianLpGradient)
    (hP : Inputs.GaussianPoincare) (hEx : ComplexModelExists) (hC : ComplexCapCondLimit)
    (hT : ComplexTestedOfFinite) : ComplexClosedLimitLaw :=
  complexClosedLimitLaw_of_identification
    (complexClosedLimitIdentification_of_capCond_baseContracts hMT hGA hLp hP hEx hC) hT

/-- **`TargetT9` without `TargetT8`**: `TargetT1`–`TargetT4`, `TargetTL`, `TargetT6`, `TargetT7`,
the hypotheses, `KolmogorovConjugate`, `ComplexModelExists` and `ComplexCapCondLimit` give
`ComplexPhysicalApproximationFreq` (`TargetTL`, `TargetT4`, `TargetT3`, `TargetT2`, `TargetT1` give
(a); R1, `TargetT7`, `TargetT6` give (b); then `complexPhysicalApproximationFreq_of_pins`).
-/
theorem complexPhysicalApproximationFreq_of_capCond (t1 : TargetT1) (t2 : TargetT2)
    (t3 : TargetT3) (t4 : TargetT4) (tL : TargetTL) (t6 : TargetT6) (t7 : TargetT7)
    (hMT : Layers.MatchedTracesContract) (hGA : Layers.GaussianAbsorptionContract)
    (hSR : Layers.ScalarRecursionContract) (hLp : Inputs.GaussianLpGradient)
    (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate) (hEx : ComplexModelExists)
    (hC : ComplexCapCondLimit) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq := by
  have hL := tL hMT hGA hSR hLp hP
  exact complexPhysicalApproximationFreq_of_pins
    (t1 hMT hGA hSR hLp hP (t2 hMT hGA hSR hLp hP hK hL) (t3 hMT hGA hSR hLp hP hL (t4 hL)))
    (t6 hMT hGA hSR hLp hP
      (t7 (complexClosedLimitIdentification_of_capCond_baseContracts hMT hGA hLp hP hEx hC)))

end BlockBand.SourceProcess.PhysApprox.B3
