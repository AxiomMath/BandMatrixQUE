module

public import BlockBand.SourceProcess.PhysApprox.B3BridgesFinal8
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalMain

/-!
# The frequent-`h` physical approximation

`complexPhysicalApproximationFreq_holds`: under the five contract hypotheses
`MatchedTracesContract`, `GaussianAbsorptionContract`, `ScalarRecursionContract`,
`GaussianLpGradient`, `GaussianPoincare` and Kolmogorov's conjugate inequality
`KolmogorovConjugate`, the physical approximation `ComplexPhysicalApproximationFreq` holds. It is
`complexPhysicalApproximationFreq_reduced8` with `GramPassLocalLarge` supplied by
`IdentGram.Local.gramPassLocalLarge_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open BlockBand.Internal.Contracts

/-- **The frequent-`h` physical approximation** `ComplexPhysicalApproximationFreq`, from the five
input hypotheses and `KolmogorovConjugate` only. -/
theorem complexPhysicalApproximationFreq_holds (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare)
    (hK : BlockBand.SourceProcess.ComplexSourceLaw.KolmogorovConjugate) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq :=
  B3.complexPhysicalApproximationFreq_reduced8 hMT hGA hSR hLp hP hK
    B3.IdentGram.Local.gramPassLocalLarge_holds

end BlockBand.SourceProcess.PhysApprox
