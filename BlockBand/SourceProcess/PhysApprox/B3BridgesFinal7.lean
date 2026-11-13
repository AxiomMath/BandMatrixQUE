module

public import BlockBand.SourceProcess.PhysApprox.B3BridgesFinal6
public import BlockBand.SourceProcess.PhysApprox.B3FracMomStep4

/-!
# A reduced final assembly, seventh version

`complexPhysicalApproximationFreq_reduced7`: the frequent-`h` physical approximation from the
contract hypotheses, `KolmogorovConjugate`, `CapIdentGramGen` and `CapIdentKDoubleGen`; the
fractional trace moments `FarFracTraceMoments4` are supplied by
`FracMom.farFracTraceMomentsAt_four`. (`CapIdentKDoubleGen` is proved, as
`IdentGram.IdentK.capIdentKDoubleGen_holds`.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **The reduced final assembly, seventh version**: `ComplexPhysicalApproximationFreq` from the
input hypotheses, `KolmogorovConjugate`, `CapIdentGramGen` and `CapIdentKDoubleGen`. -/
theorem complexPhysicalApproximationFreq_reduced7 (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hGr : IdentGram.CapIdentGramGen) (hKDd : IdentGram.CapIdentKDoubleGen) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq :=
  complexPhysicalApproximationFreq_reduced6 hMT hGA hSR hLp hP hK hGr hKDd
    (FracMom.farFracTraceMomentsAt_four hMT hGA hLp hP)

end BlockBand.SourceProcess.PhysApprox.B3
