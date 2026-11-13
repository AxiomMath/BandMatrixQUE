module

public import BlockBand.SourceProcess.PhysApprox.B3BridgesFinal7
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramPassMain
public import BlockBand.SourceProcess.PhysApprox.IdentK.Main

/-!
# A reduced final assembly, eighth version

`complexPhysicalApproximationFreq_reduced8`: the frequent-`h` physical approximation from the
contract hypotheses, `KolmogorovConjugate` and `GramPassLocalLarge`. Here `CapIdentGramGen` comes
from `IdentGram.Pass.capIdentGramGen_of_large` and `CapIdentKDoubleGen` from
`IdentGram.IdentK.capIdentKDoubleGen_holds`. (`GramPassLocalLarge` is proved, as
`IdentGram.Local.gramPassLocalLarge_holds`.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts
open BlockBand.SourceProcess.ComplexSourceLaw

/-- **The reduced final assembly, eighth version**: `ComplexPhysicalApproximationFreq` from the
input hypotheses, `KolmogorovConjugate` and `GramPassLocalLarge`. -/
theorem complexPhysicalApproximationFreq_reduced8 (hMT : Layers.MatchedTracesContract)
    (hGA : Layers.GaussianAbsorptionContract) (hSR : Layers.ScalarRecursionContract)
    (hLp : Inputs.GaussianLpGradient) (hP : Inputs.GaussianPoincare) (hK : KolmogorovConjugate)
    (hLoc : IdentGram.Pass.GramPassLocalLarge) :
    BlockBand.SourceProcess.ComplexFreq.ComplexPhysicalApproximationFreq :=
  complexPhysicalApproximationFreq_reduced7 hMT hGA hSR hLp hP hK
    (IdentGram.Pass.capIdentGramGen_of_large hLoc) IdentGram.IdentK.capIdentKDoubleGen_holds

end BlockBand.SourceProcess.PhysApprox.B3
