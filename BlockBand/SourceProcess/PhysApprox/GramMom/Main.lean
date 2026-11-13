module

public import BlockBand.SourceProcess.PhysApprox.GramMom.B1Main
public import BlockBand.SourceProcess.PhysApprox.GramMom.B23Mom
public import BlockBand.SourceProcess.PhysApprox.GramMom.CondExpReplace

/-!
# The moment sums of the local Gram estimate

`GramMomSumSq`, `GramMomSumCube`, `GramMomSingle` and `CondExpReplace` hold; this file records
`gramMomSumCube_holds`, from `gramMomSumCube_of` and `gramMomSumSq_holds`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

/-- **`GramMomSumCube` holds.** -/
theorem gramMomSumCube_holds : GramMomSumCube := gramMomSumCube_of gramMomSumSq_holds

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
