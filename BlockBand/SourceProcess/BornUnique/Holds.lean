module

public import BlockBand.SourceProcess.BornUnique.Reduce
public import BlockBand.SourceProcess.BornUnique.Concat
public import BlockBand.SourceProcess.BornUnique.SegmentProof

/-!
# `ModelUnique` from the stopped law and the restart property

`modelUnique_of_pins` derives `ModelUnique` from the two hypotheses `BornStoppedLaw` and
`BornRestart`, via `BornSegmentStep` and `BornGramLawUnique`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornUnique

open BlockBand.SourceProcess.SourceProcessLaw

/-- **`ModelUnique` from `BornStoppedLaw` and `BornRestart`.** -/
theorem modelUnique_of_pins (hSt : BornStoppedLaw) (hR : BornRestart) : ModelUnique :=
  modelUnique_of_bornGramLawUnique (bornGramLawUnique_of_segmentStep (bornSegmentStep_of hSt hR))

end BlockBand.SourceProcess.BornUnique
