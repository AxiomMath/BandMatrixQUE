module

public import BlockBand.DeterminantScore.RbarMoment
public import BlockBand.DeterminantScore.PairRowMoment

/-!
# The determinant score theorem

`determinantScore_holds`: the determinant score theorem, composed from
`RbarMoment.determinantScore_of_corner` and `ScoreMoments.pairRowMoment_holds`. Hypotheses:
`CoareaContract` and `PhysicalMinorTailStatement` (the latter is proved conditionally as
`MinorTailInverse.physicalMinorTail_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.DeterminantScoreHolds

open BlockBand.Internal.Contracts.CoareaPalm

/-- **The determinant score theorem** (both clauses) from `CoareaContract` and the physical
minor tail statement. -/
theorem determinantScore_holds (hC : CoareaContract) (hMT : PhysicalMinorTailStatement) :
    DeterminantScoreStatement :=
  RbarMoment.determinantScore_of_corner hC hMT (ScoreMoments.pairRowMoment_holds hC)

end BlockBand.DeterminantScore.DeterminantScoreHolds
