module

public import BlockBand.Critical.RelativeVectors.Comparison
public import BlockBand.Critical.RelativeVectors.Decorated

/-!
# The relative mixed-vector theorem

`relativeMixedVectorsStatement_of_inputs`: `RelativeMixedVectorsStatement` (main clause and
decorated-sine clause) from `relativeMixedVectors_comparison` (main clause; hypotheses
`RelativeDuhamelStatement`, `ReferenceFlowStatement`, `CoarseRelativeContract`,
`GaussianLpGradient`, `SpectralGoodEventContract`, `RelativeLocalizationContract`,
`DysonBrownianMotion`) and `relativeMixedVectorsStatement_of_comparison` (decorated clause, from
`PSSS.SourceContract` and `Inputs.ExternalSine`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.External

/-- **The relative mixed-vector theorem** (both clauses). -/
theorem relativeMixedVectorsStatement_of_inputs
    (hD : ∀ N r, RelativeDuhamelStatement N r)
    (hRF : ∀ N r, ReferenceFlowStatement N r)
    (hCR : CoarseRelativeContract) (hLp : GaussianLpGradient)
    (hSG : SpectralGoodEventContract) (hRL : RelativeLocalizationContract)
    (hDBM : ∀ N, DysonBrownianMotion N)
    (source : PSSS.SourceContract.{0}) (hES : BlockBand.Internal.Contracts.Inputs.ExternalSine) :
    RelativeMixedVectorsStatement :=
  relativeMixedVectorsStatement_of_comparison
    (relativeMixedVectors_comparison hD hRF hCR hLp hSG hRL hDBM) source hES

end BlockBand.Critical.RelativeVectors
