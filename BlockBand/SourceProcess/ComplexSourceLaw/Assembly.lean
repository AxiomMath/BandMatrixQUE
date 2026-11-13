module

public import BlockBand.SourceProcess.ComplexSourceLaw.Limit
public import BlockBand.SourceProcess.ComplexSourceLaw.MomentsLimit
public import BlockBand.SourceProcess.ComplexSourceLaw.Sequence

/-!
# Assembly of the complex source law contract

`complexSourceLawContract_of hU hC hR hX : ComplexSourceLawContract`: the `limit` field from
`ComplexFiniteUniqueness` and `ComplexSourceConstruction` (`limit_of`), `moments` from
`RawTagMoments` (`moments_of_raw`), `rawTagMoments := hR` and `extendedSourceMoments := hX`.
The sequence form of the contract is `complexSourceLimitSequence_of`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open BlockBand.Internal.Contracts.TransmissionLaws

/-- **The complex source law theorem** `ComplexSourceLawContract` from `ComplexFiniteUniqueness`,
`ComplexSourceConstruction`, `RawTagMoments` and `ExtendedSourceMoments`. -/
theorem complexSourceLawContract_of (hU : ComplexFiniteUniqueness)
    (hC : ComplexSourceConstruction) (hR : RawTagMoments) (hX : ExtendedSourceMoments) :
    ComplexSourceLawContract where
  limit := limit_of hU hC
  moments := moments_of_raw hR
  rawTagMoments := hR
  extendedSourceMoments := hX

end BlockBand.SourceProcess.ComplexSourceLaw
