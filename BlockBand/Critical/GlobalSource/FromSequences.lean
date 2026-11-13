module

public import BlockBand.Internal.Contracts.TransmissionSequences
public import BlockBand.Critical.GlobalSource.SourceSequences

/-!
# The sampled source limit along every critical sequence

`complexSourceLimitAlongSequences_of_contract` derives `ComplexSourceLimitAlongSequences` from
`ComplexSourceLimitSequenceContract`, by applying its `everySequence` field along the identity
subsequence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open Filter
open BlockBand.Internal.Contracts.TransmissionSequences

/-- `ComplexSourceLimitAlongSequences` from the sequence form `ComplexSourceLimitSequenceContract`
(widths `W_j = j`, lengths `r_j = r j`). -/
theorem complexSourceLimitAlongSequences_of_contract (h : ComplexSourceLimitSequenceContract) :
    ComplexSourceLimitAlongSequences := by
  intro b hb0 hb1 E hE0 hE1 np τ m hτ hτpos hm T hT ν hν r hr Φ
  exact h.everySequence b hb0 hb1 E hE0 hE1 np τ m hτ hτpos hm T hT ν hν id r tendsto_id hr Φ

end BlockBand.Critical.GlobalSource
