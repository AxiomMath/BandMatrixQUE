module

public import BlockBand.SourceProcess.BornStopped.Holds
public import BlockBand.SourceProcess.BornStopped.Extension

/-!
# The stopped born law from the extension hypothesis

`bornStoppedLaw_of_extension` derives `BornStoppedLaw` from `GramHorizonExtension`, through
`GramHorizonLaw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornStopped

open BlockBand.SourceProcess.BornUnique

/-- **`BornStoppedLaw` from `GramHorizonExtension`.** -/
theorem bornStoppedLaw_of_extension (hE : GramHorizonExtension) : BornStoppedLaw :=
  bornStoppedLaw_of_horizon (gramHorizonLaw_of_extension hE)

end BlockBand.SourceProcess.BornStopped
