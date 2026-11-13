module

public import BlockBand.SourceProcess.WienerRecovery.BrownianOnceChargedInsideBoxCore

/-!
# Continuity at empty for the Brownian cylinder content

This module proves the continuity-at-empty condition used by the Carathéodory
construction of scalar Wiener measure.  The once-charged compact-core condition
`BrownianCylinderOnceChargedCompactCore` holds unconditionally, and the
compact-intersection theorem for it gives continuity at empty for
`brownianCylinderContent`.

No continuity hypothesis is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH
namespace BrownianCylinderContinuityAtEmptyClosure

open ScalarWienerMeasureConstruction
open BrownianNestedCompactCoreProof
open BrownianOnceChargedInsideBoxCore

/-- The exact Brownian cylinder content is continuous at the empty set along
every decreasing sequence of measurable cylinders.

The only intermediate input is `BrownianCylinderOnceChargedCompactCore`, which holds
unconditionally. -/
theorem brownianCylinderContinuityAtEmpty :
    BrownianCylinderContinuityAtEmpty :=
  brownianCylinderContinuityAtEmpty_of_onceChargedCompactCore
    brownianCylinderOnceChargedCompactCore

end BrownianCylinderContinuityAtEmptyClosure
end BlockBand.SourceProcess.WienerRecovery.CEH
