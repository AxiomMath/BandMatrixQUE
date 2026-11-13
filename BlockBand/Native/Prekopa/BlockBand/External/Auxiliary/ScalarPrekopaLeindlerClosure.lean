module

public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.MeasurableWeightedBrunnMinkowski

/-!
# Unconditional scalar Prékopa–Leindler inequality

This module closes the scalar analytic base used by the finite-dimensional
bridge-mesh tensorization.  The one-dimensional measurable weighted
Brunn–Minkowski theorem supplies the sole residual input to the truncation and
Cavalieri assembly, yielding `ScalarPrekopaLeindler` with no assumptions or
callbacks.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PrekopaNative.BlockBand

open MeasureTheory Set
open scoped ENNReal Pointwise

/-- The canonical unconditional measurable weighted Brunn–Minkowski input for
the scalar Prékopa–Leindler assembly. -/
theorem measurableWeightedBrunnMinkowski : MeasurableWeightedBrunnMinkowski := by
  intro A B hA hB hAfin hBfin hAn hBn a b ha hb hab
  exact ennreal_weightedBrunnMinkowski hA hB hAfin hBfin hAn hBn ha hb hab

/-- The unconditional one-dimensional scalar Prékopa–Leindler inequality for
measurable `ℝ≥0∞`-valued functions and positive barycentric weights. -/
theorem scalarPrekopaLeindler : ScalarPrekopaLeindler :=
  scalarPrekopaLeindler_of_weightedBrunnMinkowski
    measurableWeightedBrunnMinkowski

end PrekopaNative.BlockBand
