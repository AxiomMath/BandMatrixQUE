module

public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.BridgeMeshPrekopaLeindlerProof
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Algebra.Order.Field.Pointwise
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Centered-interval rearrangement for scalar Prékopa–Leindler

This module isolates the equimeasurable-set step in the one-dimensional
rearrangement proof.  A set of finite Lebesgue measure is replaced by the closed
interval centered at zero having the same measure.  We prove exact volume
preservation, compute positive weighted sums of these intervals, and reduce the
centered-superlevel barycentric inclusion to the one-dimensional
Brunn–Minkowski estimate for the original superlevel sets.

The results here do **not** assume `ScalarPrekopaLeindler`, and they do not
contain its Cavalieri argument: arbitrary `ℝ≥0∞`-valued functions require
value/range truncation, while superlevel sets of infinite volume require spatial
(or finite-superlevel) truncation followed by a monotone limit.  These steps are
in `scalarPrekopaLeindler_of_weightedBrunnMinkowski`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PrekopaNative.BlockBand

open MeasureTheory Set
open scoped ENNReal Pointwise

/-- The one-dimensional weighted Brunn–Minkowski inequality
`a |A| + b |B| ≤ |a A + b B|` for two sets, as needed by centered rearrangement. -/
def WeightedBrunnMinkowskiData (A B : Set ℝ) (a b : ℝ) : Prop :=
  a * volume.real A + b * volume.real B ≤ volume.real (a • A + b • B)

end PrekopaNative.BlockBand
