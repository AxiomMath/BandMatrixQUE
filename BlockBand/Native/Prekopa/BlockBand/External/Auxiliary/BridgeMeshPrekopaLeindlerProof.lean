module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The scalar Prékopa–Leindler inequality

This module states `ScalarPrekopaLeindler`, the one-dimensional three-function
Prékopa–Leindler inequality for Lebesgue measure, the analytic base case of
Prékopa–Leindler on finite bridge meshes.  It is proved as `scalarPrekopaLeindler`
and tensorized to every finite Cartesian power of Lebesgue measure by
`measurePrekopaLeindler_euclidean_pi`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PrekopaNative.BlockBand

open MeasureTheory Set
open scoped ENNReal

/-- The classical one-dimensional Prékopa–Leindler inequality for Lebesgue measure:
for measurable `f, g, h ≥ 0`, `a, b > 0` with `a + b = 1` and
`f x ^ a * g y ^ b ≤ h (a x + b y)`, one has `(∫ f)^a (∫ g)^b ≤ ∫ h`.  It is proved
by the one-dimensional layer-cake/rearrangement argument as `scalarPrekopaLeindler`. -/
def ScalarPrekopaLeindler : Prop :=
  ∀ (f g h : ℝ → ℝ≥0∞),
    Measurable f → Measurable g → Measurable h →
    ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      (∀ x y, f x ^ a * g y ^ b ≤ h (a * x + b * y)) →
      (∫⁻ x, f x) ^ a * (∫⁻ y, g y) ^ b ≤ ∫⁻ z, h z

end PrekopaNative.BlockBand
