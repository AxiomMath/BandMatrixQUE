module

public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.BridgeMeshPrekopaLeindlerProof
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Algebra.Order.Field.Pointwise

/-!
# Scalar Prékopa–Leindler: one-dimensional rearrangement core

This module formalizes the interval core of the one-dimensional layer-cake proof of
`ScalarPrekopaLeindler`.  Positive barycentric Minkowski sums of closed intervals are
computed exactly, their Lebesgue volumes satisfy the required weighted geometric-mean
bound, and the pointwise Prékopa hypothesis is transferred to a constant lower bound on
the resulting interval.

The rearrangement passage from arbitrary measurable superlevel sets to centered
intervals of the same measure and the ensuing Cavalieri argument are not in this module.
The Cavalieri lemma proved below is finite-valued, whereas
`ScalarPrekopaLeindler` allows arbitrary `ℝ≥0∞`-valued functions; the scalar theorem
also uses value/range truncation (and, where needed, spatial or finite-superlevel
truncation) together with a monotone limit passage.  No scalar
Prékopa–Leindler or marginal-convexity statement is assumed here.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PrekopaNative.BlockBand

open MeasureTheory Set
open scoped ENNReal Pointwise

/-- Cavalieri's layer-cake formula for an `ENNReal`-valued measurable function with
pointwise finite values, expressed using real thresholds.  This is the exact analytic
identity used after rearranging each superlevel set into a centered interval. -/
theorem ennreal_lintegral_eq_lintegral_superlevel_toReal
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (hfinite : ∀ x, f x ≠ ∞) :
    (∫⁻ x, f x) =
      ∫⁻ t in Ioi (0 : ℝ), volume {x : ℝ | t ≤ (f x).toReal} := by
  have hnonneg : 0 ≤ᵐ[volume] fun x => (f x).toReal :=
    Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg
  have hmeas : AEMeasurable (fun x => (f x).toReal) volume :=
    (ENNReal.measurable_toReal.comp hf).aemeasurable
  rw [← lintegral_eq_lintegral_meas_le volume hnonneg hmeas]
  apply lintegral_congr
  intro x
  exact (ENNReal.ofReal_toReal (hfinite x)).symm

end PrekopaNative.BlockBand
