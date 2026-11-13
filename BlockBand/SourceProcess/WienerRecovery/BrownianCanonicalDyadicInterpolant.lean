module

public import BlockBand.SourceProcess.WienerRecovery.BrownianDyadicInterpolationCorrection

/-!
# Canonical raw-coordinate dyadic polygonal interpolants

This module defines the compact-horizon dyadic polygonal approximants explicitly.
They are written in the standard nodal hat basis: at level `n`, the coefficient of the
`j`-th hat is the unrestricted raw coordinate at `T * j / 2^n`.  Thus the construction
depends on only `2^n+1` measurable coordinates.

Continuity of every sample interpolant and measurability of the map into compact-path
space are proved below.  The other finite-dimensional facts about this fixed function
are collected in `BrownianCanonicalDyadicInterpolationFacts`: the Kronecker property of
the hats (hence the explicit edge-affine specification and uniqueness), the `n → n+1`
uniform-step containment in the level `n+1` bad event, and fixed-time almost-sure
convergence. They are proved as `brownianCanonicalDyadicInterpolationFacts`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped ENNReal NNReal Topology BigOperators
open Filter MeasureTheory ProbabilityTheory

namespace BrownianCanonicalDyadicInterpolant

open BrownianDyadicChainingClosure
open BrownianDyadicGaussianEnvelope
open BrownianDyadicCompactExtension
open BrownianDyadicInterpolationCorrection
open ScalarWienerMeasureConstruction

/-- The `j`-th node of the level-`n` dyadic mesh on `[0,T]`. -/
def dyadicNode (T : NNReal) (n : ℕ) (j : Fin (2 ^ n + 1)) : NNReal :=
  T * (j.1 : NNReal) / (2 ^ n : ℕ)

/-- The standard triangular hat centered at the `j`-th level-`n` node.  The formula
uses the normalized coordinate `2^n t / T`; division at `T=0` follows the ambient
field convention, while all Brownian applications below carry `0<T`. -/
def dyadicHat (T : NNReal) (n : ℕ) (j : Fin (2 ^ n + 1)) : CompactPath T where
  toFun t := max 0
    (1 - |(2 ^ n : ℝ) * (t.1 : ℝ) / (T : ℝ) - (j.1 : ℝ)|)
  continuous_toFun := by fun_prop

/-- The canonical level-`n` raw-coordinate polygonal interpolant, expressed as the
finite sum of nodal values times the corresponding triangular hats. -/
def canonicalRawDyadicInterpolant
    (T : NNReal) (ω : BrownianRawPath) (n : ℕ) : CompactPath T :=
  ∑ j : Fin (2 ^ n + 1),
    rawCoordinateProcess (dyadicNode T n j) ω • dyadicHat T n j

/-- Each canonical interpolant is a continuous compact path by construction. -/
theorem continuous_canonicalRawDyadicInterpolant
    (T : NNReal) (ω : BrownianRawPath) (n : ℕ) :
    Continuous (canonicalRawDyadicInterpolant T ω n) :=
  (canonicalRawDyadicInterpolant T ω n).continuous

/-- At a fixed level the canonical compact-path-valued interpolant is measurable:
it is a finite linear combination of measurable raw-coordinate evaluations with
fixed continuous hats. -/
theorem measurable_canonicalRawDyadicInterpolant (T : NNReal) (n : ℕ) :
    Measurable (fun ω : BrownianRawPath =>
      canonicalRawDyadicInterpolant T ω n) := by
  unfold canonicalRawDyadicInterpolant
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply (dyadicNode T n j)).smul measurable_const)

/-- Hence the canonical interpolants meet the almost-everywhere measurability field
for every raw Brownian measure, without using any regularity of raw sample paths. -/
theorem aemeasurable_canonicalRawDyadicInterpolant
    (hcont : BrownianCylinderContinuityAtEmpty) (T : NNReal) (n : ℕ) :
    AEMeasurable (fun ω : BrownianRawPath =>
      canonicalRawDyadicInterpolant T ω n) (brownianRawMeasure hcont) :=
  (measurable_canonicalRawDyadicInterpolant T n).aemeasurable

/-- Facts about the fixed nodal-hat construction (rather than an arbitrary sequence of
approximants): the deterministic Kronecker/affine calculation and the two probabilistic
consequences needed to instantiate `BrownianRawDyadicInterpolationData`. They are proved
as `brownianCanonicalDyadicInterpolationFacts` for `0 < T`. -/
structure BrownianCanonicalDyadicInterpolationFacts
    (hcont : BrownianCylinderContinuityAtEmpty) (T : NNReal) where
  isRawDyadicPiecewiseLinear : ∀ ω n,
    IsRawDyadicPiecewiseLinearInterpolant T ω n
      (canonicalRawDyadicInterpolant T ω n)
  unique_isRawDyadicPiecewiseLinear : ∀ ω n (f : CompactPath T),
    IsRawDyadicPiecewiseLinearInterpolant T ω n f →
      f = canonicalRawDyadicInterpolant T ω n
  badStep_subset : ∀ n : ℕ,
    {ω | compactDyadicModulus T n.succ <
      dist (canonicalRawDyadicInterpolant T ω n)
        (canonicalRawDyadicInterpolant T ω n.succ)} ⊆
      dyadicBadLevel rawCoordinateProcess T (compactDyadicModulus T) n.succ
  eval_tendsto : ∀ t : Set.Icc (0 : NNReal) T,
    ∀ᵐ ω ∂(brownianRawMeasure hcont),
      Tendsto (fun n => canonicalRawDyadicInterpolant T ω n t) atTop
        (𝓝 (rawCoordinateProcess t.1 ω))

/-- The canonical facts instantiate `BrownianRawDyadicInterpolationData` with the
nodal-hat interpolants as approximants. -/
def canonicalBrownianRawDyadicInterpolationData
    (hcont : BrownianCylinderContinuityAtEmpty) (T : NNReal)
    (facts : BrownianCanonicalDyadicInterpolationFacts hcont T) :
    BrownianRawDyadicInterpolationData hcont T where
  approximant := canonicalRawDyadicInterpolant T
  isRawDyadicPiecewiseLinear := facts.isRawDyadicPiecewiseLinear
  unique_isRawDyadicPiecewiseLinear := facts.unique_isRawDyadicPiecewiseLinear
  aemeasurable_approximant :=
    aemeasurable_canonicalRawDyadicInterpolant hcont T
  badStep_subset := facts.badStep_subset
  eval_tendsto := facts.eval_tendsto

/-- Given `BrownianCanonicalDyadicInterpolationFacts`, the Gaussian-envelope theorem
yields the measurable compact-path modification on `[0,T]`. -/
theorem exists_measurable_compactPath_modification_of_canonical_facts
    (hcont : BrownianCylinderContinuityAtEmpty) (T : NNReal) (hT : 0 < T)
    (facts : BrownianCanonicalDyadicInterpolationFacts hcont T) :
    ∃ F : BrownianRawPath → CompactPath T,
      Measurable F ∧
      (∀ᵐ ω ∂(brownianRawMeasure hcont),
        Tendsto (canonicalRawDyadicInterpolant T ω) atTop (𝓝 (F ω))) ∧
      ∀ t : Set.Icc (0 : NNReal) T,
        (fun ω => F ω t) =ᵐ[brownianRawMeasure hcont]
          rawCoordinateProcess t.1 := by
  simpa [canonicalBrownianRawDyadicInterpolationData] using
    exists_measurable_compactPath_modification_of_rawDyadic hcont T hT
      (canonicalBrownianRawDyadicInterpolationData hcont T facts)

end BrownianCanonicalDyadicInterpolant
end BlockBand.SourceProcess.WienerRecovery.CEH
