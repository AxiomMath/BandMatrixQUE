module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ProfileAnalytic
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.PhysicalKernelBridge
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib

/-!
# Elementary clauses for the explicit scalar cyclic ER control

This module discharges the monotonicity clause of the seven-clause
Erdős–Riabov analytic-control contract for the paper's explicit scalar
cyclic control.

The decay exponent is required to be nonnegative.  This is the sign relevant
for the corrected nearest-neighbour support branch: increasing the spectral
height decreases the localization length and therefore strengthens, rather
than reverses, exponential decay.  All statements are uniform in the ring
length and its parity.

Source: Erdős–Riabov, Proposition 2.8(i), Definition 2.4(ii)--(iv), and the
scalar-profile lemma of the block-band paper.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERScalarProfileControl

open scoped BigOperators
open ERCyclicDecay ERCyclicSummation ERPhysicalBridge

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The flattened physical ring, represented as a width-one parameter object.
It is only an indexing device for reusing the parity-free cyclic geometric
sum; its coupling is the original fixed coupling. -/
def flattenedParams (p : Params) : Params :=
  Params.ofDimensions p.L 1 p.b (by
    unfold Conventions.ModelParameters.L Conventions.dimension
    exact p.n_ge_four.trans (Nat.le_mul_of_pos_right p.n p.W_pos))
    (by norm_num) p.b_pos p.b_lt_half

local instance (p : Params) : NeZero p.L := p.dimensionNeZero

/-- Row-major flattening, now viewed as a cyclic residue. -/
def flattenedSiteEquiv (p : Params) :
    Site p.n p.W ≃ ZMod (flattenedParams p).n := by
  change Site p.n p.W ≃ ZMod p.L
  exact p.siteIndexEquiv.trans (zmodValEquiv p.L).symm

@[simp] theorem flattenedSiteEquiv_val (p : Params) (x : Site p.n p.W) :
    (flattenedSiteEquiv p x).val = (p.siteIndexEquiv x).val := by
  change ((↑(p.siteIndexEquiv x).val : ZMod p.L)).val =
    (p.siteIndexEquiv x).val
  exact ZMod.val_natCast_of_lt (p.siteIndexEquiv x).isLt

/-- On positive heights, multiplying the localization length by the height
turns its two defining branches into `W√η` and `Lη`. -/
theorem erLocalizationLength_mul (p : Params) {η : ℝ} (hη : 0 < η) :
    erLocalizationLength p η * η =
      min ((p.W : ℝ) * Real.sqrt η) ((p.L : ℝ) * η) := by
  have hsqrt : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  rw [erLocalizationLength, min_mul_of_nonneg _ _ hη.le]
  congr 1
  field_simp
  nlinarith [Real.sq_sqrt hη.le]

/-- Every summand in the explicit cyclic control is nonnegative. -/
theorem erManuscriptCyclicControl_nonneg (p : Params) (a D η : ℝ)
    (hη : 0 < η)
    (x y : Site p.n p.W) :
    0 ≤ erManuscriptCyclicControl p a D η x y := by
  unfold erManuscriptCyclicControl
  have hℓ : 0 < erLocalizationLength p η := by
    unfold erLocalizationLength
    exact lt_min (div_pos p.real_W_pos (Real.sqrt_pos.2 hη)) p.real_L_pos
  -- The control has no floor summand.
  have := hℓ
  exact mul_nonneg (by positivity) (Real.exp_pos _).le

/-- Cyclic block distance is invariant under a common translation. -/
theorem cyclicBlockDistance_add_right (p : Params)
    (x y t : ZMod p.n) :
    cyclicBlockDistance p (x + t) (y + t) =
      cyclicBlockDistance p x y := by
  unfold cyclicBlockDistance orientedBlockDistance
  rw [show x + t - (y + t) = x - y by abel]

/-- Reflection preserves cyclic distance. -/
theorem cyclicBlockDistance_neg (p : Params) (x y : ZMod p.n) :
    cyclicBlockDistance p (-x) (-y) = cyclicBlockDistance p x y := by
  unfold cyclicBlockDistance orientedBlockDistance
  have hdiff : -x - -y = -(x - y) := by abel
  rw [hdiff, ZMod.neg_val]
  by_cases hzero : x - y = 0
  · rw [ite_eq_left hzero, hzero]
    simp
  · rw [ite_eq_right hzero]
    have hv : (x - y).val < p.n := (x - y).val_lt
    omega

end ERScalarProfileControl
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
