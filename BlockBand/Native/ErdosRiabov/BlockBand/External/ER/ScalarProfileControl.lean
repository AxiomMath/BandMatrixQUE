module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ProfileAnalytic
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.PhysicalKernelBridge
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Elementary clauses for the explicit scalar cyclic ER control

This module proves the monotonicity clause of the seven Erdős–Riabov analytic-control
conditions for the explicit scalar cyclic control of the paper.

The decay exponent is required to be nonnegative.  This is the sign relevant
for the corrected nearest-neighbour support branch: increasing the spectral
height decreases the localization length and therefore strengthens, rather
than reverses, exponential decay.  All statements are uniform in the ring
length and its parity.

Source: Erdős–Riabov, Proposition 2.8(i), Definition 2.4(ii)--(iv), and the scalar
profile lemma of the paper.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
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

/-- Reflect an anchored endpoint into the canonical half-cycle. -/
def endpointReflection (p : Params) (z : ZMod p.n) : ZMod p.n :=
  if 2 * z.val ≤ p.n then z else -z

@[simp] theorem endpointReflection_val (p : Params) (z : ZMod p.n) :
    (endpointReflection p z).val = min z.val (p.n - z.val) := by
  by_cases h : 2 * z.val ≤ p.n
  · rw [endpointReflection, ite_eq_left h, min_eq_left]
    omega
  · have hz : z ≠ 0 := by
      intro hz
      subst z
      simp at h
    rw [endpointReflection, ite_eq_right h, ZMod.neg_val, ite_eq_right hz,
      min_eq_right]
    omega

/-- Equal half-rate exponential weight for the two cyclic distances from
`0` to `d` through the representative `k`. -/
def cyclicHalfRateWeight (N d : ℕ) (ell : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-((min k (N - k) : ℕ) : ℝ) / (2 * ell)) *
    Real.exp (-((min (max k d - min k d)
      (N - (max k d - min k d)) : ℕ) : ℝ) / (2 * ell))

/-- Unequal half-rate cyclic weight.  The first distance retains `ell₂` and
the output leg retains `ell₁`; this distinction is required by the nearby
ER-bootstrap branch. -/
def cyclicTwoRateWeight (N d : ℕ) (ell₂ ell₁ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-((min k (N - k) : ℕ) : ℝ) / (2 * ell₂)) *
    Real.exp (-((min (max k d - min k d)
      (N - (max k d - min k d)) : ℕ) : ℝ) / (2 * ell₁))

/-- The unequal-rate weight has a removable equal-rate limit, definitionally
recovering the previous parity-aware weight. -/
@[simp] theorem cyclicTwoRateWeight_same (N d : ℕ) (ell : ℝ) (k : ℕ) :
    cyclicTwoRateWeight N d ell ell k =
      cyclicHalfRateWeight N d ell k := rfl

/-- Interval transfer for the floor ratio.  All transcendental work is
isolated in the explicit lower bound `hExp`; the remaining dependence on the
localization length is monotone. -/
theorem antipode_floor_ratio_of_interval {m : ℕ}
    {ell lower upper L R : ℝ}
    (hlower : 0 < lower) (hL : 0 < L)
    (hlo : lower ≤ ell) (hup : ell ≤ upper)
    (hExp : R * L ^ 4 / lower ^ 2 ≤
      Real.exp ((m : ℝ) / (2 * upper))) :
    R * Real.exp (-(m : ℝ) / (2 * ell)) ≤
      ell ^ 2 * L⁻¹ ^ 4 := by
  have hell : 0 < ell := hlower.trans_le hlo
  have hupper : 0 < upper := hell.trans_le hup
  have hexponent :
      (m : ℝ) / (2 * upper) ≤ (m : ℝ) / (2 * ell) := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg m)
      (by positivity) (by linarith)
  have hexp : R * L ^ 4 / lower ^ 2 ≤
      Real.exp ((m : ℝ) / (2 * ell)) :=
    hExp.trans (Real.exp_le_exp.mpr hexponent)
  have hlowerSq : lower ^ 2 ≤ ell ^ 2 :=
    (sq_le_sq₀ hlower.le hell.le).2 hlo
  have hpos : 0 < Real.exp ((m : ℝ) / (2 * ell)) := Real.exp_pos _
  rw [show -(m : ℝ) / (2 * ell) =
    -((m : ℝ) / (2 * ell)) by ring, Real.exp_neg]
  rw [mul_inv_le_iff₀ hpos]
  calc
    R ≤ (R * L ^ 4 / lower ^ 2) * (lower ^ 2 * L⁻¹ ^ 4) := by
      field_simp [ne_of_gt hlower, ne_of_gt hL]
      exact le_rfl
    _ ≤ Real.exp ((m : ℝ) / (2 * ell)) *
        (lower ^ 2 * L⁻¹ ^ 4) := by
      gcongr
    _ ≤ Real.exp ((m : ℝ) / (2 * ell)) *
        (ell ^ 2 * L⁻¹ ^ 4) := by gcongr
    _ = (ell ^ 2 * L⁻¹ ^ 4) *
        Real.exp ((m : ℝ) / (2 * ell)) := by ring

end ERScalarProfileControl
end GaussianRing
end ERNative.BlockBand
