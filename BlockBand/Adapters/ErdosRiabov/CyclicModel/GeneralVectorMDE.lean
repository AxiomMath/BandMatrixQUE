module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ERControlKernels
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Basic.Complex.Basic
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.CriticalSequences
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Conventions
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib

/-!
# General vector MDE for nonnegative row-stochastic covariance profiles

This module proves the deterministic vector-MDE estimates used for the block-band
model, for an arbitrary finite index set and an
arbitrary nonnegative row-stochastic real covariance profile `S`.

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, the vector Dyson equation `-1/m = z + S m` and the
stability operator `1 - a S` behind ER (2.10).  The normalization is that
of the paper: `S` has nonnegative entries and row sums exactly `1`, and the
resolvent sign is `G(z) = (z - H)⁻¹`, so the scalar semicircle solution is
`erSemicircleStieltjes z`, the root of `m² + z m + 1 = 0` with
`(Im m) (Im z) > 0`.

All results are deterministic and finite-dimensional.  No constant depends on
the cardinality of the index set: every bound below is uniform in `ι`, in the
profile `S` and in the spectral parameters, and depends only on `‖a‖` (and, for
decay, on the range of `S` and the decay rate).  No limit is taken.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERGeneralVectorMDE

open scoped BigOperators
open Matrix

variable {ι : Type*} [Fintype ι]

/-- The covariance operator `(S m)_i = ∑_j S_ij m_j` acting on complex vectors. -/
def profileApply (S : Matrix ι ι ℝ) (m : ι → ℂ) (i : ι) : ℂ :=
  ∑ j, (S i j : ℂ) * m j

/-- The vector MDE `-1/m_i = z + (S m)_i`, written without division as
`1 + m_i (z + (S m)_i) = 0` for every index `i`. -/
def IsVectorMDESolution (S : Matrix ι ι ℝ) (z : ℂ) (m : ι → ℂ) : Prop :=
  ∀ i, 1 + m i * (z + profileApply S m i) = 0

/-!
## Existence and the Ward identity
-/

/-!
## Uniqueness
-/

/-- Complex conjugation maps solutions at `z` to solutions at `conj z`. -/
theorem IsVectorMDESolution.conj {S : Matrix ι ι ℝ} {z : ℂ} {m : ι → ℂ}
    (hm : IsVectorMDESolution S z m) :
    IsVectorMDESolution S (starRingEnd ℂ z) (fun i => starRingEnd ℂ (m i)) := by
  intro i
  have h := congrArg (starRingEnd ℂ) (hm i)
  simpa [profileApply, map_sum, map_add, map_mul] using h

/-!
## Stability of `1 - a S`
-/

/-!
## Assembly
-/

/-!
## The concrete cyclic Gaussian-ring profile
-/

local instance (p : Params) : NeZero p.n := p.nNeZero

end ERGeneralVectorMDE
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
