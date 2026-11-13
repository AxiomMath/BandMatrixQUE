module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.GaussianPoincareIntermediate

/-!
# Sharp finite-product variance tensorization for ER Gaussian coordinates

This additive module supplies the measure-theoretic Efron–Stein step needed
between the sharp scalar Gaussian Poincare theorem and the concrete ER upper
coordinate product law.  All constants are exactly one.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERTensorizedGaussianPoincare

open Matrix MeasureTheory ProbabilityTheory
open ERProfile ERConcrete ERGaussianCoordinate ERResolventMomentIBP
open ERSharpCoordinateIBP ERActualWardBound
open ERGaussianPoincareIntermediate
open scoped BigOperators NNReal RealInnerProductSpace

local instance (p : Params) : NeZero p.n := p.nNeZero
local instance (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance (p : Params) : Fintype (UpperPair p) := Fintype.ofFinite _
local instance (p : Params) : DecidableEq (UpperPair p) := Classical.decEq _

/-- Nondependent evaluation form of `Function.update`, specialized before the
`UpperPair` subtype is unfolded by matrix reconstruction simplification. -/
@[simp] theorem upperPair_update_apply
    {p : Params} (u : UpperPair p → ℂ) (q : UpperPair p) (v : ℂ)
    (q' : UpperPair p) :
    Function.update u q v q' = if q' = q then v else u q' :=
  Function.update_apply _ _ _ _

/-- Diagonal upper pairs are canonically and bijectively indexed by sites. -/
theorem sum_upperPair_diagonal_eq
    {p : Params} {R : Type*} [AddCommMonoid R]
    (f : Site p.n p.W → R) :
    (∑ q ∈ (Finset.univ.filter fun q : UpperPair p =>
        q.1.1 = q.1.2), f q.1.1) = ∑ a, f a := by
  symm
  apply Finset.sum_bij (fun a _ => diagonalUpperPair p a)
  · intro a _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  · intro a₁ _ a₂ _ h
    have := congrArg (fun q : UpperPair p => q.1.1) h
    simpa [diagonalUpperPair] using this
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨q.1.1, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    simp only [diagonalUpperPair_val]
    exact Prod.ext rfl hq
  · intro a _
    simp [diagonalUpperPair]

end ERTensorizedGaussianPoincare
end GaussianRing
end ERNative.BlockBand
