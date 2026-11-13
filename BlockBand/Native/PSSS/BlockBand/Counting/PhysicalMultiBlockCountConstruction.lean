module

public import BlockBand.Native.PSSS.BlockBand.Analysis.ProjectedWegnerSchur
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Probability.IdentDistrib
public import BlockBand.Native.PSSS.BlockBand.Basic.Indices
public import BlockBand.Native.PSSS.BlockBand.Spectral.Ordered
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Interface
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Sequences
public import Mathlib.Probability.HasLaw

/-!
# Physical multi-block count construction

This module proves the elementary bound `eigenCount_le_dimension`: any eigenvalue count of a
Hermitian matrix is at most the dimension. The physical multi-block construction itself (the
normalized physical matrix, its cross-block background and the diagonal-block GUE law) is
developed in `CoareaNative.BlockBand.GaussianRing`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory Set

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Any eigenvalue count is bounded by the matrix dimension. -/
theorem eigenCount_le_dimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (s : Set ℝ) :
    eigenCount A s ≤ Fintype.card ι := by
  classical
  unfold eigenCount
  calc
    (Finset.univ.filter (fun i => orderedEigenvalue A i ∈ s)).card ≤
        (Finset.univ : Finset (Fin (Fintype.card ι))).card :=
      Finset.card_filter_le _ _
    _ = Fintype.card ι := by simp

end GaussianRing
end PSSSNative.BlockBand
