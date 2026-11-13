module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.FluctuationMoments
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Probability.Independence.Integration

/-!
# Product-coordinate analysis for the Gaussian ER expansion

This module supplies the measure-theoretic product-coordinate facts that are
available from the Gaussian-ring law without any local-law input.  A single
upper-triangular matrix entry is separated from all remaining upper entries;
mutual independence gives independence of the two finite tuples.

These statements are uniform in `Params`, so the finite index type, and hence
the matrix dimension, may vary with an external parameter.  They do not assume
stochastic domination, a moment recursion, self-consistency, or a local law.

Source: Erdős–Riabov, arXiv:2506.06441v1, finite-coordinate Gaussian
integration by parts in the fluctuation-averaging argument for Theorem 3.3.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERProductCoordinateAnalysis

open MeasureTheory ProbabilityTheory

/-!
## Generic separation of one coordinate from a finite product family
-/

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {μ : Measure Ω} {β : ι → Type*} [mβ : ∀ i, MeasurableSpace (β i)]

/-- The one-coordinate tuple, kept as a subtype-indexed dependent function so
that it is directly compatible with `iIndepFun.indepFun_finset`. -/
def singletonTuple (f : ∀ i, Ω → β i) (i : ι) :
    Ω → ((j : ({i} : Finset ι)) → β j) :=
  fun ω j => f j ω

/-- The tuple of all coordinates except `i`. -/
def complementTuple (f : ∀ i, Ω → β i) (i : ι) :
    Ω → ((j : (Finset.univ.erase i : Finset ι)) → β j) :=
  fun ω j => f j ω

/-- A member of a mutually independent finite family is independent of the
tuple of every other member.  This is the finite product-coordinate
factorization needed before applying one-dimensional Gaussian IBP. -/
theorem singletonTuple_indep_complementTuple
    (f : ∀ i, Ω → β i) (i : ι)
    (hf : iIndepFun f μ) (hmeas : ∀ j, Measurable (f j)) :
    IndepFun (singletonTuple f i) (complementTuple f i) μ := by
  apply iIndepFun.indepFun_finset ({i} : Finset ι) (Finset.univ.erase i)
  · simp
  · exact hf
  · exact hmeas

/-- Both coordinate tuples are measurable. -/
theorem measurable_singletonTuple_complementTuple
    (f : ∀ i, Ω → β i) (i : ι) (hmeas : ∀ j, Measurable (f j)) :
    Measurable (singletonTuple f i) ∧ Measurable (complementTuple f i) := by
  constructor
  · apply Measurable.of_eval
    intro j
    exact hmeas j
  · apply Measurable.of_eval
    intro j
    exact hmeas j

/-!
## Analytic closure lemmas for finite IBP expansions
-/

/-!
## Specialization to the Gaussian block-band ring
-/

local instance (p : Params) : NeZero p.n := p.nNeZero
local instance (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance (p : Params) : Fintype (UpperPair p) := Fintype.ofFinite _
local instance (p : Params) : DecidableEq (UpperPair p) := Classical.decEq _

/-- The random upper-entry family appearing in the Gaussian-ring law. -/
def upperEntryFamily {p : Params} (M : Law p) : UpperPair p → M.Ω → ℂ :=
  fun q ω => M.H ω q.1.1 q.1.2

/-- Every upper entry is measurable as a complex random variable. -/
theorem measurable_upperEntryFamily {p : Params} (M : Law p) (q : UpperPair p) :
    Measurable (upperEntryFamily M q) :=
  M.measurable_entry q.1.1 q.1.2

/-- An upper-triangular Gaussian-ring entry is independent of the tuple
of all other upper entries; this follows from `Law.upper_independent`. -/
theorem Law.upperEntry_indep_complement
    {p : Params} (M : Law p) (q : UpperPair p) :
    IndepFun (singletonTuple (upperEntryFamily M) q)
      (complementTuple (upperEntryFamily M) q) M.P := by
  exact singletonTuple_indep_complementTuple (upperEntryFamily M) q
    M.upper_independent (measurable_upperEntryFamily M)

end ERProductCoordinateAnalysis
end GaussianRing
end ERNative.BlockBand
