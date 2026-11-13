module

public import BlockBand.Native.PSSS.BlockBand.Spectral.Measurable.OrderedSpectrum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable Hermitian eigenvalue counts

The multiplicity-counted number of eigenvalues of a Hermitian matrix in a Borel set is a Borel
measurable function of the matrix.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand

universe u

/-- The multiplicity-counted number of eigenvalues in a Borel set is a Borel-measurable
`ℕ`-valued function on Hermitian matrices. -/
theorem measurable_eigenCount
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (s : Set Real) (hs : MeasurableSet s) :
    Measurable (fun A : HermitianMatrix ι => eigenCount A s) := by
  classical
  simp only [eigenCount, Finset.card_filter]
  apply Finset.measurable_sum
  intro i _hi
  apply Measurable.ite
  · exact hs.preimage (measurable_orderedEigenvalue i)
  · exact measurable_const
  · exact measurable_const

/-- Multiplicity-counted eigenvalue counts in a closed interval are
Borel-measurable and remain `Nat`-valued.  Both endpoints are included, as in
`Set.Icc`; no simple-spectrum or boundary-avoidance hypothesis is imposed. -/
theorem measurable_eigenCount_Icc
    {ι : Type u} [Fintype ι] [DecidableEq ι] (a b : Real) :
    Measurable (fun A : HermitianMatrix ι =>
      eigenCount A (Set.Icc a b)) :=
  measurable_eigenCount (Set.Icc a b) measurableSet_Icc

end PSSSNative.BlockBand
