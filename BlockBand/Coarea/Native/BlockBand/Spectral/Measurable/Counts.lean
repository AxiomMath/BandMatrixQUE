module

public import BlockBand.Coarea.Native.BlockBand.Spectral.Measurable.OrderedSpectrum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable Hermitian eigenvalue counts and inertia

Multiplicity-counted eigenvalue counts in Borel sets and the strictly negative
count `N_R(E)` (inertia) are Borel-measurable functions of a Hermitian matrix.
This measurability is needed for the random spectral constructions of the paper.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

universe u

/-- The multiplicity-counted number of increasing ordered eigenvalues in a
Borel set is a Borel-measurable `Nat`-valued function on the Hermitian
subtype. -/
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

/-- The strictly-negative inertia used in the Schur data is Borel measurable.  Its codomain is `Nat`, multiplicity is retained, and a
zero eigenvalue is excluded by the strict set `Set.Iio 0`. -/
theorem measurable_inertia
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : HermitianMatrix ι => inertia A) := by
  simpa only [inertia_def] using
    (measurable_eigenCount (ι := ι) (Set.Iio 0) measurableSet_Iio)

end CoareaNative.BlockBand
