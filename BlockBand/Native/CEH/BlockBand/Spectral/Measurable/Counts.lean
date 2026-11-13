module

public import BlockBand.Native.CEH.BlockBand.Spectral.Measurable.OrderedSpectrum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable Hermitian eigenvalue counts and inertia

Multiplicity-counted eigenvalue counts in a Borel set, in a closed interval, and the
strictly negative inertia `N_R(E)` of the Schur data are Borel measurable `ℕ`-valued functions of
a Hermitian matrix.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

universe u

/-- The multiplicity-counted number of increasing ordered eigenvalues in a
Borel set is a Borel-measurable `ℕ`-valued function on the Hermitian subtype. -/
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

/-- The strictly-negative inertia of the Schur data is Borel measurable. Its codomain is `ℕ`,
multiplicity is retained, and a zero eigenvalue is excluded by the strict set `Set.Iio 0`. -/
theorem measurable_inertia
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : HermitianMatrix ι => inertia A) := by
  simpa only [inertia_def] using
    (measurable_eigenCount (ι := ι) (Set.Iio 0) measurableSet_Iio)

end CEHNative.BlockBand
