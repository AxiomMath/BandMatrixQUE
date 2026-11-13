module

public import BlockBand.Coarea.Native.BlockBand.Coarea.HermitianDiscriminantReal
public import BlockBand.Coarea.Native.BlockBand.Spectral.Measurable.OrderedSpectrum

/-!
# The full-measure simple-spectrum locus in Hermitian coordinates

This module packages the unconditional global measure-theoretic consequence of
`HermitianDiscriminantReal`: in the explicit real coordinate chart for complex
Hermitian matrices, the locus with separable characteristic polynomial is
Borel measurable and has full Lebesgue measure.  It also proves measurability
of the complete increasing ordered spectrum after reconstruction from these
coordinates.

This is the part of the global eigenpair atlas which is independent of choices
of eigenvector phase.  Mathlib's chosen `Matrix.IsHermitian.eigenvectorBasis`
is not supplied with a measurable-dependence theorem, and a single global
continuous eigenvector choice is obstructed by phase/projective topology.
Consequently this module makes no eigenvector or global coarea statement; the
projective eigenpair charts and their change of variables are treated separately
(`lintegral_fixedRankEigenpairIncidence_chart`,
`physicalExhaustiveCoareaPoleChartCover_exhaustive`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory

/-- The real finite-ordinal coordinate space used for complex Hermitian
`d × d` matrices. -/
abbrev HermitianCoordinateSpace (d : ℕ) :=
  Fin (Fintype.card (HermitianCoordinate d)) → ℝ

/-- Reconstruct a project `HermitianMatrix` from finite-ordinal real
coordinates. -/
def hermitianOfFinCoordinates (d : ℕ) (x : HermitianCoordinateSpace d) :
    HermitianMatrix (Fin d) :=
  hermitianOfCoordinates (x ∘ hermitianCoordinateEquivFin d)

/-- The simple-spectrum locus in the explicit real coordinate chart.  Here
"simple" means that the monic characteristic polynomial is separable; for a
complex Hermitian matrix this is precisely absence of repeated eigenvalues. -/
def hermitianSimpleSpectrumCoordinates (d : ℕ) :
    Set (HermitianCoordinateSpace d) :=
  {x | (hermitianOfFinCoordinates d x : Matrix (Fin d) (Fin d) ℂ).charpoly.Separable}

/-- The algebraic simple-spectrum locus is exactly the nonvanishing locus of
the real norm-square discriminant polynomial. -/
theorem hermitianSimpleSpectrumCoordinates_eq_polynomialSimpleLocus (d : ℕ) :
    hermitianSimpleSpectrumCoordinates d =
      polynomialSimpleLocus _ (hermitianDiscriminantNormSqFin d) := by
  ext x
  simp only [hermitianSimpleSpectrumCoordinates, hermitianOfFinCoordinates,
    hermitianOfCoordinates, Set.mem_ofPred_eq, polynomialSimpleLocus]
  rw [eval_hermitianDiscriminantNormSqFin]
  have hzero :
      MvPolynomial.eval (x ∘ hermitianCoordinateEquivFin d)
          (hermitianDiscriminantNormSq d) = 0 ↔
        ¬(hermitianMatrixOfCoordinates
          (x ∘ hermitianCoordinateEquivFin d)).charpoly.Separable := by
    rw [eval_hermitianDiscriminantNormSq_eq_zero_iff_discr, Matrix.discr]
    exact Polynomial.discr_eq_zero_iff_not_separable
      (Matrix.charpoly_monic _)
  simpa using (not_congr hzero).symm

/-- The simple-spectrum locus is Borel measurable in explicit real Hermitian
coordinates. -/
theorem measurableSet_hermitianSimpleSpectrumCoordinates (d : ℕ) :
    MeasurableSet (hermitianSimpleSpectrumCoordinates d) := by
  rw [hermitianSimpleSpectrumCoordinates_eq_polynomialSimpleLocus]
  exact measurableSet_polynomialSimpleLocus _ _

/-- The complement of the simple-spectrum locus has Lebesgue measure zero. -/
theorem volume_hermitianSimpleSpectrumCoordinates_compl (d : ℕ) :
    volume (hermitianSimpleSpectrumCoordinates d)ᶜ = 0 := by
  rw [hermitianSimpleSpectrumCoordinates_eq_polynomialSimpleLocus]
  exact volume_polynomialSimpleLocus_compl _ _
    (hermitianDiscriminantNormSqFin_ne_zero d)

/-- Reconstruction from finite-ordinal coordinates into the Hermitian subtype
is continuous. -/
theorem continuous_hermitianOfFinCoordinates (d : ℕ) :
    Continuous (hermitianOfFinCoordinates d) := by
  rw [continuous_induced_rng]
  change Continuous (fun x : HermitianCoordinateSpace d =>
    hermitianMatrixOfCoordinates (x ∘ hermitianCoordinateEquivFin d))
  change Continuous (fun x : HermitianCoordinateSpace d =>
    hermitianCoordinatesLinearMap d (x ∘ hermitianCoordinateEquivFin d))
  fun_prop

/-- Reconstruction from finite-ordinal coordinates into the Hermitian subtype
is Borel measurable. -/
theorem measurable_hermitianOfFinCoordinates (d : ℕ) :
    Measurable (hermitianOfFinCoordinates d) :=
  (continuous_hermitianOfFinCoordinates d).measurable

/-- The increasing ordered eigenvalue of any fixed rank is measurable as a
function of the explicit Hermitian coordinates. -/
theorem measurable_orderedEigenvalue_hermitianOfFinCoordinates
    (d : ℕ) (r : Fin (Fintype.card (Fin d))) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      orderedEigenvalue (hermitianOfFinCoordinates d x) r) :=
  (measurable_orderedEigenvalue r).comp
    (measurable_hermitianOfFinCoordinates d)

/-- The complete increasing ordered spectrum is measurable as a
function-valued map on explicit Hermitian coordinates. -/
theorem measurable_orderedSpectrum_hermitianOfFinCoordinates (d : ℕ) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      fun r : Fin (Fintype.card (Fin d)) => orderedEigenvalue (hermitianOfFinCoordinates d x) r) :=
  measurable_pi_iff.mpr fun r =>
    measurable_orderedEigenvalue_hermitianOfFinCoordinates d r

/-- Restricting the ordered spectrum to the full-measure simple locus remains
measurable.  This is the phase-free measurable spectral datum used by the projective
eigenpair atlas. -/
theorem measurable_orderedSpectrum_on_hermitianSimpleSpectrum (d : ℕ) :
    Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      fun r : Fin (Fintype.card (Fin d)) => orderedEigenvalue
        (hermitianOfFinCoordinates d x.1) r) :=
  (measurable_orderedSpectrum_hermitianOfFinCoordinates d).comp
    measurable_subtype_coe

end CoareaNative.BlockBand
