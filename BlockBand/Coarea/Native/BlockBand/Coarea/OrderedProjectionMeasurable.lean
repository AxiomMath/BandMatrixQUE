module

public import BlockBand.Coarea.Native.BlockBand.Coarea.LagrangeProjectorEvaluation

/-!
# Measurable zero-extended ordered Hermitian projections

This module closes the Mathlib-only ordered-projection part of the paper's
ordered spectral data.  On the full-measure simple-spectrum locus the value is
the exact rank-one Lagrange projector; on the discriminant it is defined to be
zero.  Thus no measurable choice of Mathlib's eigenvector basis is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- The ordered rank-one spectral projection, extended by zero across the
repeated-spectrum discriminant. -/
def zeroExtendedOrderedEigenprojection (d : ℕ) (r : HermitianEigenRank d)
    (x : HermitianCoordinateSpace d) : Matrix (Fin d) (Fin d) ℂ := by
  classical
  exact if x ∈ hermitianSimpleSpectrumCoordinates d then
      hermitianLagrangeSpectralProjector d r x
    else 0

/-- The zero-extended ordered projection is Borel measurable in explicit real
Hermitian coordinates. -/
theorem measurable_zeroExtendedOrderedEigenprojection (d : ℕ)
    (r : HermitianEigenRank d) :
    Measurable (zeroExtendedOrderedEigenprojection d r) := by
  classical
  unfold zeroExtendedOrderedEigenprojection
  exact (measurable_hermitianLagrangeSpectralProjector d r).piecewise
    (measurableSet_hermitianSimpleSpectrumCoordinates d) measurable_const

/-- The complete paper-facing ordered spectral data in increasing rank order:
each rank is paired with its eigenvalue and its zero-extended rank-one
projection. -/
def orderedSpectralData (d : ℕ) (x : HermitianCoordinateSpace d) :
    HermitianEigenRank d → ℝ × Matrix (Fin d) (Fin d) ℂ :=
  fun r =>
    (orderedEigenvalue (hermitianOfFinCoordinates d x) r,
      zeroExtendedOrderedEigenprojection d r x)

/-- The complete increasing ordered spectral data is a Borel measurable
function-valued map. -/
theorem measurable_orderedSpectralData_map (d : ℕ) :
    Measurable (orderedSpectralData d) := by
  apply measurable_pi_iff.mpr
  intro r
  exact (measurable_orderedEigenvalue_hermitianOfFinCoordinates d r).prodMk
    (measurable_zeroExtendedOrderedEigenprojection d r)

/-- Paper-facing measurable ordered spectral data: both the increasing
eigenvalue and its zero-extended simple-spectrum projection are Borel maps. -/
theorem measurable_orderedSpectralData (d : ℕ)
    (r : HermitianEigenRank d) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      orderedEigenvalue (hermitianOfFinCoordinates d x) r) ∧
    Measurable (zeroExtendedOrderedEigenprojection d r) :=
  ⟨measurable_orderedEigenvalue_hermitianOfFinCoordinates d r,
    measurable_zeroExtendedOrderedEigenprojection d r⟩

/-- On the simple-spectrum locus the extension is exactly the Lagrange
projector. -/
theorem zeroExtendedOrderedEigenprojection_eq_lagrange
    {d : ℕ} (r : HermitianEigenRank d) (x : HermitianCoordinateSpace d)
    (hx : x ∈ hermitianSimpleSpectrumCoordinates d) :
    zeroExtendedOrderedEigenprojection d r x =
      hermitianLagrangeSpectralProjector d r x := by
  simp [zeroExtendedOrderedEigenprojection, hx]

/-- On the repeated-spectrum locus the extension vanishes. -/
theorem zeroExtendedOrderedEigenprojection_eq_zero
    {d : ℕ} (r : HermitianEigenRank d) (x : HermitianCoordinateSpace d)
    (hx : x ∉ hermitianSimpleSpectrumCoordinates d) :
    zeroExtendedOrderedEigenprojection d r x = 0 := by
  simp [zeroExtendedOrderedEigenprojection, hx]

/-- On simple spectrum the measurable projection satisfies the full exact
rank-one/eigenspace correctness package. -/
theorem zeroExtendedOrderedEigenprojection_correct
    {d : ℕ} (r : HermitianEigenRank d) (x : HermitianCoordinateSpace d)
    (hx : x ∈ hermitianSimpleSpectrumCoordinates d) :
    HermitianLagrangeProjectorCorrect d r x := by
  change
    ((hermitianOfFinCoordinates d x : HermitianMatrix (Fin d)) :
      Matrix (Fin d) (Fin d) ℂ).charpoly.Separable at hx
  exact hermitianLagrangeProjectorCorrect_of_separable x hx r

/-- The zero-extended projection has rank one on simple spectrum. -/
theorem rank_zeroExtendedOrderedEigenprojection
    {d : ℕ} (r : HermitianEigenRank d) (x : HermitianCoordinateSpace d)
    (hx : x ∈ hermitianSimpleSpectrumCoordinates d) :
    (zeroExtendedOrderedEigenprojection d r x).rank = 1 := by
  rw [zeroExtendedOrderedEigenprojection_eq_lagrange r x hx]
  exact (zeroExtendedOrderedEigenprojection_correct r x hx).rank_one

end CoareaNative.BlockBand
