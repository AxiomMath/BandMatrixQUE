module

public import BlockBand.Coarea.Native.BlockBand.Coarea.ProjectiveEigenvectorCharts
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurable spectral-projector eigenline chart precursors

For a Hermitian matrix with simple spectrum, the rank-one eigenprojection at an
ordered eigenvalue is given algebraically by the Lagrange product
`∏_{s ≠ r} (A - λ_s I) / (λ_r - λ_s)`.  This module defines that formula in the
explicit real Hermitian coordinates and proves its measurability, together with
measurability of every column and every phase-fixed projective chart obtained
from a nonzero projector entry.

The formula is defined on all matrices (division by zero uses the field's total
inverse), while its spectral interpretation is intended on the simple-spectrum
locus.  The current Mathlib API does not connect separability of a Hermitian
characteristic polynomial directly to pairwise distinct `eigenvalues₀`, nor
provide the polynomial-functional-calculus eigenprojection theorem.  We
therefore do not assert here that the Lagrange product is rank one or satisfies
the eigenvector equation.  The measurable finite family of nonzero-entry chart
sources proved below is the dependency-complete precursor to the eventual
least-chart selection.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

set_option linter.unusedSectionVars false

open Matrix

/-- Ordered eigenvalue ranks for a `d × d` Hermitian matrix. -/
abbrev HermitianEigenRank (d : ℕ) := Fin (Fintype.card (Fin d))

/-- The fixed increasing list of all ranks except `r`.  A list, rather than a
`Finset` product, is used because matrix multiplication is noncommutative. -/
def otherHermitianEigenRanks (d : ℕ) (r : HermitianEigenRank d) :
    List (HermitianEigenRank d) :=
  (List.ofFn fun s : HermitianEigenRank d => s).filter (· ≠ r)

/-- One factor in the Lagrange spectral-projection formula. -/
def hermitianSpectralLagrangeFactor (d : ℕ) (r s : HermitianEigenRank d)
    (x : HermitianCoordinateSpace d) : Matrix (Fin d) (Fin d) ℂ :=
  (((orderedEigenvalue (hermitianOfFinCoordinates d x) r -
      orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℝ) : ℂ)⁻¹) •
    ((hermitianOfFinCoordinates d x : Matrix (Fin d) (Fin d) ℂ) -
      ((orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℝ) : ℂ) • 1)

/-- The Lagrange-product candidate for the ordered rank-`r` spectral
projection.  On simple spectrum, the factors commute because they are
polynomials in the same matrix, but no commutativity is needed for this fixed
list product. -/
def hermitianLagrangeSpectralProjector (d : ℕ) (r : HermitianEigenRank d)
    (x : HermitianCoordinateSpace d) : Matrix (Fin d) (Fin d) ℂ :=
  ((otherHermitianEigenRanks d r).map fun s =>
    hermitianSpectralLagrangeFactor d r s x).prod

/-- Every Lagrange factor is a measurable matrix-valued function of the real
Hermitian coordinates. -/
theorem measurable_hermitianSpectralLagrangeFactor
    (d : ℕ) (r s : HermitianEigenRank d) :
    Measurable (hermitianSpectralLagrangeFactor d r s) := by
  apply Measurable.of_eval_matrix
  intro i j
  have hr := measurable_orderedEigenvalue_hermitianOfFinCoordinates d r
  have hs := measurable_orderedEigenvalue_hermitianOfFinCoordinates d s
  have hA : Measurable (fun x : HermitianCoordinateSpace d =>
      (hermitianOfFinCoordinates d x : Matrix (Fin d) (Fin d) ℂ)) :=
    measurable_coe_hermitianMatrix.comp
      (measurable_hermitianOfFinCoordinates d)
  simp only [hermitianSpectralLagrangeFactor, Matrix.smul_apply,
    Matrix.sub_apply]
  fun_prop

/-- Products of two measurable finite matrix-valued functions are measurable,
proved entrywise because Mathlib does not install a global `MeasurableMul₂`
instance for noncommutative square matrices. -/
theorem measurable_matrix_mul {α : Type*} [MeasurableSpace α]
    {m : Type*} [Fintype m] [DecidableEq m]
    {f g : α → Matrix m m ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x * g x) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.mul_apply]
  fun_prop

/-- The full Lagrange spectral-projector candidate is measurable. -/
theorem measurable_hermitianLagrangeSpectralProjector
    (d : ℕ) (r : HermitianEigenRank d) :
    Measurable (hermitianLagrangeSpectralProjector d r) := by
  unfold hermitianLagrangeSpectralProjector
  induction otherHermitianEigenRanks d r with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      exact measurable_const
  | cons s l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact measurable_matrix_mul
        (measurable_hermitianSpectralLagrangeFactor d r s) ih

/-- A column of the measurable Lagrange projector, regarded in the paper's
Euclidean complex vector space. -/
def hermitianLagrangeProjectorColumn (d : ℕ) (r : HermitianEigenRank d)
    (j : Fin d) (x : HermitianCoordinateSpace d) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun i => hermitianLagrangeSpectralProjector d r x i j

/-- Every projector column is measurable. -/
theorem measurable_hermitianLagrangeProjectorColumn
    (d : ℕ) (r : HermitianEigenRank d) (j : Fin d) :
    Measurable (hermitianLagrangeProjectorColumn d r j) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℂ)).measurable.comp
  rw [measurable_pi_iff]
  intro i
  exact (measurable_hermitianLagrangeSpectralProjector d r).eval_matrix

/-- Source of the `(i,j)` projective chart: the `i`-th coordinate of the
`j`-th projector column is nonzero. -/
def hermitianLagrangeProjectorChartSource (d : ℕ)
    (r : HermitianEigenRank d) (i j : Fin d) :
    Set (HermitianCoordinateSpace d) :=
  {x | hermitianLagrangeSpectralProjector d r x i j ≠ 0}

/-- Every nonzero-entry projector chart source is measurable. -/
theorem measurableSet_hermitianLagrangeProjectorChartSource
    (d : ℕ) (r : HermitianEigenRank d) (i j : Fin d) :
    MeasurableSet (hermitianLagrangeProjectorChartSource d r i j) := by
  have hij : Measurable (fun x : HermitianCoordinateSpace d =>
      hermitianLagrangeSpectralProjector d r x i j) :=
    (measurable_hermitianLagrangeSpectralProjector d r).eval_matrix
  rw [show hermitianLagrangeProjectorChartSource d r i j =
      {x | hermitianLagrangeSpectralProjector d r x i j = 0}ᶜ by
    ext x
    simp [hermitianLagrangeProjectorChartSource]]
  exact (hij (measurableSet_singleton (0 : ℂ))).compl

/-- A phase-fixed unit vector reconstructed from a nonzero projector entry.
The source subtype contains exactly the denominator-nonvanishing proof needed
by the affine chart. -/
def phaseFixedLagrangeProjectorColumn (d : ℕ)
    (r : HermitianEigenRank d) (i j : Fin d)
    (x : hermitianLagrangeProjectorChartSource d r i j) :
    EuclideanSpace ℂ (Fin d) :=
  projectiveUnitReconstruction i
    (projectiveEigenvectorChart i
      (hermitianLagrangeProjectorColumn d r j x.1))

/-- Each phase-fixed projector-column candidate is measurable on its nonzero
entry source. -/
theorem measurable_phaseFixedLagrangeProjectorColumn
    (d : ℕ) (r : HermitianEigenRank d) (i j : Fin d) :
    Measurable (phaseFixedLagrangeProjectorColumn d r i j) := by
  apply (measurable_projectiveUnitReconstruction i).comp
  rw [measurable_pi_iff]
  intro q
  have hP : Measurable (fun x : hermitianLagrangeProjectorChartSource d r i j =>
      hermitianLagrangeSpectralProjector d r x.1) :=
    (measurable_hermitianLagrangeSpectralProjector d r).comp
      measurable_subtype_coe
  have hnum : Measurable (fun x : hermitianLagrangeProjectorChartSource d r i j =>
      hermitianLagrangeSpectralProjector d r x.1 q.1 j) := hP.eval_matrix
  have hden : Measurable (fun x : hermitianLagrangeProjectorChartSource d r i j =>
      hermitianLagrangeSpectralProjector d r x.1 i j) := hP.eval_matrix
  exact hnum.div hden

/-- The phase-fixed projector-column candidate has Euclidean norm one. -/
@[simp] theorem norm_phaseFixedLagrangeProjectorColumn
    (d : ℕ) (r : HermitianEigenRank d) (i j : Fin d)
    (x : hermitianLagrangeProjectorChartSource d r i j) :
    ‖phaseFixedLagrangeProjectorColumn d r i j x‖ = 1 := by
  exact norm_projectiveUnitReconstruction i _

/-- If the Lagrange projector candidate is nonzero, at least one of the finite
projective chart sources contains the coordinate point.  This is the exact
finite-coverage input for a future measurable least-chart disjointization. -/
theorem exists_mem_hermitianLagrangeProjectorChartSource_of_ne_zero
    (d : ℕ) (r : HermitianEigenRank d) (x : HermitianCoordinateSpace d)
    (hP : hermitianLagrangeSpectralProjector d r x ≠ 0) :
    ∃ i j : Fin d, x ∈ hermitianLagrangeProjectorChartSource d r i j := by
  by_contra h
  push Not at h
  apply hP
  ext i j
  simpa [hermitianLagrangeProjectorChartSource] using h i j

end CoareaNative.BlockBand
