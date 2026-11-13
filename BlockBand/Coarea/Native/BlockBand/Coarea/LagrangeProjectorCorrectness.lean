module

public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenlineSelection

/-!
# Correctness interface for measurable Lagrange eigenprojectors

This module isolates the exact algebraic bridge still needed to turn the measurable
Lagrange product into a global measurable eigenline.  The interface records that
the product is a nonzero rank-one orthogonal projector and that its range is the
ordered eigenspace.  From these hypotheses we prove, without any further spectral
choice, that every phase-fixed nonzero column constructed in
`EigenlineSelection` is a normalized eigenvector.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix
open scoped ComplexConjugate

/-- On the algebraic simple-spectrum locus the project's increasing ordered
eigenvalue enumeration is injective.  This closes the first previously missing
library bridge: separability gives duplicate-free characteristic roots, and
Mathlib identifies those roots with `eigenvalues₀`. -/
theorem orderedEigenvalue_injective_of_separable
    {d : ℕ} (A : HermitianMatrix (Fin d))
    (hsep : (A : Matrix (Fin d) (Fin d) ℂ).charpoly.Separable) :
    Function.Injective (orderedEigenvalue A) := by
  have heigC : Function.Injective
      (fun i => (A.property.eigenvalues i : ℂ)) := by
    rw [A.property.charpoly_eq, Polynomial.separable_prod_X_sub_C_iff] at hsep
    exact hsep
  have heig : Function.Injective A.property.eigenvalues := by
    intro i j hij
    exact heigC (congrArg (fun t : ℝ => (t : ℂ)) hij)
  let E : Fin d ≃ Fin (Fintype.card (Fin d)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  have heig0 : Function.Injective A.property.eigenvalues₀ := by
    intro i j hij
    apply E.symm.injective
    apply heig
    simpa [Matrix.IsHermitian.eigenvalues, E] using hij
  intro r s hrs
  apply Fin.rev_injective
  apply heig0
  exact hrs

/-- Distinct ranks have nonzero Lagrange denominators on the simple-spectrum
locus. -/
theorem orderedEigenvalue_sub_ne_zero_of_separable
    {d : ℕ} (A : HermitianMatrix (Fin d))
    (hsep : (A : Matrix (Fin d) (Fin d) ℂ).charpoly.Separable)
    {r s : HermitianEigenRank d} (hrs : r ≠ s) :
    orderedEigenvalue A r - orderedEigenvalue A s ≠ 0 := by
  exact sub_ne_zero.mpr (fun h => hrs (orderedEigenvalue_injective_of_separable A hsep h))

/-- Algebraic correctness data for the ordered Lagrange projector at one
Hermitian coordinate point.  This is the precise interface that can be supplied
by a polynomial functional-calculus theorem (external, if necessary).

`rank_one` uses the matrix rank over `ℂ`; together with `selfAdjoint` and
`idempotent` it says that the candidate is a rank-one orthogonal projector.
The final identity says its range is contained in the ordered eigenspace. -/
structure HermitianLagrangeProjectorCorrect (d : ℕ)
    (r : HermitianEigenRank d) (x : HermitianCoordinateSpace d) : Prop where
  nonzero : hermitianLagrangeSpectralProjector d r x ≠ 0
  rank_one : (hermitianLagrangeSpectralProjector d r x).rank = 1
  selfAdjoint : (hermitianLagrangeSpectralProjector d r x).conjTranspose =
    hermitianLagrangeSpectralProjector d r x
  idempotent : hermitianLagrangeSpectralProjector d r x *
    hermitianLagrangeSpectralProjector d r x =
    hermitianLagrangeSpectralProjector d r x
  left_eigen :
    (hermitianOfFinCoordinates d x : Matrix (Fin d) (Fin d) ℂ) *
        hermitianLagrangeSpectralProjector d r x =
      ((orderedEigenvalue (hermitianOfFinCoordinates d x) r : ℝ) : ℂ) •
        hermitianLagrangeSpectralProjector d r x

/-- Correctness supplies a nonempty finite family of measurable projective
charts at every coordinate point. -/
theorem HermitianLagrangeProjectorCorrect.exists_chart
    {d : ℕ} {r : HermitianEigenRank d} {x : HermitianCoordinateSpace d}
    (h : HermitianLagrangeProjectorCorrect d r x) :
    ∃ i j : Fin d, x ∈ hermitianLagrangeProjectorChartSource d r i j :=
  exists_mem_hermitianLagrangeProjectorChartSource_of_ne_zero d r x h.nonzero

/-- A nonzero projector column is an eigenvector of the reconstructed Hermitian
matrix, expressed in the Euclidean vector model used by the chart atlas. -/
theorem hermitianLagrangeProjectorColumn_eigenvector
    {d : ℕ} {r : HermitianEigenRank d} {x : HermitianCoordinateSpace d}
    (h : HermitianLagrangeProjectorCorrect d r x) (j : Fin d) :
    ((hermitianOfFinCoordinates d x : Matrix (Fin d) (Fin d) ℂ).mulVec
        (hermitianLagrangeProjectorColumn d r j x)) =
      ((orderedEigenvalue (hermitianOfFinCoordinates d x) r : ℝ) : ℂ) •
        hermitianLagrangeProjectorColumn d r j x := by
  funext i
  have hij := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) h.left_eigen
  change ((hermitianOfFinCoordinates d x : Matrix (Fin d) (Fin d) ℂ) *
      hermitianLagrangeSpectralProjector d r x) i j = _
  simpa [Matrix.smul_apply, hermitianLagrangeProjectorColumn] using hij

/-- Every phase-fixed chart representative obtained from a correct Lagrange
projector remains in the same ordered eigenspace. -/
theorem phaseFixedLagrangeProjectorColumn_eigenvector
    {d : ℕ} {r : HermitianEigenRank d} {i j : Fin d}
    (x : hermitianLagrangeProjectorChartSource d r i j)
    (h : HermitianLagrangeProjectorCorrect d r x.1) :
    ((hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ).mulVec
        (phaseFixedLagrangeProjectorColumn d r i j x)) =
      ((orderedEigenvalue (hermitianOfFinCoordinates d x.1) r : ℝ) : ℂ) •
        phaseFixedLagrangeProjectorColumn d r i j x := by
  have hv : hermitianLagrangeProjectorColumn d r j x.1 i ≠ 0 := x.property
  let v := hermitianLagrangeProjectorColumn d r j x.1
  let a : ℂ :=
    ((‖projectiveAffineRepresentative i v‖⁻¹ : ℝ) : ℂ) * (v i)⁻¹
  have hphase : phaseFixedLagrangeProjectorColumn d r i j x = a • v := by
    rw [phaseFixedLagrangeProjectorColumn, projectiveUnitReconstruction,
      projectiveEigenvectorReconstruction_chart i _ hv,
      projectiveAffineRepresentative]
    apply PiLp.ext
    intro q
    simp [a, v, projectiveAffineRepresentative, mul_assoc]
  rw [hphase]
  change (hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ).mulVec
      (a • v.ofLp) = _
  rw [Matrix.mulVec_smul,
    show (hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ).mulVec
        v.ofLp =
      ((orderedEigenvalue (hermitianOfFinCoordinates d x.1) r : ℝ) : ℂ) • v.ofLp by
        exact hermitianLagrangeProjectorColumn_eigenvector h j]
  ext q
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Paper-facing functional-calculus input: the Lagrange product is correct at
every ordered rank throughout the full-measure simple-spectrum locus.  This is
a, explicit interface rather than an unconditional theorem; its only
missing ingredient is the finite-dimensional polynomial functional calculus. -/
structure HermitianLagrangeFunctionalCalculus (d : ℕ) : Prop where
  correct : ∀ (x : HermitianCoordinateSpace d),
    x ∈ hermitianSimpleSpectrumCoordinates d →
    ∀ r : HermitianEigenRank d, HermitianLagrangeProjectorCorrect d r x

/-- Under the functional-calculus interface the Lagrange projector is
nonzero at every rank on the simple-spectrum locus. -/
theorem hermitianLagrangeSpectralProjector_ne_zero_on_simple
    {d : ℕ} (hfc : HermitianLagrangeFunctionalCalculus d)
    (x : hermitianSimpleSpectrumCoordinates d) (r : HermitianEigenRank d) :
    hermitianLagrangeSpectralProjector d r x.1 ≠ 0 :=
  (hfc.correct x.1 x.2 r).nonzero

/-- The `(i,j)` chart source restricted to the full-measure simple-spectrum
locus. -/
abbrev hermitianSimpleLagrangeChartSource (d : ℕ)
    (r : HermitianEigenRank d) (i j : Fin d) :=
  {x : hermitianSimpleSpectrumCoordinates d //
    x.1 ∈ hermitianLagrangeProjectorChartSource d r i j}

/-- The phase-fixed vector on a simple-spectrum chart. -/
def phaseFixedSimpleLagrangeEigenvector (d : ℕ)
    (r : HermitianEigenRank d) (i j : Fin d)
    (x : hermitianSimpleLagrangeChartSource d r i j) :
    EuclideanSpace ℂ (Fin d) :=
  phaseFixedLagrangeProjectorColumn d r i j ⟨x.1.1, x.2⟩

/-- On each fixed finite chart, the phase-fixed eigenline selection is
measurable.  No arbitrary Mathlib eigenbasis is selected. -/
theorem measurable_phaseFixedSimpleLagrangeEigenvector
    (d : ℕ) (r : HermitianEigenRank d) (i j : Fin d) :
    Measurable (phaseFixedSimpleLagrangeEigenvector d r i j) := by
  apply (measurable_phaseFixedLagrangeProjectorColumn d r i j).comp
  have hval : Measurable (fun x : hermitianSimpleLagrangeChartSource d r i j =>
      x.1.1) := measurable_subtype_coe.comp measurable_subtype_coe
  exact hval.subtype_mk

/-- The simple-chart selection is normalized to unit Euclidean norm. -/
@[simp] theorem norm_phaseFixedSimpleLagrangeEigenvector
    (d : ℕ) (r : HermitianEigenRank d) (i j : Fin d)
    (x : hermitianSimpleLagrangeChartSource d r i j) :
    ‖phaseFixedSimpleLagrangeEigenvector d r i j x‖ = 1 :=
  norm_phaseFixedLagrangeProjectorColumn d r i j ⟨x.1.1, x.2⟩

/-- The distinguished coordinate has positive real part, recording the chosen
phase gauge. -/
theorem phaseFixedSimpleLagrangeEigenvector_self_re_pos
    (d : ℕ) (r : HermitianEigenRank d) (i j : Fin d)
    (x : hermitianSimpleLagrangeChartSource d r i j) :
    0 < (phaseFixedSimpleLagrangeEigenvector d r i j x i).re :=
  projectiveUnitReconstruction_self_re_pos i _

/-- The phase-fixed selection on a correct simple-spectrum chart is a unit
ordered eigenvector. -/
theorem phaseFixedSimpleLagrangeEigenvector_eigenvector
    {d : ℕ} (hfc : HermitianLagrangeFunctionalCalculus d)
    (r : HermitianEigenRank d) (i j : Fin d)
    (x : hermitianSimpleLagrangeChartSource d r i j) :
    ((hermitianOfFinCoordinates d x.1.1 : Matrix (Fin d) (Fin d) ℂ).mulVec
        (phaseFixedSimpleLagrangeEigenvector d r i j x)) =
      ((orderedEigenvalue (hermitianOfFinCoordinates d x.1.1) r : ℝ) : ℂ) •
        phaseFixedSimpleLagrangeEigenvector d r i j x := by
  exact phaseFixedLagrangeProjectorColumn_eigenvector
    ⟨x.1.1, x.2⟩ (hfc.correct x.1.1 x.1.2 r)

/-- Every simple-spectrum coordinate point is covered by at least one of the
finite measurable phase-fixed charts, assuming the correctness interface. -/
theorem exists_simple_Lagrange_chart
    {d : ℕ} (hfc : HermitianLagrangeFunctionalCalculus d)
    (r : HermitianEigenRank d) (x : hermitianSimpleSpectrumCoordinates d) :
    ∃ i j : Fin d, x.1 ∈ hermitianLagrangeProjectorChartSource d r i j :=
  (hfc.correct x.1 x.2 r).exists_chart

end CoareaNative.BlockBand
