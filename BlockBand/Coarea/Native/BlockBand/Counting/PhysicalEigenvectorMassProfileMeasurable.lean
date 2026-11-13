module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalEigenvectorMassProfile
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalGaussianRingStateMeasurable
public import BlockBand.Coarea.Native.BlockBand.Coarea.OrderedEigenlineSelection
public import BlockBand.Coarea.Native.BlockBand.Coarea.SelectedCoordinateEigenpairChart

/-!
# Measurable physical eigenvector mass profiles

This module constructs a canonical measurable phase-fixed eigenvector on the
simple-spectrum locus using the ordered Lagrange-projector charts.  Outside
that locus the vector is set to zero and its probability-valued block-mass
mark is set to a fixed Dirac mass.  Thus the resulting marked configuration
and its rational-window encoding are globally measurable without asserting
measurability of Mathlib's arbitrary orthonormal eigenbasis at collisions.

Measurability of the original `physicalBlockMassProfile` would need a
measurable-dependence theorem for `Matrix.IsHermitian.eigenvectorBasis` on the
repeated-spectrum locus (or an equality identifying its block weights with a
specified measurable collision convention).  No such theorem is present in
Mathlib.  The simple-spectrum construction below avoids this rather than
claiming that the arbitrary basis choice is measurable.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

abbrev PhysicalIndex (p : Params) := BlockGUE.Index (physicalBlockSizes p)
abbrev PhysicalDimension (p : Params) := Fintype.card (PhysicalIndex p)

/-- Canonical finite-ordinal indexing of the physical matrix coordinates. -/
noncomputable def physicalIndexEquivFin (p : Params) :
    PhysicalIndex p ≃ Fin (PhysicalDimension p) :=
  Fintype.equivFin _

/-- Reindex a physical Hermitian matrix by the canonical finite ordinal. -/
def physicalHermitianFinReindex (p : Params)
    (A : HermitianMatrix (PhysicalIndex p)) :
    HermitianMatrix (Fin (PhysicalDimension p)) :=
  ⟨Matrix.reindex (physicalIndexEquivFin p) (physicalIndexEquivFin p) A.1,
    isHermitian_reindex_equiv (physicalIndexEquivFin p) A.1 A.2⟩

/-- Explicit real coordinates of a physical Hermitian matrix after canonical
finite-ordinal reindexing. -/
def physicalHermitianFinCoordinates (p : Params)
    (A : HermitianMatrix (PhysicalIndex p)) :
    HermitianCoordinateSpace (PhysicalDimension p) :=
  fun k => coordinatesOfHermitian (physicalHermitianFinReindex p A)
    ((hermitianCoordinateEquivFin (PhysicalDimension p)).symm k)

/-- Canonical finite reindexing is measurable entry by entry. -/
theorem measurable_physicalHermitianFinReindex (p : Params) :
    Measurable (physicalHermitianFinReindex p) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval_matrix
  intro i j
  exact measurable_coe_hermitianMatrix.eval_matrix

/-- Physical Hermitian coordinates are measurable because every output
coordinate is the real or imaginary part of one fixed matrix entry. -/
theorem measurable_physicalHermitianFinCoordinates (p : Params) :
    Measurable (physicalHermitianFinCoordinates p) := by
  have hraw : Measurable (fun A : HermitianMatrix (PhysicalIndex p) =>
      (physicalHermitianFinReindex p A :
        Matrix (Fin (PhysicalDimension p)) (Fin (PhysicalDimension p)) ℂ)) :=
    measurable_coe_hermitianMatrix.comp
      (measurable_physicalHermitianFinReindex p)
  rw [measurable_pi_iff]
  intro k
  generalize hc :
    (hermitianCoordinateEquivFin (PhysicalDimension p)).symm k = c
  rcases c with i | ij
  · simp only [physicalHermitianFinCoordinates, hc, coordinatesOfHermitian]
    change Measurable (Complex.re ∘ fun A =>
      (physicalHermitianFinReindex p A : Matrix _ _ ℂ) i i)
    exact Complex.measurable_re.comp (hraw.eval_matrix (i := i) (j := i))
  · rcases ij with ij | ij
    · simp only [physicalHermitianFinCoordinates, hc, coordinatesOfHermitian]
      change Measurable (Complex.re ∘ fun A =>
        (physicalHermitianFinReindex p A : Matrix _ _ ℂ) ij.1.1 ij.1.2)
      exact Complex.measurable_re.comp
        (hraw.eval_matrix (i := ij.1.1) (j := ij.1.2))
    · simp only [physicalHermitianFinCoordinates, hc, coordinatesOfHermitian]
      change Measurable (Complex.im ∘ fun A =>
        (physicalHermitianFinReindex p A : Matrix _ _ ℂ) ij.1.1 ij.1.2)
      exact Complex.measurable_im.comp
        (hraw.eval_matrix (i := ij.1.1) (j := ij.1.2))

/-- Reconstructing the extracted finite coordinates returns the canonically
reindexed physical Hermitian matrix. -/
theorem hermitianOfFinCoordinates_physicalHermitianFinCoordinates
    (p : Params) (A : HermitianMatrix (PhysicalIndex p)) :
    hermitianOfFinCoordinates (PhysicalDimension p)
      (physicalHermitianFinCoordinates p A) =
      physicalHermitianFinReindex p A := by
  simpa [hermitianOfFinCoordinates, physicalHermitianFinCoordinates,
    Function.comp_def] using
    (hermitianOfCoordinates_coordinatesOfHermitian
      (physicalHermitianFinReindex p A))

/-- Physical matrices whose explicit finite-coordinate characteristic polynomial
has simple roots. -/
def physicalSimpleSpectrumMatrices (p : Params) :
    Set (HermitianMatrix (PhysicalIndex p)) :=
  physicalHermitianFinCoordinates p ⁻¹'
    hermitianSimpleSpectrumCoordinates (PhysicalDimension p)

/-- The physical simple-spectrum locus is measurable. -/
theorem measurableSet_physicalSimpleSpectrumMatrices (p : Params) :
    MeasurableSet (physicalSimpleSpectrumMatrices p) :=
  (measurableSet_hermitianSimpleSpectrumCoordinates (PhysicalDimension p)).preimage
    (measurable_physicalHermitianFinCoordinates p)

/-- Coordinate identification from a physical simple-spectrum matrix to the
coordinate simple-spectrum subtype used by the Lagrange-projector atlas. -/
def physicalSimpleSpectrumCoordinates (p : Params) :
    physicalSimpleSpectrumMatrices p →
      hermitianSimpleSpectrumCoordinates (PhysicalDimension p) :=
  fun A => ⟨physicalHermitianFinCoordinates p A.1, A.2⟩

/-- The coordinate identification on the physical simple-spectrum subtype is
measurable. -/
theorem measurable_physicalSimpleSpectrumCoordinates (p : Params) :
    Measurable (physicalSimpleSpectrumCoordinates p) := by
  apply Measurable.subtype_mk
  exact (measurable_physicalHermitianFinCoordinates p).comp
    measurable_subtype_coe

/-- Convert the physical finite-ordinal rank to the rank type used by the
coordinate eigenline atlas. -/
def physicalEigenRank (p : Params) (i : Fin (PhysicalDimension p)) :
    HermitianEigenRank (PhysicalDimension p) :=
  Fin.cast (Fintype.card_fin (PhysicalDimension p)).symm i

/-- Canonical phase-fixed ordered unit eigenvector of a physical matrix on the
simple-spectrum locus, expressed in the canonical finite-ordinal indexing. -/
def physicalSimpleOrderedEigenvectorFin (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : physicalSimpleSpectrumMatrices p) :
    EuclideanSpace ℂ (Fin (PhysicalDimension p)) :=
  orderedEigenlineSelection (PhysicalDimension p) (physicalEigenRank p i)
    (physicalSimpleSpectrumCoordinates p A)

/-- Canonical ordered eigenvectors are measurable on the entire
simple-spectrum subtype. -/
theorem measurable_physicalSimpleOrderedEigenvectorFin (p : Params)
    (i : Fin (PhysicalDimension p)) :
    Measurable (physicalSimpleOrderedEigenvectorFin p i) :=
  (measurable_orderedEigenlineSelection (PhysicalDimension p)
      (physicalEigenRank p i)).comp
    (measurable_physicalSimpleSpectrumCoordinates p)

/-- The canonical simple-spectrum ordered eigenvector has unit norm. -/
@[simp] theorem norm_physicalSimpleOrderedEigenvectorFin (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : physicalSimpleSpectrumMatrices p) :
    ‖physicalSimpleOrderedEigenvectorFin p i A‖ = 1 :=
  norm_orderedEigenlineSelection (physicalEigenRank p i)
    (physicalSimpleSpectrumCoordinates p A)

/-- On simple spectrum, the selected finite-coordinate unit vector satisfies
the ordered eigenvector equation for the canonically reindexed physical matrix. -/
theorem physicalSimpleOrderedEigenvectorFin_eigenvector (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : physicalSimpleSpectrumMatrices p) :
    ((physicalHermitianFinReindex p A.1 : Matrix _ _ ℂ).mulVec
      (physicalSimpleOrderedEigenvectorFin p i A)) =
    ((orderedEigenvalue (physicalHermitianFinReindex p A.1)
      (physicalEigenRank p i) : ℝ) : ℂ) •
      physicalSimpleOrderedEigenvectorFin p i A := by
  rw [← hermitianOfFinCoordinates_physicalHermitianFinCoordinates p A.1]
  exact orderedEigenlineSelection_eigenvector (physicalEigenRank p i)
    (physicalSimpleSpectrumCoordinates p A)

/-- Globally measurable extension of the phase-fixed ordered eigenvector.
It agrees with the unit eigenvector on simple spectrum and uses zero at
collisions; hence no normalization claim is made off the simple locus. -/
def physicalMeasurableOrderedEigenvectorFin (p : Params)
    (i : Fin (PhysicalDimension p)) :
    HermitianMatrix (PhysicalIndex p) →
      EuclideanSpace ℂ (Fin (PhysicalDimension p)) :=
  Function.extend (Subtype.val : physicalSimpleSpectrumMatrices p →
      HermitianMatrix (PhysicalIndex p))
    (physicalSimpleOrderedEigenvectorFin p i) (fun _ => 0)

/-- The global zero extension of canonical ordered eigenvectors is measurable. -/
theorem measurable_physicalMeasurableOrderedEigenvectorFin (p : Params)
    (i : Fin (PhysicalDimension p)) :
    Measurable (physicalMeasurableOrderedEigenvectorFin p i) := by
  exact (MeasurableEmbedding.subtype_coe
      (measurableSet_physicalSimpleSpectrumMatrices p)).measurable_extend
    (measurable_physicalSimpleOrderedEigenvectorFin p i) measurable_const

/-- On a simple-spectrum physical matrix, the global extension is exactly the
canonical phase-fixed unit eigenvector. -/
theorem physicalMeasurableOrderedEigenvectorFin_apply_simple (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : physicalSimpleSpectrumMatrices p) :
    physicalMeasurableOrderedEigenvectorFin p i A.1 =
      physicalSimpleOrderedEigenvectorFin p i A := by
  simp [physicalMeasurableOrderedEigenvectorFin]

/-- The canonical simple-spectrum eigenvector transported back to the physical
block index. -/
def physicalSimpleOrderedEigenvector (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : physicalSimpleSpectrumMatrices p) :
    EuclideanSpace ℂ (PhysicalIndex p) :=
  (EuclideanSpace.equiv (PhysicalIndex p) ℂ).symm
    (fun a => physicalSimpleOrderedEigenvectorFin p i A
      (physicalIndexEquivFin p a))

/-- Transport back to physical block coordinates preserves measurability. -/
theorem measurable_physicalSimpleOrderedEigenvector (p : Params)
    (i : Fin (PhysicalDimension p)) :
    Measurable (physicalSimpleOrderedEigenvector p i) := by
  apply (EuclideanSpace.equiv (PhysicalIndex p) ℂ).symm.continuous.measurable.comp
  have hfun : Measurable (fun A =>
      (EuclideanSpace.equiv (Fin (PhysicalDimension p)) ℂ)
        (physicalSimpleOrderedEigenvectorFin p i A)) :=
    (EuclideanSpace.equiv (Fin (PhysicalDimension p)) ℂ).continuous.measurable.comp
      (measurable_physicalSimpleOrderedEigenvectorFin p i)
  rw [measurable_pi_iff]
  intro a
  exact hfun.eval

/-- Transport back to the physical block index preserves the unit norm. -/
@[simp] theorem norm_physicalSimpleOrderedEigenvector (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : physicalSimpleSpectrumMatrices p) :
    ‖physicalSimpleOrderedEigenvector p i A‖ = 1 := by
  have hsq : ‖physicalSimpleOrderedEigenvector p i A‖ ^ 2 =
      ‖physicalSimpleOrderedEigenvectorFin p i A‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ a : PhysicalIndex p,
      ‖physicalSimpleOrderedEigenvectorFin p i A (physicalIndexEquivFin p a)‖ ^ 2) = _
    exact (Equiv.sum_comp (physicalIndexEquivFin p)
      (fun j => ‖physicalSimpleOrderedEigenvectorFin p i A j‖ ^ 2))
  have hnorm := norm_physicalSimpleOrderedEigenvectorFin p i A
  nlinarith [norm_nonneg (physicalSimpleOrderedEigenvector p i A)]

/-- Globally measurable canonical block weight.  It is the ordered
phase-fixed eigenvector weight on simple spectrum and zero at collisions. -/
def physicalMeasurableBlockMassWeight (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : HermitianMatrix (PhysicalIndex p)) (k : Fin p.n) : NNReal :=
  ∑ a : Fin (physicalBlockSizes p k),
    ‖physicalMeasurableOrderedEigenvectorFin p i A
      (physicalIndexEquivFin p ⟨k, a⟩)‖₊ ^ 2

/-- Every globally extended canonical block weight is measurable. -/
theorem measurable_physicalMeasurableBlockMassWeight (p : Params)
    (i : Fin (PhysicalDimension p)) (k : Fin p.n) :
    Measurable (fun A => physicalMeasurableBlockMassWeight p i A k) := by
  unfold physicalMeasurableBlockMassWeight
  apply Finset.measurable_sum
  intro a _ha
  have hfun : Measurable (fun A =>
      (EuclideanSpace.equiv (Fin (PhysicalDimension p)) ℂ)
        (physicalMeasurableOrderedEigenvectorFin p i A)) :=
    (EuclideanSpace.equiv (Fin (PhysicalDimension p)) ℂ).continuous.measurable.comp
      (measurable_physicalMeasurableOrderedEigenvectorFin p i)
  exact hfun.eval.nnnorm.pow_const 2

/-- Block weight of the canonical phase-fixed eigenvector on simple spectrum. -/
def physicalSimpleBlockMassWeight (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : physicalSimpleSpectrumMatrices p) (k : Fin p.n) : NNReal :=
  physicalBlockMassWeight p (physicalSimpleOrderedEigenvector p i A) k

/-- Every canonical simple-spectrum block weight is measurable. -/
theorem measurable_physicalSimpleBlockMassWeight (p : Params)
    (i : Fin (PhysicalDimension p)) (k : Fin p.n) :
    Measurable (fun A => physicalSimpleBlockMassWeight p i A k) := by
  unfold physicalSimpleBlockMassWeight physicalBlockMassWeight
  apply Finset.measurable_sum
  intro a _ha
  have hcoord : Measurable (fun A =>
      physicalSimpleOrderedEigenvector p i A ⟨k, a⟩) := by
    have hfun : Measurable (fun A =>
        (EuclideanSpace.equiv (PhysicalIndex p) ℂ)
          (physicalSimpleOrderedEigenvector p i A)) :=
      (EuclideanSpace.equiv (PhysicalIndex p) ℂ).continuous.measurable.comp
        (measurable_physicalSimpleOrderedEigenvector p i)
    exact hfun.eval
  exact hcoord.nnnorm.pow_const 2

/-- The canonical simple-spectrum block masses sum to one. -/
theorem sum_physicalSimpleBlockMassWeight_eq_one (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : physicalSimpleSpectrumMatrices p) :
    ∑ k : Fin p.n, physicalSimpleBlockMassWeight p i A k = 1 :=
  sum_physicalBlockMassWeight_eq_one p
    (physicalSimpleOrderedEigenvector p i A)
    (norm_physicalSimpleOrderedEigenvector p i A)

/-- Probability-valued block-mass profile of the canonical phase-fixed ordered
eigenvector on simple spectrum. -/
def physicalSimpleBlockMassProfile (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : physicalSimpleSpectrumMatrices p) :
    ProbabilityMeasure (Fin p.n) := by
  let w : Fin p.n → NNReal := physicalSimpleBlockMassWeight p i A
  have hsum : ∑ k, w k = 1 := sum_physicalSimpleBlockMassWeight_eq_one p i A
  have hhas : HasSum w 1 := by
    simpa [hsum] using (hasSum_fintype w)
  exact ⟨Measure.sum fun k => w k • Measure.dirac k,
    hhas.isProbabilityMeasure_sum_dirac_nnreal⟩

/-- The canonical simple-spectrum probability profile is measurable. -/
theorem measurable_physicalSimpleBlockMassProfile (p : Params)
    (i : Fin (PhysicalDimension p)) :
    Measurable (physicalSimpleBlockMassProfile p i) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro S hS
  change Measurable (fun A =>
    (Measure.sum fun k => physicalSimpleBlockMassWeight p i A k •
      Measure.dirac k) S)
  simp_rw [Measure.sum_apply _ hS]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hS]
  apply Measurable.tsum
  intro k
  exact (measurable_physicalSimpleBlockMassWeight p i k).coe_nnreal_ennreal.mul
    ((measurable_one.indicator hS).comp measurable_const)

/-- Fixed collision mark used where an ordered eigenline is not intrinsic. -/
def defaultPhysicalBlockMassProfile (p : Params) : ProbabilityMeasure (Fin p.n) :=
  ⟨Measure.dirac 0, inferInstance⟩

/-- Globally measurable probability-valued block-mass profile: the canonical
simple-spectrum profile, extended at collisions by the fixed Dirac mass at
block zero. -/
def physicalMeasurableBlockMassProfile (p : Params)
    (i : Fin (PhysicalDimension p)) :
    HermitianMatrix (PhysicalIndex p) → ProbabilityMeasure (Fin p.n) :=
  Function.extend (Subtype.val : physicalSimpleSpectrumMatrices p →
      HermitianMatrix (PhysicalIndex p))
    (physicalSimpleBlockMassProfile p i)
    (fun _ => defaultPhysicalBlockMassProfile p)

/-- The canonical probability-valued profile is globally measurable, including
at repeated spectra where it uses the fixed default mark. -/
theorem measurable_physicalMeasurableBlockMassProfile (p : Params)
    (i : Fin (PhysicalDimension p)) :
    Measurable (physicalMeasurableBlockMassProfile p i) := by
  exact (MeasurableEmbedding.subtype_coe
      (measurableSet_physicalSimpleSpectrumMatrices p)).measurable_extend
    (measurable_physicalSimpleBlockMassProfile p i) measurable_const

/-- On simple spectrum the total profile is exactly the canonical phase-fixed
ordered-eigenvector block-mass profile. -/
theorem physicalMeasurableBlockMassProfile_apply_simple (p : Params)
    (i : Fin (PhysicalDimension p))
    (A : physicalSimpleSpectrumMatrices p) :
    physicalMeasurableBlockMassProfile p i A.1 =
      physicalSimpleBlockMassProfile p i A := by
  simp [physicalMeasurableBlockMassProfile]

/-- Canonical measurable block-mass mark of the normalized physical matrix. -/
def Law.physicalMeasurableOrderedBlockMassProfile {p : Params} (M : Law p)
    (ω : M.Ω) (i : Fin (PhysicalDimension p)) :
    ProbabilityMeasure (Fin p.n) :=
  physicalMeasurableBlockMassProfile p i (M.normalizedPhysicalMatrix ω)

/-- Every canonical physical ordered block-mass mark is measurable. -/
theorem Law.measurable_physicalMeasurableOrderedBlockMassProfile
    {p : Params} (M : Law p) (i : Fin (PhysicalDimension p)) :
    Measurable (fun ω => M.physicalMeasurableOrderedBlockMassProfile ω i) :=
  (measurable_physicalMeasurableBlockMassProfile p i).comp
    M.measurable_normalizedPhysicalMatrix

/-- Unconditionally measurable eigenvector-mass marked physical spectrum.  Its
locations use the increasing physical spectrum; its marks use the canonical
phase-fixed eigenline on simple spectrum and a fixed probability mark at
collisions. -/
def Law.physicalMeasurableEigenvectorMassMarkedConfiguration
    {p : Params} (M : Law p) (e L ρ : ℝ) (ω : M.Ω) :
    FiniteMarkedConfiguration (PhysicalDimension p)
      (ProbabilityMeasure (Fin p.n)) :=
  fun i =>
    (L * ρ * (Real.sqrt p.c *
      orderedEigenvalue (M.normalizedPhysicalMatrix ω) i - e),
      M.physicalMeasurableOrderedBlockMassProfile ω i)

/-- The canonical eigenvector-mass marked finite configuration is measurable,
with no measurability hypothesis on the eigenbasis. -/
theorem Law.measurable_physicalMeasurableEigenvectorMassMarkedConfiguration
    {p : Params} (M : Law p) (e L ρ : ℝ) :
    Measurable (M.physicalMeasurableEigenvectorMassMarkedConfiguration e L ρ) := by
  rw [measurable_pi_iff]
  intro i
  have hloc : Measurable (fun ω =>
      L * ρ * (Real.sqrt p.c *
        orderedEigenvalue (M.normalizedPhysicalMatrix ω) i - e)) :=
    ((((measurable_orderedEigenvalue i).comp
      M.measurable_normalizedPhysicalMatrix).const_mul _).sub
        measurable_const).const_mul _
  exact hloc.prodMk
    (M.measurable_physicalMeasurableOrderedBlockMassProfile i)

/-- Rational-window state encoding of the canonical measurable physical
mass-profile marked spectrum. -/
def Law.physicalMeasurableEigenvectorMassProfileState
    {p : Params} (M : Law p) (e L ρ : ℝ) (ω : M.Ω) :
    LocalWindowMeasureEncoding (ProbabilityMeasure (Fin p.n)) :=
  finiteMarkedLocalWindowEncoding
    (M.physicalMeasurableEigenvectorMassMarkedConfiguration e L ρ ω)

/-- The rational-window state encoding of canonical mass-profile marks is
unconditionally measurable. -/
theorem Law.measurable_physicalMeasurableEigenvectorMassProfileState
    {p : Params} (M : Law p) (e L ρ : ℝ) :
    Measurable (M.physicalMeasurableEigenvectorMassProfileState e L ρ) :=
  (measurable_finiteMarkedLocalWindowEncoding (PhysicalDimension p)).comp
    (M.measurable_physicalMeasurableEigenvectorMassMarkedConfiguration e L ρ)

end GaussianRing
end CoareaNative.BlockBand
