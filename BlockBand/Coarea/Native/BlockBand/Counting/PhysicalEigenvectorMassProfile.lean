module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalUnfoldedRestrictionExponential
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Physical eigenvector block-mass profiles

This module begins the correction from trivially marked physical spectra to the
paper's eigenvector marks.  An increasing ordered eigenvalue is paired with the
corresponding vector in Mathlib's orthonormal Hermitian eigenbasis.  Its squared
coordinate norms are summed inside each physical block, giving nonnegative weights of
total mass one and hence a probability measure on the finite block-index space.

The resulting finite marked configuration is a finite Gaussian-ring spectral
configuration.  Mathlib's chosen Hermitian eigenbasis is not currently known here to
vary measurably with the matrix, especially across repeated eigenvalues.  Accordingly
measurability is recorded as an explicit predicate and no pushforward law or limit
closure is claimed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The normalized eigenvector paired with the `i`th *increasing* ordered eigenvalue.
Mathlib indexes its Hermitian eigenbasis by the original finite type and its sorted
spectrum in decreasing order, so both the cardinality equivalence and `Fin.rev` are
visible in the definition. -/
def orderedNormalizedEigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (i : Fin (Fintype.card ι)) :
    EuclideanSpace ℂ ι :=
  A.property.eigenvectorBasis
    (Fintype.equivOfCardEq (Fintype.card_fin _) i.rev)

/-- The selected vector is an eigenvector for the corresponding increasing ordered
eigenvalue. -/
theorem orderedNormalizedEigenvector_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (i : Fin (Fintype.card ι)) :
    (A : Matrix ι ι ℂ) *ᵥ (orderedNormalizedEigenvector A i) =
      (orderedEigenvalue A i : ℂ) • orderedNormalizedEigenvector A i := by
  simpa [orderedNormalizedEigenvector, orderedEigenvalue,
    Matrix.IsHermitian.eigenvalues] using
      A.property.mulVec_eigenvectorBasis
        (Fintype.equivOfCardEq (Fintype.card_fin _) i.rev)

/-- The selected ordered vector has Euclidean norm one, including at repeated
spectra. -/
@[simp] theorem norm_orderedNormalizedEigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (i : Fin (Fintype.card ι)) :
    ‖orderedNormalizedEigenvector A i‖ = 1 := by
  exact A.property.eigenvectorBasis.norm_eq_one _

/-- The mass assigned by an ordered normalized eigenvector to one physical block. -/
def physicalBlockMassWeight (p : Params)
    (v : EuclideanSpace ℂ (BlockGUE.Index (physicalBlockSizes p)))
    (k : Fin p.n) : NNReal :=
  ∑ a : Fin (physicalBlockSizes p k), ‖v ⟨k, a⟩‖₊ ^ 2

/-- Block masses are nonnegative. -/
theorem physicalBlockMassWeight_nonneg (p : Params)
    (v : EuclideanSpace ℂ (BlockGUE.Index (physicalBlockSizes p)))
    (k : Fin p.n) : 0 ≤ physicalBlockMassWeight p v k :=
  (physicalBlockMassWeight p v k).2

/-- The block masses of a unit vector sum to one. -/
theorem sum_physicalBlockMassWeight_eq_one (p : Params)
    (v : EuclideanSpace ℂ (BlockGUE.Index (physicalBlockSizes p)))
    (hv : ‖v‖ = 1) :
    ∑ k : Fin p.n, physicalBlockMassWeight p v k = 1 := by
  apply NNReal.eq
  simp only [physicalBlockMassWeight, NNReal.coe_sum, NNReal.coe_pow,
    coe_nnnorm]
  rw [← Fintype.sum_sigma']
  rw [← EuclideanSpace.norm_sq_eq v, hv]
  norm_num

/-- The physical block-mass profile of one ordered normalized eigenvector, as a
probability measure on the finite cyclic block-index set. -/
def physicalBlockMassProfile (p : Params)
    (A : HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (i : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p)))) :
    ProbabilityMeasure (Fin p.n) := by
  let w : Fin p.n → NNReal := fun k =>
    physicalBlockMassWeight p (orderedNormalizedEigenvector A i) k
  have hsum : ∑ k, w k = 1 :=
    sum_physicalBlockMassWeight_eq_one p (orderedNormalizedEigenvector A i)
      (norm_orderedNormalizedEigenvector A i)
  have hhas : HasSum w 1 := by
    simpa [hsum] using (hasSum_fintype w)
  exact ⟨Measure.sum fun k => w k • Measure.dirac k,
    hhas.isProbabilityMeasure_sum_dirac_nnreal⟩

/-- Evaluation on one block singleton recovers its squared-coordinate mass. -/
theorem physicalBlockMassProfile_singleton (p : Params)
    (A : HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (i : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p))))
    (k : Fin p.n) :
    physicalBlockMassProfile p A i {k} =
      physicalBlockMassWeight p (orderedNormalizedEigenvector A i) k := by
  classical
  simp [physicalBlockMassProfile]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The profile has total mass one. -/
@[simp] theorem physicalBlockMassProfile_univ (p : Params)
    (A : HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (i : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p)))) :
    physicalBlockMassProfile p A i Set.univ = 1 :=
  ProbabilityMeasure.coeFn_univ _

/-- The normalized physical matrix's `i`th ordered eigenvector profile. -/
def Law.physicalOrderedBlockMassProfile {p : Params} (M : Law p)
    (ω : M.Ω)
    (i : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p)))) :
    ProbabilityMeasure (Fin p.n) :=
  physicalBlockMassProfile p (M.normalizedPhysicalMatrix ω) i

/-- The paper-corrected finite marked spectrum: unfolded eigenvalue locations are
marked by their physical block-mass probability profiles. -/
def Law.physicalEigenvectorMassMarkedConfiguration {p : Params} (M : Law p)
    (e L ρ : ℝ) (ω : M.Ω) :
    FiniteMarkedConfiguration
      (Fintype.card (BlockGUE.Index (physicalBlockSizes p)))
      (ProbabilityMeasure (Fin p.n)) :=
  fun i =>
    (L * ρ * (Real.sqrt p.c *
      orderedEigenvalue (M.normalizedPhysicalMatrix ω) i - e),
      M.physicalOrderedBlockMassProfile ω i)

/-- The spectral location of the corrected marked configuration is exactly the existing
physical unfolded location. -/
@[simp] theorem Law.physicalEigenvectorMassMarkedConfiguration_fst
    {p : Params} (M : Law p) (e L ρ : ℝ) (ω : M.Ω)
    (i : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p)))) :
    (M.physicalEigenvectorMassMarkedConfiguration e L ρ ω i).1 =
      L * ρ * (Real.sqrt p.c *
        orderedEigenvalue (M.normalizedPhysicalMatrix ω) i - e) := rfl

/-- Every mark in the corrected finite configuration is a probability measure of total
mass one. -/
@[simp] theorem Law.physicalEigenvectorMassMarkedConfiguration_mark_univ
    {p : Params} (M : Law p) (e L ρ : ℝ) (ω : M.Ω)
    (i : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p)))) :
    (M.physicalEigenvectorMassMarkedConfiguration e L ρ ω i).2 Set.univ = 1 :=
  ProbabilityMeasure.coeFn_univ _

/-- Measurability obligation for the eigenvector-profile marks.  It is separated
from the algebraic construction because no global measurable choice of Mathlib's
Hermitian eigenbasis has been proved here. -/
def Law.PhysicalEigenvectorMassProfileMeasurable {p : Params} (M : Law p) : Prop :=
  ∀ i : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p))),
    Measurable (fun ω => M.physicalOrderedBlockMassProfile ω i)

/-- Once the explicit profile-measurability obligation is supplied, the entire corrected
finite marked configuration is measurable. -/
theorem Law.measurable_physicalEigenvectorMassMarkedConfiguration
    {p : Params} (M : Law p) (hprofile : M.PhysicalEigenvectorMassProfileMeasurable)
    (e L ρ : ℝ) :
    Measurable (M.physicalEigenvectorMassMarkedConfiguration e L ρ) := by
  rw [measurable_pi_iff]
  intro i
  have hloc : Measurable (fun ω =>
      L * ρ * (Real.sqrt p.c *
        orderedEigenvalue (M.normalizedPhysicalMatrix ω) i - e)) :=
    ((((measurable_orderedEigenvalue i).comp M.measurable_normalizedPhysicalMatrix).const_mul _).sub
      measurable_const).const_mul _
  exact hloc.prodMk (hprofile i)

end GaussianRing
end CoareaNative.BlockBand
