module

public import BlockBand.Model.Construction.SpectralPhysicalAE
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Torus probability profiles of the physical ordered selection

The block masses of the selected eigenvectors define, for each rank, a probability measure on the
torus supported on the grid `k/n`; it is measurable in the matrix and gives the almost-sure
profile identity under every physical Gaussian model.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open MeasureTheory
open scoped ENNReal

/-- The physical block mass, retaining all internal site coordinates. -/
def physicalOrderedBlockMass (p : Parameters) (H : p.SiteMatrix)
    (α : Fin p.N) (k : ZMod p.n) : ℝ :=
  ∑ a : Fin p.W, ‖physicalOrderedEigenvector p H α (k, a)‖ ^ 2

/-- The torus grid point `k/n`. -/
def physicalProfileGrid (p : Parameters) (k : ZMod p.n) : Torus :=
  QuotientAddGroup.mk ((k.val : ℝ) / p.n)

/-- Block masses are nonnegative even on the exceptional default matrices. -/
theorem physicalOrderedBlockMass_nonneg (p : Parameters) (H : p.SiteMatrix)
    (α : Fin p.N) (k : ZMod p.n) : 0 ≤ physicalOrderedBlockMass p H α k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Every raw-matrix block-mass coordinate is Borel measurable. -/
theorem measurable_physicalOrderedBlockMass (p : Parameters) (α : Fin p.N)
    (k : ZMod p.n) : Measurable (fun H => physicalOrderedBlockMass p H α k) := by
  apply Finset.measurable_sum
  intro a _
  exact measurable_physicalOrderedSiteMass p α (k, a)

/-- The block masses sum to one on every good physical matrix. -/
theorem physicalOrderedBlockMass_sum (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) (α : Fin p.N) :
    (∑ k, physicalOrderedBlockMass p H α k) = 1 := by
  rw [← physicalOrderedEigenvector_totalMass p H hH hsep α]
  exact (Fintype.sum_prod_type (fun x : p.Site =>
    ‖physicalOrderedEigenvector p H α x‖ ^ 2)).symm

/-- Almost-sure block mass normalization under the physical law, simultaneous in all ranks. -/
theorem physicalOrderedBlockMass_sum_ae (p : Parameters) (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ α : Fin p.N, (∑ k, physicalOrderedBlockMass p H α k) = 1 := by
  filter_upwards [physicalOrderedEigenvector_totalMass_ae p model] with H hH
  intro α
  rw [← hH α]
  exact (Fintype.sum_prod_type (fun x : p.Site =>
    ‖physicalOrderedEigenvector p H α x‖ ^ 2)).symm

/-- Unnormalized finite weighted Dirac profile measure on all raw matrices. -/
def physicalOrderedProfileMeasure (p : Parameters) (H : p.SiteMatrix)
    (α : Fin p.N) : Measure Torus :=
  ∑ k : ZMod p.n, ENNReal.ofReal (physicalOrderedBlockMass p H α k) •
    Measure.dirac (physicalProfileGrid p k)

/-- The good locus: Hermitian `H` with separable characteristic polynomial. -/
def physicalProfileGood (p : Parameters) (H : p.SiteMatrix) : Prop :=
  H.IsHermitian ∧ H.charpoly.Separable

/-- Total profile measure is one on the good locus. -/
theorem physicalOrderedProfileMeasure_univ (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) (α : Fin p.N) :
    physicalOrderedProfileMeasure p H α Set.univ = 1 := by
  simp only [physicalOrderedProfileMeasure, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => physicalOrderedBlockMass_nonneg p H α k),
    physicalOrderedBlockMass_sum p H hH hsep α]
  norm_num

/-- The probability-valued profile of each rank, with the Dirac mass at zero as default. -/
def physicalOrderedProfile (p : Parameters) (H : p.SiteMatrix)
    (α : Fin p.N) : MassProfile := by
  classical
  exact if h : physicalProfileGood p H then
    ⟨physicalOrderedProfileMeasure p H α,
      (isProbabilityMeasure_iff).mpr (physicalOrderedProfileMeasure_univ p H h.1 h.2 α)⟩
  else ⟨Measure.dirac (0 : Torus), inferInstance⟩

/-- The profile measure equals the exact block-mass Dirac sum on good matrices. -/
theorem physicalOrderedProfile_eq (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) (α : Fin p.N) :
    (physicalOrderedProfile p H α : Measure Torus) = physicalOrderedProfileMeasure p H α := by
  simp [physicalOrderedProfile, physicalProfileGood, hH, hsep]

/-- The default profile outside the Hermitian simple-spectrum locus is the Dirac mass at zero. -/
theorem physicalOrderedProfile_default (p : Parameters) (H : p.SiteMatrix)
    (hbad : ¬ physicalProfileGood p H) (α : Fin p.N) :
    (physicalOrderedProfile p H α : Measure Torus) = Measure.dirac (0 : Torus) := by
  simp [physicalOrderedProfile, hbad]

/-- Integration of continuous tests against the physical profile. -/
theorem physicalOrderedProfile_integral (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) (α : Fin p.N)
    (φ : ContinuousMap Torus ℝ) :
    (∫ r, φ r ∂(physicalOrderedProfile p H α : Measure Torus)) =
      ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k * φ (physicalProfileGrid p k) := by
  rw [physicalOrderedProfile_eq p H hH hsep α]
  unfold physicalOrderedProfileMeasure
  rw [integral_finsetSum_measure (fun k _ =>
    (integrable_dirac (by simp)).smul_measure (ENNReal.ofReal_ne_top))]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (physicalOrderedBlockMass_nonneg p H α _), smul_eq_mul]

/-- The almost-sure profile identity under every physical Gaussian model, uniformly in all
increasing ranks and all continuous real torus tests. -/
theorem physicalOrderedProfile_ae (p : Parameters) (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ α : Fin p.N, ∀ φ : ContinuousMap Torus ℝ,
        (∫ r, φ r ∂(physicalOrderedProfile p H α : Measure Torus)) =
          ∑ k : ZMod p.n,
            (∑ a : Fin p.W, ‖physicalOrderedEigenvector p H α (k, a)‖ ^ 2) *
              φ (QuotientAddGroup.mk ((k.val : ℝ) / p.n)) := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  exact fun α φ => physicalOrderedProfile_integral p H hH hsep α φ

/-- Every finite weighted profile measure is Giry measurable by its evaluations. -/
theorem measurable_physicalOrderedProfileMeasure (p : Parameters) (α : Fin p.N) :
    Measurable (fun H => physicalOrderedProfileMeasure p H α) := by
  apply Finset.measurable_sum
  intro k _
  exact (ENNReal.measurable_ofReal.comp
    (measurable_physicalOrderedBlockMass p α k)).smul_measure _

/-- Injective ordered ranks imply separability. -/
theorem charpoly_separable_of_injective_orderedEigenvalue
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : HermitianMatrix ι)
    (hs : Function.Injective (orderedEigenvalue A)) : A.val.charpoly.Separable := by
  rw [A.property.charpoly_eq, Polynomial.separable_prod_X_sub_C_iff]
  intro x y hxy
  apply BlockBand.Foundations.Spectral.increasingIndex.symm.injective
  apply hs
  change BlockBand.Foundations.Spectral.increasingEigenvalue A.property
      (BlockBand.Foundations.Spectral.increasingIndex.symm x) =
    BlockBand.Foundations.Spectral.increasingEigenvalue A.property
      (BlockBand.Foundations.Spectral.increasingIndex.symm y)
  rw [← BlockBand.Foundations.Spectral.eigenvalue_increasingIndex,
    ← BlockBand.Foundations.Spectral.eigenvalue_increasingIndex,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact Complex.ofReal_injective hxy

/-- Raw increasing-rank injectivity is a Borel event. -/
theorem measurableSet_rawIncreasingEigenvalue_injective (p : Parameters) :
    MeasurableSet {H : p.SiteMatrix |
      Function.Injective (fun i => rawIncreasingEigenvalue (ι := p.Site) i H)} := by
  have hs : {H : p.SiteMatrix |
      Function.Injective (fun i => rawIncreasingEigenvalue (ι := p.Site) i H)} =
      ⋂ i : Fin (Fintype.card p.Site), ⋂ j : Fin (Fintype.card p.Site), ⋂ (_ : i ≠ j),
        {H | rawIncreasingEigenvalue i H ≠ rawIncreasingEigenvalue j H} := by
    ext H
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i j hij heq
      exact hij (h heq)
    · intro h i j heq
      by_contra hij
      exact h i j hij heq
  rw [hs]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ =>
      (measurableSet_eq_fun (measurable_rawIncreasingEigenvalue i)
        (measurable_rawIncreasingEigenvalue j)).compl

/-- The Hermitian separable good locus is Borel. -/
theorem measurableSet_physicalProfileGood (p : Parameters) :
    MeasurableSet {H : p.SiteMatrix | physicalProfileGood p H} := by
  have hs : {H : p.SiteMatrix | physicalProfileGood p H} =
      {H | H.IsHermitian} ∩ {H | Function.Injective
        (fun i => rawIncreasingEigenvalue (ι := p.Site) i H)} := by
    ext H
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      have hi := orderedEigenvalue_injective_of_separable (⟨H, h.1⟩ : HermitianMatrix p.Site) h.2
      intro i j hij
      apply hi
      simpa only [rawIncreasingEigenvalue_eq _ H h.1, orderedEigenvalue] using hij
    · intro h
      refine ⟨h.1, ?_⟩
      apply charpoly_separable_of_injective_orderedEigenvalue (⟨H, h.1⟩ : HermitianMatrix p.Site)
      intro i j hij
      apply h.2
      simpa only [rawIncreasingEigenvalue_eq _ H h.1, orderedEigenvalue] using hij
  rw [hs]
  exact measurableSet_isHermitian.inter (measurableSet_rawIncreasingEigenvalue_injective p)

/-- The probability-valued profile is measurable for the Giry σ-algebra. -/
theorem measurable_physicalOrderedProfile (p : Parameters) (α : Fin p.N) :
    Measurable (fun H => physicalOrderedProfile p H α) := by
  classical
  have hm : Measurable (fun H : p.SiteMatrix =>
      if physicalProfileGood p H then physicalOrderedProfileMeasure p H α
      else Measure.dirac (0 : Torus)) :=
    (measurable_physicalOrderedProfileMeasure p α).piecewise
      (measurableSet_physicalProfileGood p) measurable_const
  have he : (fun H : p.SiteMatrix =>
      (physicalOrderedProfile p H α : Measure Torus)) =
      (fun H => if physicalProfileGood p H then physicalOrderedProfileMeasure p H α
        else Measure.dirac (0 : Torus)) := by
    funext H
    by_cases h : physicalProfileGood p H <;> simp [physicalOrderedProfile, h]
  have hc : Measurable (fun H => (physicalOrderedProfile p H α : Measure Torus)) := by
    rw [he]
    exact hm
  exact hc.subtype_mk

end BlockBand.Model.Construction
