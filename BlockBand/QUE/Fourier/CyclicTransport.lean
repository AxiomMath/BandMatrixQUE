module
public import BlockBand.QUE.Haar.ProjectorTransport
public import BlockBand.QUE.Invariance.CyclicLaw
public import BlockBand.Model.Construction.SpectralProfiles
public import Mathlib.LinearAlgebra.Matrix.Permutation
/-!
# Cyclic covariance of the selected-rank masses

Conjugating by a cyclic site permutation reindexes the site masses of the eigenvector of each
increasing rank, so under every physical Gaussian law the block masses are cyclically covariant
(`physical_blockMass_cyclic_ae`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Fourier
open Matrix MeasureTheory BlockBand.Model.Construction

/-- The site-permutation matrix, as a complex unitary. -/
def sitePermutationUnitary (p : Parameters) (e : p.Site ≃ p.Site) :
    Matrix.unitaryGroup p.Site ℂ := by
  refine ⟨Equiv.Perm.permMatrix ℂ e, Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  change (Equiv.Perm.permMatrix ℂ e)ᴴ * Equiv.Perm.permMatrix ℂ e = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- Conjugation by the permutation unitary is site reindexing. -/
theorem sitePermutation_conjugation (p : Parameters) (e : p.Site ≃ p.Site)
    (H : p.SiteMatrix) :
    (sitePermutationUnitary p e : p.SiteMatrix) * H *
      (sitePermutationUnitary p e : p.SiteMatrix)ᴴ = p.siteReindexMatrix e H := by
  change Equiv.Perm.permMatrix ℂ e * H * (Equiv.Perm.permMatrix ℂ e)ᴴ = _
  rw [Matrix.conjTranspose_permMatrix]
  change e.toPEquiv.toMatrix * H * e.symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- The site masses of the eigenvector of each increasing rank translate with the matrix. -/
theorem physical_siteMass_cyclic (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable)
    (α : Fin p.N) (s : ZMod p.n) (x : p.Site) :
    ‖physicalOrderedEigenvector p (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) α x‖ ^ 2 =
      ‖physicalOrderedEigenvector p H α (p.cyclicSiteEquiv s x)‖ ^ 2 := by
  rw [← sitePermutation_conjugation]
  rw [BlockBand.QUE.Haar.physicalOrderedEigenvector_unitary_mass p H hH hsep]
  change ‖(Equiv.Perm.permMatrix ℂ (p.cyclicSiteEquiv s) *ᵥ physicalOrderedEigenvector p H α) x‖ ^ 2 = _
  rw [Matrix.permMatrix_mulVec]
  rfl

/-- The block masses translate with the matrix. -/
theorem physical_blockMass_cyclic (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable)
    (α : Fin p.N) (s k : ZMod p.n) :
    physicalOrderedBlockMass p (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) α k =
      physicalOrderedBlockMass p H α (k + s) := by
  unfold physicalOrderedBlockMass
  apply Finset.sum_congr rfl
  intro a _
  exact physical_siteMass_cyclic p H hH hsep α s (k, a)

/-- Cyclic mass covariance under every physical Gaussian law. -/
theorem physical_blockMass_cyclic_ae (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (s : ZMod p.n) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ k,
      physicalOrderedBlockMass p (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) α k =
        physicalOrderedBlockMass p H α (k + s) := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  exact fun k => physical_blockMass_cyclic p H hH hsep α s k
end BlockBand.QUE.Fourier
