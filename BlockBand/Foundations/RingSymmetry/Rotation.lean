module

public import BlockBand.Internal.Contracts.RingSymmetry
public import BlockBand.QUE.Fourier.CyclicTransport
public import BlockBand.QUE.Fourier.PhysicalWeightedMass

/-!
# Finite-`W` ring rotation invariance

We prove `RingRotationInvariance` (`ringRotationInvariance_holds`), with no hypothesis, for every
admissible `p`, every exact physical law `model.law` and every block shift `s`. The proof uses
the following results of other modules:
* `GaussianRingModel.map_cyclicMatrix`: `model.law` is invariant under the block rotation (the
  Gaussian entry law is invariant under the variance-preserving site permutation);
* `physical_eigenvalue_cyclic`, `physical_blockMass_cyclic`: on Hermitian matrices with
  separable characteristic polynomial (simple spectrum) the rotation keeps the increasing
  eigenvalues and shifts the selected block masses by `s` (the selected eigenvector is unique up
  to a phase); the first field of `model.isPhysical` and `model.ae_charpoly_separable`: these hold almost surely.
The integral identities hold for every functional `F`: the rotation is a measurable equivalence
preserving `model.law` (`MeasurePreserving.integral_comp`, `lintegral_comp_emb`), and the two
integrands agree almost surely.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Foundations.RingSymmetry

open MeasureTheory BlockBand.Model.Construction BlockBand.Internal.Contracts.RingSymmetry
open scoped ENNReal

/-- The block rotation as a measurable equivalence of `p.SiteMatrix` (inverse: rotation by
`-s`). -/
def ringRotationEquiv (p : Parameters) (s : ZMod p.n) : p.SiteMatrix ≃ᵐ p.SiteMatrix where
  toFun := ringRotation p s
  invFun := ringRotation p (-s)
  left_inv H := by
    funext x y
    simp [ringRotation, Parameters.siteReindexMatrix, Parameters.cyclicSiteEquiv]
  right_inv H := by
    funext x y
    simp [ringRotation, Parameters.siteReindexMatrix, Parameters.cyclicSiteEquiv]
  measurable_toFun := p.measurable_siteReindexMatrix _
  measurable_invFun := p.measurable_siteReindexMatrix _

/-- The rotation preserves the exact physical law. -/
theorem measurePreserving_ringRotation {p : Parameters} (model : p.GaussianRingModel)
    (s : ZMod p.n) :
    MeasurePreserving (ringRotation p s) (model.law : Measure p.SiteMatrix)
      (model.law : Measure p.SiteMatrix) :=
  ⟨p.measurable_siteReindexMatrix _, model.map_cyclicMatrix s⟩

/-- Almost surely the rotation keeps the eigenvalues and shifts the block masses by `s`. -/
theorem ae_ringRotation_spectral {p : Parameters} (model : p.GaussianRingModel) (s : ZMod p.n) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      eigenvalueVector p (ringRotation p s H) = eigenvalueVector p H ∧
      ∀ (α : Fin p.N) (k : ZMod p.n),
        blockMassMatrix p (ringRotation p s H) α k = blockMassMatrix p H α (k + s) := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  refine ⟨?_, fun α k => ?_⟩
  · funext α
    exact BlockBand.QUE.Fourier.physical_eigenvalue_cyclic p H hH α s
  · exact BlockBand.QUE.Fourier.physical_blockMass_cyclic p H hH hsep α s k

/-- **Ring rotation invariance** `RingRotationInvariance`, with no hypothesis. -/
theorem ringRotationInvariance_holds : RingRotationInvariance := by
  intro p model s
  have hmp := measurePreserving_ringRotation model s
  have hemb : MeasurableEmbedding (ringRotation p s) := (ringRotationEquiv p s).measurableEmbedding
  have hae := ae_ringRotation_spectral model s
  refine ⟨model.map_cyclicMatrix s, hae, fun F => ?_, fun F => ?_⟩
  · have hcongr : (fun H => F (eigenvalueVector p H) (fun α k => blockMassMatrix p H α (k + s)))
        =ᵐ[(model.law : Measure p.SiteMatrix)]
        fun H => F (eigenvalueVector p (ringRotation p s H))
          (blockMassMatrix p (ringRotation p s H)) := by
      filter_upwards [hae] with H hH
      rw [hH.1]
      congr 1
      funext α k
      exact (hH.2 α k).symm
    rw [integral_congr_ae hcongr]
    exact hmp.integral_comp hemb (fun H => F (eigenvalueVector p H) (blockMassMatrix p H))
  · have hcongr : (fun H => F (eigenvalueVector p H) (fun α k => blockMassMatrix p H α (k + s)))
        =ᵐ[(model.law : Measure p.SiteMatrix)]
        fun H => F (eigenvalueVector p (ringRotation p s H))
          (blockMassMatrix p (ringRotation p s H)) := by
      filter_upwards [hae] with H hH
      rw [hH.1]
      congr 1
      funext α k
      exact (hH.2 α k).symm
    rw [lintegral_congr_ae hcongr]
    exact hmp.lintegral_comp_emb hemb (fun H => F (eigenvalueVector p H) (blockMassMatrix p H))

end BlockBand.Foundations.RingSymmetry
