module

public import BlockBand.Model.Construction.SpectralPhysical
public import BlockBand.Model.Construction.GaussianSimpleSpectrum

/-!
# Almost-sure spectral identities under the physical law

Under every physical Gaussian block-band law, the explicit Borel increasing eigenvector selection
is almost surely orthonormal, solves the eigenvalue equation with the increasing eigenvalues, and
has unit total site mass. This uses the almost-sure simplicity
`GaussianRingModel.ae_charpoly_separable`; it covers all finite admissible parameters and ranks.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open MeasureTheory

/-- Almost-sure orthonormality of the explicit physical spectral selection. -/
theorem physicalOrderedEigenvector_orthonormal_ae (p : Parameters)
    (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ α β : Fin p.N,
        (∑ x, starRingEnd ℂ (physicalOrderedEigenvector p H α x) *
          physicalOrderedEigenvector p H β x) = if α = β then 1 else 0 := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  exact fun α β => physicalOrderedEigenvector_orthonormal p H hH hsep α β

/-- The almost-sure eigenvalue equation, with the physical increasing eigenvalue. -/
theorem physicalOrderedEigenvector_eigenvector_ae (p : Parameters)
    (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ α : Fin p.N, ∀ x : p.Site,
        H.mulVec (physicalOrderedEigenvector p H α) x =
          (physicalOrderedEigenvalue p H α : ℂ) * physicalOrderedEigenvector p H α x := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  exact fun α x => physicalOrderedEigenvector_eigenvector p H hH hsep α x

/-- Almost-sure unit total site mass of the selected eigenvectors. -/
theorem physicalOrderedEigenvector_totalMass_ae (p : Parameters)
    (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ α : Fin p.N, (∑ x, ‖physicalOrderedEigenvector p H α x‖ ^ 2) = 1 := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  exact fun α => physicalOrderedEigenvector_totalMass p H hH hsep α

end BlockBand.Model.Construction
