module

public import BlockBand.Model.Construction.SpectralMarkedData

/-!
# The measurable physical spectral realization

For every physical Gaussian model, a spectral realization (`SpectralRealization`) with all its
measurability and almost-sure fields is constructed from the explicit ordered eigenvector
selection and profiles.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

/-- Constructor for every field of the finite physical spectral realization, from the physical
Gaussian model alone. -/
def constructSpectralRealization (p : Parameters) (model : p.GaussianRingModel) :
    p.SpectralRealization model where
  eigenvalue := physicalOrderedEigenvalue p
  eigenvector := physicalOrderedEigenvector p
  profile := physicalOrderedProfile p
  markedConfig := physicalOrderedMarkedConfig p
  measurable_eigenvalue := measurable_physicalOrderedEigenvalue p
  measurable_siteMass := measurable_physicalOrderedSiteMass p
  measurable_markedConfig := measurable_physicalOrderedMarkedConfig p
  orthonormal_ae := physicalOrderedEigenvector_orthonormal_ae p model
  eigenvector_ae := physicalOrderedEigenvector_eigenvector_ae p model
  ordered_ae := physicalOrderedEigenvalue_monotone_ae p model
  profile_ae := physicalOrderedProfile_ae p model
  markedConfig_ae := physicalOrderedMarkedConfig_ae p model

/-- Existence of measurable physical spectral data for every physical Gaussian law. -/
theorem nonempty_spectralRealization (p : Parameters) (model : p.GaussianRingModel) :
    Nonempty (p.SpectralRealization model) := ⟨constructSpectralRealization p model⟩

end BlockBand.Model.Construction
