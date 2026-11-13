module

public import BlockBand.Model.Construction.SpectralSelection
public import BlockBand.Model.Construction.OrderedSimpleSpectrum

/-!
# Exact physical-domain spectral observables

The domain is raw matrices on p.Site with n≥4, W≥1 and 0<b<1/2. Eigenvalues
are increasing ranks of raw H, without H/sqrt(c) normalization. The explicit
selected vectors carry measurable coordinates/site masses, and their exact
finite algebra holds on Hermitian matrices with separable characteristic
polynomial. Ordering is almost sure for every exact GaussianRingModel, using
only its proved Hermitian support. Sparse discriminant-null, Torus profile and
marked-configuration construction remain separate obligations.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open MeasureTheory

/-- Physical sites have exactly the total dimension nW. -/
theorem physicalSite_card (p : Parameters) : Fintype.card p.Site = p.N := by
  simp [Parameters.Site, Parameters.N]

/-- Convert physical ranks to the exact finite-spectrum rank type. -/
def physicalSpectralRank (p : Parameters) (α : Fin p.N) : Fin (Fintype.card p.Site) :=
  Fin.cast (physicalSite_card p).symm α

/-- Increasing raw-H eigenvalue observable on every physical matrix. -/
def physicalOrderedEigenvalue (p : Parameters) (H : p.SiteMatrix) (α : Fin p.N) : ℝ :=
  rawIncreasingEigenvalue (physicalSpectralRank p α) H

/-- Explicit measurable increasing-rank eigenvector observable, with fixed defaults. -/
def physicalOrderedEigenvector (p : Parameters) (H : p.SiteMatrix)
    (α : Fin p.N) (x : p.Site) : ℂ :=
  rawOrderedColumnSelection (physicalSpectralRank p α) H x

/-- Each exact physical raw-H eigenvalue coordinate is Borel measurable. -/
theorem measurable_physicalOrderedEigenvalue (p : Parameters) (α : Fin p.N) :
    Measurable (fun H => physicalOrderedEigenvalue p H α) :=
  measurable_rawIncreasingEigenvalue _

/-- Each explicit physical eigenvector coordinate is Borel measurable. -/
theorem measurable_physicalOrderedEigenvector (p : Parameters)
    (α : Fin p.N) (x : p.Site) :
    Measurable (fun H => physicalOrderedEigenvector p H α x) :=
  measurable_rawOrderedColumnSelection _ x

/-- Each physical site mass is Borel measurable in the exact raw-H domain. -/
theorem measurable_physicalOrderedSiteMass (p : Parameters)
    (α : Fin p.N) (x : p.Site) :
    Measurable (fun H => ‖physicalOrderedEigenvector p H α x‖ ^ 2) :=
  measurable_rawOrderedSiteMass _ x

/-- Increasing order holds almost surely under every exact physical Gaussian
model; simplicity is unnecessary and no spectral input wrapper is assumed. -/
theorem physicalOrderedEigenvalue_monotone_ae (p : Parameters)
    (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ α β : Fin p.N, α ≤ β →
        physicalOrderedEigenvalue p H α ≤ physicalOrderedEigenvalue p H β := by
  filter_upwards [model.isPhysical.1] with H hH
  intro α β hab
  unfold physicalOrderedEigenvalue
  rw [rawIncreasingEigenvalue_eq _ H hH, rawIncreasingEigenvalue_eq _ H hH]
  apply BlockBand.Foundations.Spectral.increasingEigenvalue_monotone hH
  exact hab

/-- Exact conjugate-first orthonormality for the explicit physical selection
on each Hermitian matrix with separable characteristic polynomial. -/
theorem physicalOrderedEigenvector_orthonormal (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) (α β : Fin p.N) :
    (∑ x, starRingEnd ℂ (physicalOrderedEigenvector p H α x) *
      physicalOrderedEigenvector p H β x) = if α = β then 1 else 0 := by
  unfold physicalOrderedEigenvector
  simp_rw [rawOrderedColumnSelection_eq _ H hH]
  have hs := orderedEigenvalue_injective_of_separable (⟨H, hH⟩ : HermitianMatrix p.Site) hsep
  have h := orderedColumnSelection_orthonormal
    (physicalSpectralRank p α) (physicalSpectralRank p β) ⟨H, hH⟩ hs
  simpa only [physicalSpectralRank, Fin.cast_inj] using h

/-- Unit total mass for every explicit physical rank on the simple spectrum. -/
theorem physicalOrderedEigenvector_totalMass (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) (α : Fin p.N) :
    (∑ x, ‖physicalOrderedEigenvector p H α x‖ ^ 2) = 1 := by
  unfold physicalOrderedEigenvector
  simp_rw [rawOrderedColumnSelection_eq _ H hH]
  exact sum_norm_sq_orderedColumnSelection _ ⟨H, hH⟩
    (orderedEigenvalue_injective_of_separable _ hsep)

/-- The explicit physical eigenvector solves the exact raw-H eigen-equation. -/
theorem physicalOrderedEigenvector_eigenvector (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) (α : Fin p.N) (x : p.Site) :
    H.mulVec (physicalOrderedEigenvector p H α) x =
      (physicalOrderedEigenvalue p H α : ℂ) * physicalOrderedEigenvector p H α x := by
  unfold physicalOrderedEigenvector physicalOrderedEigenvalue
  simp_rw [rawOrderedColumnSelection_eq _ H hH, rawIncreasingEigenvalue_eq _ H hH]
  have h := mulVec_orderedColumnSelection (physicalSpectralRank p α) ⟨H, hH⟩
    (orderedEigenvalue_injective_of_separable _ hsep)
  exact congrFun h x

end BlockBand.Model.Construction
