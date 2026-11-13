module

public import BlockBand.Model.GaussianRing
public import BlockBand.PointProcess.Vague

/-!
# Spectral observables of the physical model

A spectral realization fixes measurable ordered eigenpairs for the finite
Hermitian matrix. Its axioms are solely finite-dimensional spectral identities;
it contains no QUE, comparison, limiting, or endpoint assertion.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand

open MeasureTheory
open scoped ENNReal

namespace Parameters

/-- Semicircle density in the physical row-variance-one normalization. -/
def semicircleDensity (E : ℝ) : ℝ :=
  Real.sqrt (4 - E ^ 2) / (2 * Real.pi)

/-- A measurable ordered spectral realization and its exact finite marked
configuration. Degenerate matrices may use arbitrary defaults; all displayed
spectral identities are required almost surely under the Gaussian law. -/
structure SpectralRealization (p : Parameters) (model : p.GaussianRingModel) where
  eigenvalue : p.SiteMatrix → Fin p.N → ℝ
  eigenvector : p.SiteMatrix → Fin p.N → p.Site → ℂ
  profile : p.SiteMatrix → Fin p.N → MassProfile
  markedConfig : ℝ → p.SiteMatrix → MarkedPointMeasure
  measurable_eigenvalue : ∀ α, Measurable (fun H => eigenvalue H α)
  measurable_siteMass : ∀ α x, Measurable (fun H => ‖eigenvector H α x‖ ^ 2)
  measurable_markedConfig : ∀ E, Measurable (markedConfig E)
  orthonormal_ae :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ α β, (∑ x, starRingEnd ℂ (eigenvector H α x) * eigenvector H β x) =
        if α = β then 1 else 0
  eigenvector_ae :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ α x, (H.mulVec (eigenvector H α)) x =
        (eigenvalue H α : ℂ) * eigenvector H α x
  ordered_ae :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ α β, α ≤ β → eigenvalue H α ≤ eigenvalue H β
  profile_ae :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ α (φ : ContinuousMap Torus ℝ),
        ∫ r, φ r ∂(profile H α : Measure Torus) =
          ∑ k : ZMod p.n,
            (∑ a : Fin p.W, ‖eigenvector H α (k, a)‖ ^ 2) *
              φ (QuotientAddGroup.mk ((k.val : ℝ) / p.n))
  markedConfig_ae :
    ∀ E : ℝ,
      ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
        (markedConfig E H).marked.measure =
          ∑ α : Fin p.N, Measure.dirac
            (p.N * semicircleDensity E * (eigenvalue H α - E), profile H α)

/-- Physical unfolding `N ρ(E) (λ-E)`. -/
def SpectralRealization.unfoldedEigenvalue
    {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (E : ℝ)
    (H : p.SiteMatrix) (α : Fin p.N) : ℝ :=
  p.N * semicircleDensity E * (spectral.eigenvalue H α - E)

/-- The exact QUE quadratic statistic for a deterministic real site test. -/
def SpectralRealization.queStatistic
    {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model)
    (α : Fin p.N) (v : p.Site → ℝ) : ℝ :=
  ∫ H,
    |(∑ x, v x * ‖spectral.eigenvector H α x‖ ^ 2) -
      (p.N : ℝ)⁻¹ * ∑ x, v x| ^ 2
    ∂(model.law : Measure p.SiteMatrix)

end Parameters

end BlockBand
