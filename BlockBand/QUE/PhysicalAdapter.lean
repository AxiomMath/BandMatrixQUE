module

public import BlockBand.QUE.SiteDecomposition
public import BlockBand.Model.Observables

/-!
# The physical QUE statistic as a finite quadratic statistic

The QUE statistic of the physical model is the centred finite quadratic statistic
`quadraticStatistic` of the site masses `|u_α(b, a)|²`, under the physical law and with the
baseline `1/(nW)` (`queStatistic_eq_quadraticStatistic`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE

open MeasureTheory
open scoped BigOperators

/-- The squared coordinate norm of the ordered eigenvector of the physical model. -/
def physicalSiteMass {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (α : Fin p.N)
    (H : p.SiteMatrix) (x : p.Site) : ℝ :=
  ‖spectral.eigenvector H α x‖ ^ 2

/-- The physical QUE statistic is the centred finite quadratic statistic, under the physical law
and with the site baseline `1/(nW)`. -/
theorem queStatistic_eq_quadraticStatistic {p : Parameters}
    {model : p.GaussianRingModel} (spectral : p.SpectralRealization model)
    (α : Fin p.N) (v : p.Site → ℝ) :
    spectral.queStatistic α v =
      quadraticStatistic (model.law : Measure p.SiteMatrix)
        (physicalSiteMass spectral α) (p.N : ℝ)⁻¹ v := by
  unfold Parameters.SpectralRealization.queStatistic quadraticStatistic
  congr 1
  funext H
  unfold fluctuation physicalSiteMass
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [mul_comm (∑ x, v x) ((p.N : ℝ)⁻¹)]

end BlockBand.QUE
