module
public import BlockBand.QUE.Fourier.CyclicTransport
public import BlockBand.QUE.Fourier.PhysicalIntegrability
public import BlockBand.QUE.Fourier.CyclicMoments
/-!
# Cyclic Fourier moments of the physical model

Cyclic invariance of the physical law gives the orthogonality of distinct Fourier modes, the
mass-mode covariance with `1/n` normalization and the signed pair numerator for the block masses
of the selected eigenvector.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Fourier
open MeasureTheory BlockBand.Model.Construction

/-- Cyclic conjugation preserves the physical expectation of a measurable observable. -/
theorem integral_physical_cyclic (p : Parameters) (model : p.GaussianRingModel)
    (s : ZMod p.n) (F : p.SiteMatrix → ℂ) (hF : Measurable F) :
    (∫ H, F (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) ∂(model.law : Measure p.SiteMatrix)) =
      ∫ H, F H ∂(model.law : Measure p.SiteMatrix) := by
  have h := integral_map (p.measurable_siteReindexMatrix (p.cyclicSiteEquiv s)).aemeasurable
    (hF.aestronglyMeasurable : AEStronglyMeasurable F
      (Measure.map (p.siteReindexMatrix (p.cyclicSiteEquiv s)) (model.law : Measure p.SiteMatrix)))
  rw [model.map_cyclicMatrix s] at h
  exact h.symm

/-- The physical Fourier mode translates with the matrix, almost surely. -/
theorem physicalMode_cyclic_ae (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (s m : ZMod p.n) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      physicalMode p α m (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) =
        mode (fun k => (physicalOrderedBlockMass p H α (k + s) : ℂ)) m := by
  filter_upwards [physical_blockMass_cyclic_ae p model α s] with H hH
  unfold physicalMode
  congr 1
  funext k
  rw [hH k]

/-- Orthogonality of distinct physical Fourier modes, at the same rank. -/
theorem physical_expected_distinct_mode_orthogonality (p : Parameters)
    (model : p.GaussianRingModel) (α : Fin p.N) (r s : ZMod p.n) (hrs : r ≠ s) :
    (∫ H, physicalMode p α r H * starRingEnd ℂ (physicalMode p α s H)
      ∂(model.law : Measure p.SiteMatrix)) = 0 := by
  apply expected_distinct_mode_orthogonality (model.law : Measure p.SiteMatrix)
    (fun H k => (physicalOrderedBlockMass p H α k : ℂ)) r s hrs
  have h := integral_physical_cyclic p model 1
    (fun H => physicalMode p α r H * starRingEnd ℂ (physicalMode p α s H))
    ((measurable_physicalMode p α r).mul ((Complex.continuous_conj.measurable.comp (measurable_physicalMode p α s))))
  refine (integral_congr_ae ?_).trans h
  filter_upwards [physicalMode_cyclic_ae p model α 1 r,
    physicalMode_cyclic_ae p model α 1 s] with H hr hs
  rw [hr, hs]

/-- The mass-mode integral identity for all shifts, from law invariance and the covariance of the
selected projector. -/
theorem physical_mass_mode_shift (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (m a : ZMod p.n) :
    (∫ H, (physicalOrderedBlockMass p H α a : ℂ) *
      starRingEnd ℂ (mode (fun k => (physicalOrderedBlockMass p H α (k + a) : ℂ)) m)
      ∂(model.law : Measure p.SiteMatrix)) =
    ∫ H, (physicalOrderedBlockMass p H α 0 : ℂ) * starRingEnd ℂ (physicalMode p α m H)
      ∂(model.law : Measure p.SiteMatrix) := by
  have hf : Measurable (fun H => (physicalOrderedBlockMass p H α 0 : ℂ) *
      starRingEnd ℂ (physicalMode p α m H)) := by
    exact (measurable_physicalOrderedBlockMass p α 0).complex_ofReal.mul
      (Complex.continuous_conj.measurable.comp (measurable_physicalMode p α m))
  rw [← integral_physical_cyclic p model a _ hf]
  apply integral_congr_ae
  filter_upwards [physical_blockMass_cyclic_ae p model α a,
    physicalMode_cyclic_ae p model α a m] with H hmass hmode
  rw [hmode, hmass 0, zero_add]

/-- Physical cyclic covariance with the `1/n` normalization. -/
theorem physical_expected_mass_mode_covariance (p : Parameters)
    (model : p.GaussianRingModel) (α : Fin p.N) (m i : ZMod p.n) :
    (∫ H, (physicalOrderedBlockMass p H α i : ℂ) * starRingEnd ℂ (physicalMode p α m H)
      ∂(model.law : Measure p.SiteMatrix)) =
      ZMod.stdAddChar (i * m) * (p.n : ℂ)⁻¹ *
        (∫ H, physicalMode p α m H * starRingEnd ℂ (physicalMode p α m H)
          ∂(model.law : Measure p.SiteMatrix)) :=
  expected_mass_mode_covariance (model.law : Measure p.SiteMatrix)
    (fun H k => (physicalOrderedBlockMass p H α k : ℂ)) m i
    (fun k => integrable_physicalMass_mode p model α k m)
    (physical_mass_mode_shift p model α m)

/-- The physical signed numerator, with its `n/2` and `1/2` factors. -/
theorem physical_signed_pair_numerator (p : Parameters)
    (model : p.GaussianRingModel) (α : Fin p.N) (m i : ZMod p.n) :
    (p.n : ℂ) / 2 * (∫ H,
      ((physicalOrderedBlockMass p H α i : ℂ) - physicalOrderedBlockMass p H α (i + 1)) *
        starRingEnd ℂ (physicalMode p α m H) ∂(model.law : Measure p.SiteMatrix)) =
      (1 - ZMod.stdAddChar m) / 2 * ZMod.stdAddChar (i * m) *
        (∫ H, physicalMode p α m H * starRingEnd ℂ (physicalMode p α m H)
          ∂(model.law : Measure p.SiteMatrix)) :=
  signed_pair_numerator (model.law : Measure p.SiteMatrix)
    (fun H k => (physicalOrderedBlockMass p H α k : ℂ)) m i
    (fun k => integrable_physicalMass_mode p model α k m)
    (physical_mass_mode_shift p model α m)
/-- The complex diagonal covariance is the real squared-norm variance. -/
theorem physical_diagonal_covariance_eq_variance (p : Parameters)
    (model : p.GaussianRingModel) (α : Fin p.N) (m : ZMod p.n) :
    (∫ H, physicalMode p α m H * starRingEnd ℂ (physicalMode p α m H)
      ∂(model.law : Measure p.SiteMatrix)) =
      ((∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix) : ℝ) : ℂ) := by
  calc
    _ = ∫ H, ((‖physicalMode p α m H‖ ^ 2 : ℝ) : ℂ)
        ∂(model.law : Measure p.SiteMatrix) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun H => by
        simp only [Complex.mul_conj', Complex.ofReal_pow])
    _ = _ := integral_ofReal
end BlockBand.QUE.Fourier
