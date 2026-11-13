module
public import BlockBand.QUE.Fourier.FiniteAlgebra
public import BlockBand.Model.Construction.SpectralProfiles
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-!
# Integrability of the physical block masses and Fourier modes

The block masses of the selected eigenvector are almost surely in `[0, 1]` and its Fourier modes
have norm at most one, so all their products are integrable under the physical law.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Fourier
open MeasureTheory BlockBand.Model.Construction

/-- Negative-sign Fourier mode of the physical block masses at a fixed rank. -/
def physicalMode (p : Parameters) (α : Fin p.N) (m : ZMod p.n) (H : p.SiteMatrix) : ℂ :=
  mode (fun k => (physicalOrderedBlockMass p H α k : ℂ)) m

theorem measurable_physicalMode (p : Parameters) (α : Fin p.N) (m : ZMod p.n) :
    Measurable (physicalMode p α m) := by
  unfold physicalMode mode
  simp only [ZMod.dft_apply, smul_eq_mul]
  exact Finset.measurable_sum _ (fun k _ => measurable_const.mul
    ((measurable_physicalOrderedBlockMass p α k).complex_ofReal))

/-- Physical simplex normalization bounds each block mass by one almost surely. -/
theorem physical_mass_le_one_ae (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ k,
      physicalOrderedBlockMass p H α k ≤ 1 := by
  filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
  intro k
  rw [← hH α]
  exact Finset.single_le_sum (fun j _ => physicalOrderedBlockMass_nonneg p H α j)
    (Finset.mem_univ k)

/-- Integrability of the physical mass coordinates. -/
theorem integrable_physicalMass (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (k : ZMod p.n) :
    Integrable (fun H => physicalOrderedBlockMass p H α k) (model.law : Measure p.SiteMatrix) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_physicalOrderedBlockMass p α k).aestronglyMeasurable
  filter_upwards [physical_mass_le_one_ae p model α] with H hH
  simpa only [Real.norm_eq_abs, abs_of_nonneg (physicalOrderedBlockMass_nonneg p H α k)] using hH k

/-- The physical Fourier mode has complex norm at most one, almost surely. -/
theorem physicalMode_norm_le_one_ae (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (m : ZMod p.n) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ‖physicalMode p α m H‖ ≤ 1 := by
  filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
  unfold physicalMode mode
  simp only [ZMod.dft_apply, smul_eq_mul]
  calc
    ‖∑ k, ZMod.stdAddChar (-(k * m)) * (physicalOrderedBlockMass p H α k : ℂ)‖ ≤
        ∑ k, ‖ZMod.stdAddChar (-(k * m)) * (physicalOrderedBlockMass p H α k : ℂ)‖ := norm_sum_le _ _
    _ = ∑ k, physicalOrderedBlockMass p H α k := by
      apply Finset.sum_congr rfl
      intro k _
      simp [ZMod.stdAddChar_apply, Complex.norm_real,
        abs_of_nonneg (physicalOrderedBlockMass_nonneg p H α k)]
    _ = 1 := hH α

theorem integrable_physicalMode (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (m : ZMod p.n) :
    Integrable (physicalMode p α m) (model.law : Measure p.SiteMatrix) := by
  exact (integrable_const (1 : ℝ)).mono'
    (measurable_physicalMode p α m).aestronglyMeasurable
    (physicalMode_norm_le_one_ae p model α m)

/-- All physical mass-mode mixed coordinates are integrable under the physical law. -/
theorem integrable_physicalMass_mode (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (k m : ZMod p.n) :
    Integrable (fun H => (physicalOrderedBlockMass p H α k : ℂ) *
      starRingEnd ℂ (physicalMode p α m H)) (model.law : Measure p.SiteMatrix) := by
  have hm : Measurable (fun H => (physicalOrderedBlockMass p H α k : ℂ) *
      starRingEnd ℂ (physicalMode p α m H)) := by
    exact (measurable_physicalOrderedBlockMass p α k).complex_ofReal.mul
      (Complex.continuous_conj.measurable.comp (measurable_physicalMode p α m))
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [physical_mass_le_one_ae p model α, physicalMode_norm_le_one_ae p model α m] with H hH hM
  rw [norm_mul, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (physicalOrderedBlockMass_nonneg p H α k)]
  nlinarith [physicalOrderedBlockMass_nonneg p H α k, norm_nonneg (physicalMode p α m H), hH k]
/-- The physical second Fourier moments are integrable. -/
theorem integrable_physicalMode_sq (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (m : ZMod p.n) :
    Integrable (fun H => ‖physicalMode p α m H‖ ^ 2) (model.law : Measure p.SiteMatrix) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_physicalMode p α m).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [physicalMode_norm_le_one_ae p model α m] with H hH
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (physicalMode p α m H)]

/-- The mass-weighted Fourier variances are integrable. -/
theorem integrable_physicalMass_mode_sq (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (k m : ZMod p.n) :
    Integrable (fun H => physicalOrderedBlockMass p H α k * ‖physicalMode p α m H‖ ^ 2)
      (model.law : Measure p.SiteMatrix) := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_physicalOrderedBlockMass p α k).mul
      ((measurable_physicalMode p α m).norm.pow_const 2)).aestronglyMeasurable)
  filter_upwards [physical_mass_le_one_ae p model α, physicalMode_norm_le_one_ae p model α m] with H hH hM
  change ‖physicalOrderedBlockMass p H α k * ‖physicalMode p α m H‖ ^ 2‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (physicalOrderedBlockMass_nonneg p H α k) (sq_nonneg _))]
  have hs : ‖physicalMode p α m H‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (physicalMode p α m H)]
  exact (mul_le_mul_of_nonneg_left hs (physicalOrderedBlockMass_nonneg p H α k)).trans (by simpa using hH k)
/-- All physical mode products are integrable, including distinct frequencies. -/
theorem integrable_physicalMode_product (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (r s : ZMod p.n) :
    Integrable (fun H => physicalMode p α r H * starRingEnd ℂ (physicalMode p α s H))
      (model.law : Measure p.SiteMatrix) := by
  have hm := (measurable_physicalMode p α r).mul
    (Complex.continuous_conj.measurable.comp (measurable_physicalMode p α s))
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [physicalMode_norm_le_one_ae p model α r,
    physicalMode_norm_le_one_ae p model α s] with H hr hs
  change ‖physicalMode p α r H * starRingEnd ℂ (physicalMode p α s H)‖ ≤ 1
  rw [norm_mul, RCLike.norm_conj]
  exact (mul_le_mul hr hs (norm_nonneg _) (by norm_num)).trans (by norm_num)
end BlockBand.QUE.Fourier
