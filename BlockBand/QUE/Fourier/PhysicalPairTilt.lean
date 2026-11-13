module
public import BlockBand.QUE.Fourier.PhysicalMoments
/-!
# The normalized physical neighbouring-pair law

The neighbouring-pair measure tilts the physical law by `(n/2)(p_i + p_{i+1})`; it is a probability
measure, and under it the signed contrast `(p_i - p_{i+1})/(p_i + p_{i+1})` gives the signed-pair
identity for the Fourier variance `E|A_m|²` (`physical_signed_pair_identity_variance`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Fourier
open MeasureTheory BlockBand.Model.Construction
open scoped NNReal ENNReal

/-- Every physical block mass has mean `1/n`. -/
theorem physical_mass_expectation (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n) :
    (∫ H, physicalOrderedBlockMass p H α i ∂(model.law : Measure p.SiteMatrix)) =
      (p.n : ℝ)⁻¹ := by
  have hmean (k : ZMod p.n) :
      (∫ H, physicalOrderedBlockMass p H α k ∂(model.law : Measure p.SiteMatrix)) =
      ∫ H, physicalOrderedBlockMass p H α 0 ∂(model.law : Measure p.SiteMatrix) := by
    have h := integral_map (p.measurable_siteReindexMatrix (p.cyclicSiteEquiv k)).aemeasurable
      ((measurable_physicalOrderedBlockMass p α 0).aestronglyMeasurable :
        AEStronglyMeasurable (fun H => physicalOrderedBlockMass p H α 0)
          (Measure.map (p.siteReindexMatrix (p.cyclicSiteEquiv k)) (model.law : Measure p.SiteMatrix)))
    rw [model.map_cyclicMatrix k] at h
    rw [h]
    apply integral_congr_ae
    filter_upwards [physical_blockMass_cyclic_ae p model α k] with H hH
    simpa using (hH 0).symm
  have hsum : (p.n : ℝ) *
      (∫ H, physicalOrderedBlockMass p H α 0 ∂(model.law : Measure p.SiteMatrix)) = 1 := by
    have h := integral_finsetSum Finset.univ (fun k _ => integrable_physicalMass p model α k)
    have he : (∫ H, ∑ k, physicalOrderedBlockMass p H α k ∂(model.law : Measure p.SiteMatrix)) = 1 := by
      apply integral_eq_const
      filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
      exact hH α
    rw [he] at h
    simp_rw [hmean] at h
    simpa using h.symm
  rw [hmean i]
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n_pos.ne'
  rw [← one_div]
  apply (eq_div_iff hn).2
  simpa only [mul_comm] using hsum

/-- The weight `(n/2)(p_i + p_{i+1})` of neighbouring block masses, everywhere nonnegative. -/
def physicalPairWeight (p : Parameters) (α : Fin p.N) (i : ZMod p.n)
    (H : p.SiteMatrix) : ℝ≥0 :=
  ⟨(p.n : ℝ) / 2 * (physicalOrderedBlockMass p H α i + physicalOrderedBlockMass p H α (i + 1)),
    mul_nonneg (by positivity) (add_nonneg (physicalOrderedBlockMass_nonneg p H α i)
      (physicalOrderedBlockMass_nonneg p H α (i + 1)))⟩

theorem measurable_physicalPairWeight (p : Parameters) (α : Fin p.N) (i : ZMod p.n) :
    Measurable (physicalPairWeight p α i) := by
  apply Measurable.subtype_mk
  exact measurable_const.mul ((measurable_physicalOrderedBlockMass p α i).add
    (measurable_physicalOrderedBlockMass p α (i + 1)))

theorem integrable_physicalPairWeight (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n) :
    Integrable (fun H => (physicalPairWeight p α i H : ℝ)) (model.law : Measure p.SiteMatrix) :=
  ((integrable_physicalMass p model α i).add
    (integrable_physicalMass p model α (i + 1))).const_mul _

theorem physicalPairWeight_integral (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n) :
    (∫ H, (physicalPairWeight p α i H : ℝ) ∂(model.law : Measure p.SiteMatrix)) = 1 := by
  change (∫ H, (p.n : ℝ) / 2 * (_ + _) ∂(model.law : Measure p.SiteMatrix)) = _
  rw [integral_const_mul, integral_add (integrable_physicalMass p model α i)
    (integrable_physicalMass p model α (i + 1)), physical_mass_expectation,
    physical_mass_expectation]
  field_simp [NeZero.ne (p.n : ℝ)]
  norm_num

/-- The physical neighbouring-pair measure. -/
def physicalPairMeasure (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n) : Measure p.SiteMatrix :=
  (model.law : Measure p.SiteMatrix).withDensity (fun H => physicalPairWeight p α i H)

/-- The physical pair tilt is a probability measure. -/
theorem physicalPairMeasure_isProbability (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n) : IsProbabilityMeasure (physicalPairMeasure p model α i) := by
  apply (isProbabilityMeasure_iff).2
  rw [physicalPairMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := ofReal_integral_eq_lintegral_ofReal (integrable_physicalPairWeight p model α i)
    (Filter.Eventually.of_forall (fun H => (physicalPairWeight p α i H).coe_nonneg))
  rw [physicalPairWeight_integral] at h
  simpa only [ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal] using h.symm

/-- Integral transport through the pair density, for any complex observable. -/
theorem integral_physicalPairMeasure (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n) (F : p.SiteMatrix → ℂ) :
    (∫ H, F H ∂physicalPairMeasure p model α i) =
      ∫ H, (physicalPairWeight p α i H : ℝ) • F H ∂(model.law : Measure p.SiteMatrix) := by
  exact integral_withDensity_eq_integral_smul (measurable_physicalPairWeight p α i) F
/-- Neighboring contrast, with the ordinary real zero-denominator default. -/
def physicalPairContrast (p : Parameters) (α : Fin p.N) (i : ZMod p.n)
    (H : p.SiteMatrix) : ℝ :=
  (physicalOrderedBlockMass p H α i - physicalOrderedBlockMass p H α (i + 1)) /
    (physicalOrderedBlockMass p H α i + physicalOrderedBlockMass p H α (i + 1))

/-- Pair density cancels the contrast denominator even when both masses vanish.
Nonnegativity forces the numerator to vanish on that zero-density locus. -/
theorem physicalPairWeight_contrast (p : Parameters) (α : Fin p.N) (i : ZMod p.n)
    (H : p.SiteMatrix) :
    (physicalPairWeight p α i H : ℝ) * physicalPairContrast p α i H =
      (p.n : ℝ) / 2 * (physicalOrderedBlockMass p H α i - physicalOrderedBlockMass p H α (i + 1)) := by
  change ((p.n : ℝ) / 2 * (physicalOrderedBlockMass p H α i + physicalOrderedBlockMass p H α (i + 1))) *
    ((physicalOrderedBlockMass p H α i - physicalOrderedBlockMass p H α (i + 1)) /
      (physicalOrderedBlockMass p H α i + physicalOrderedBlockMass p H α (i + 1))) = _
  by_cases hz : physicalOrderedBlockMass p H α i + physicalOrderedBlockMass p H α (i + 1) = 0
  · have hi := physicalOrderedBlockMass_nonneg p H α i
    have hj := physicalOrderedBlockMass_nonneg p H α (i + 1)
    have ha : physicalOrderedBlockMass p H α i = 0 := by linarith
    have hb : physicalOrderedBlockMass p H α (i + 1) = 0 := by linarith
    simp [ha, hb]
  · field_simp

/-- The full physical signed-pair contrast identity under its normalized tilt. -/
theorem physical_signed_pair_identity (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (m i : ZMod p.n) :
    (∫ H, (physicalPairContrast p α i H : ℂ) * starRingEnd ℂ (physicalMode p α m H)
      ∂physicalPairMeasure p model α i) =
      (1 - ZMod.stdAddChar m) / 2 * ZMod.stdAddChar (i * m) *
        (∫ H, physicalMode p α m H * starRingEnd ℂ (physicalMode p α m H)
          ∂(model.law : Measure p.SiteMatrix)) := by
  rw [integral_physicalPairMeasure]
  have he (H : p.SiteMatrix) : (physicalPairWeight p α i H : ℝ) •
      ((physicalPairContrast p α i H : ℂ) * starRingEnd ℂ (physicalMode p α m H)) =
      (p.n : ℂ) / 2 *
        (((physicalOrderedBlockMass p H α i : ℂ) - physicalOrderedBlockMass p H α (i + 1)) *
          starRingEnd ℂ (physicalMode p α m H)) := by
    change ((physicalPairWeight p α i H : ℝ) : ℂ) * _ = _
    rw [← mul_assoc, ← Complex.ofReal_mul, physicalPairWeight_contrast]
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul]
  exact physical_signed_pair_numerator p model α m i
/-- The normalized physical pair tilt preserves the Fourier variance: the first signed-pair
identity, with its `n/2` normalization. -/
theorem physical_pair_variance_identity (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (m i : ZMod p.n) :
    (∫ H, ‖physicalMode p α m H‖ ^ 2 ∂physicalPairMeasure p model α i) =
      ∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix) := by
  let M (k : ZMod p.n) := ∫ H,
    physicalOrderedBlockMass p H α k * ‖physicalMode p α m H‖ ^ 2
      ∂(model.law : Measure p.SiteMatrix)
  have hmean (k : ZMod p.n) : M k = M 0 := by
    have hf : Measurable (fun H => physicalOrderedBlockMass p H α 0 *
        ‖physicalMode p α m H‖ ^ 2) :=
      (measurable_physicalOrderedBlockMass p α 0).mul
        ((measurable_physicalMode p α m).norm.pow_const 2)
    have h := integral_map (p.measurable_siteReindexMatrix (p.cyclicSiteEquiv k)).aemeasurable
      (hf.aestronglyMeasurable : AEStronglyMeasurable _
        (Measure.map (p.siteReindexMatrix (p.cyclicSiteEquiv k)) (model.law : Measure p.SiteMatrix)))
    rw [model.map_cyclicMatrix k] at h
    change M 0 = _ at h
    rw [h]
    apply integral_congr_ae
    filter_upwards [physical_blockMass_cyclic_ae p model α k,
      physicalMode_cyclic_ae p model α k m] with H hmass hmode
    rw [hmass 0, zero_add, hmode]
    rw [mode_translate (fun j => (physicalOrderedBlockMass p H α j : ℂ)) k m, norm_mul]
    simp only [ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
    rfl
  have hsum : (p.n : ℝ) * M 0 =
      ∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix) := by
    calc
      (p.n : ℝ) * M 0 = ∑ k : ZMod p.n, M k := by
        simp_rw [hmean]
        simp
      _ = ∫ H, ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k *
          ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix) :=
        (integral_finsetSum _ (fun k _ => integrable_physicalMass_mode_sq p model α k m)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
        rw [← Finset.sum_mul, hH α, one_mul]
  unfold physicalPairMeasure
  rw [integral_withDensity_eq_integral_smul (measurable_physicalPairWeight p α i)]
  change (∫ H, ((p.n : ℝ) / 2 * (_ + _)) * ‖physicalMode p α m H‖ ^ 2
    ∂(model.law : Measure p.SiteMatrix)) = _
  simp_rw [mul_assoc, add_mul]
  rw [integral_const_mul, integral_add (integrable_physicalMass_mode_sq p model α i m)
    (integrable_physicalMass_mode_sq p model α (i + 1) m)]
  change (p.n : ℝ) / 2 * (M i + M (i + 1)) = _
  rw [hmean i, hmean (i + 1), ← hsum]
  ring
/-- The signed-pair equation with `γ = E|A_m|²` under the physical law. -/
theorem physical_signed_pair_identity_variance (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (m i : ZMod p.n) :
    (∫ H, (physicalPairContrast p α i H : ℂ) * starRingEnd ℂ (physicalMode p α m H)
      ∂physicalPairMeasure p model α i) =
      (1 - ZMod.stdAddChar m) / 2 * ZMod.stdAddChar (i * m) *
        ((∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix) : ℝ) : ℂ) := by
  rw [physical_signed_pair_identity, physical_diagonal_covariance_eq_variance]
end BlockBand.QUE.Fourier
