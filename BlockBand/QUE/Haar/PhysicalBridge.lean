module

public import BlockBand.QUE.Haar.ProjectorTransport
public import BlockBand.QUE.Haar.FixedBridge
public import BlockBand.QUE.PhysicalAdapter
public import BlockBand.Model.Construction.SpectralPhysicalAE
public import BlockBand.QUE.Invariance.BlockGaussianLaw
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The physical Haar bridge at a fixed rank

Under the physical Gaussian law, independent Haar rotations of the blocks preserve the law of the
selected eigenvector at each increasing rank, so the physical site fluctuation equals its Haar
average; with the fixed-vector Haar bridge this bounds the physical site fluctuation by the block
statistic plus `1/(W+1)` (`physical_haar_bridge`, `physical_haar_bound`).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.QUE.Haar

open Matrix MeasureTheory
open scoped BigOperators Classical
open BlockBand.Model.Construction BlockBand.Foundations.Spectral
open BlockBand.Foundations.FiniteBlock

/-- Every spectral realization has, almost surely under the physical law, the canonical site masses
at each increasing rank. -/
theorem spectral_mass_eq_canonical_ae {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ α : Fin p.N, ∀ x : p.Site,
      physicalSiteMass spectral α H x = ‖physicalOrderedEigenvector p H α x‖ ^ 2 := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable,
    spectral.orthonormal_ae, spectral.eigenvector_ae, spectral.ordered_ae]
    with H hH hsep hon heig hord
  intro α x
  apply physical_rank_mass_eq_canonical p H hH hsep (spectral.eigenvalue H)
    (spectral.eigenvector H) hon
    (fun β => funext (heig β))
    (fun β γ hβγ => hord β γ hβγ)

/-- The canonical physical block vectors. -/
def canonicalBlockVector (p : Parameters) (α : Fin p.N) (H : p.SiteMatrix)
    (b : ZMod p.n) (a : Fin p.W) : ℂ := physicalOrderedEigenvector p H α (b, a)

/-- The canonical site masses. -/
def canonicalSiteMass (p : Parameters) (α : Fin p.N) (H : p.SiteMatrix) (x : p.Site) : ℝ :=
  ‖physicalOrderedEigenvector p H α x‖ ^ 2

/-- The complete canonical selected vector is measurable, coordinatewise. -/
theorem measurable_canonicalBlockVector (p : Parameters) (α : Fin p.N) :
    Measurable (canonicalBlockVector p α) := by
  apply measurable_pi_iff.mpr
  intro b
  apply measurable_pi_iff.mpr
  intro a
  exact measurable_physicalOrderedEigenvector p α (b, a)

/-- Canonical block masses have the unit total mass almost surely. -/
theorem sum_canonicalBlockMass_ae (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      (∑ b : ZMod p.n, blockMass (canonicalBlockVector p α H) b) = 1 := by
  filter_upwards [physicalOrderedEigenvector_totalMass_ae p model] with H hH
  have h := hH α
  change (∑ x : ZMod p.n × Fin p.W, ‖physicalOrderedEigenvector p H α x‖ ^ 2) = 1 at h
  rw [Fintype.sum_prod_type] at h
  exact h

/-- The block embedding acts on each block by its own unitary. -/
theorem blockUnitary_mulVec (p : Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) (v : p.Site → ℂ) (x : p.Site) :
    ((p.blockUnitary U : p.SiteMatrix) *ᵥ v) x =
      ((U x.1 : Matrix (Fin p.W) (Fin p.W) ℂ) *ᵥ fun a => v (x.1, a)) x.2 := by
  simp [Matrix.mulVec, dotProduct, Parameters.blockUnitary_coe,
    Parameters.blockUnitaryMatrix_apply, Fintype.sum_prod_type, ite_mul, Finset.sum_ite_irrel]

/-- On simple spectrum, the canonical selected masses after block conjugation are the Haar-rotated
masses at the same increasing rank. -/
theorem canonical_mass_blockConjugation (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) (α : Fin p.N) (x : p.Site) :
    canonicalSiteMass p α (p.blockUnitaryConjugation U H) x =
      rotatedMass (canonicalBlockVector p α H) U x := by
  rw [canonicalSiteMass]
  have h := physicalOrderedEigenvector_unitary_mass p H hH hsep (p.blockUnitary U) α x
  rw [blockUnitary_mulVec] at h
  exact h

/-- The canonical QUE statistic at a fixed rank, with the physical law and site normalization. -/
def canonicalQueStatistic (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (w : p.Site → ℝ) : ℝ :=
  quadraticStatistic (model.law : Measure p.SiteMatrix) (canonicalSiteMass p α) (p.N : ℝ)⁻¹ w

/-- The QUE statistic of every realization equals the canonical one (no measurability of the
eigenvector phases is needed). -/
theorem queStatistic_eq_canonical {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (α : Fin p.N) (w : p.Site → ℝ) :
    spectral.queStatistic α w = canonicalQueStatistic p model α w := by
  rw [queStatistic_eq_quadraticStatistic]
  unfold canonicalQueStatistic quadraticStatistic
  apply integral_congr_ae
  filter_upwards [spectral_mass_eq_canonical_ae spectral] with H hH
  unfold fluctuation canonicalSiteMass
  simp_rw [hH α]

/-- A deterministic test bounded by one has normalized mass fluctuation at
most two on every nonnegative finite unit-mass vector. -/
theorem normalized_test_abs_le_two {I : Type*} [Fintype I] [Nonempty I]
    (mass : I → ℝ) (hmass : ∀ x, 0 ≤ mass x) (hsum : ∑ x, mass x = 1)
    (w : I → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    |(∑ x, w x * mass x) - (Fintype.card I : ℝ)⁻¹ * ∑ x, w x| ≤ 2 := by
  have hcard : 0 < (Fintype.card I : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  have hweighted : |∑ x, w x * mass x| ≤ 1 := by
    calc
      _ ≤ ∑ x, |w x * mass x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, |w x| * mass x := by simp only [abs_mul, abs_of_nonneg (hmass _)]
      _ ≤ ∑ x, mass x := Finset.sum_le_sum (fun x _ => by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw x) (hmass x))
      _ = 1 := hsum
  have htest : |∑ x, w x| ≤ (Fintype.card I : ℝ) := by
    calc
      _ ≤ ∑ x, |w x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : I, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hw x)
      _ = _ := by simp
  have huniform : |(Fintype.card I : ℝ)⁻¹ * ∑ x, w x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hcard.le)]
    calc
      _ ≤ (Fintype.card I : ℝ)⁻¹ * (Fintype.card I : ℝ) :=
        mul_le_mul_of_nonneg_left htest (inv_nonneg.mpr hcard.le)
      _ = 1 := inv_mul_cancel₀ hcard.ne'
  exact (abs_sub _ _).trans (by linarith)

/-- Bounded finite mass statistics are integrable, by measurability and almost-sure
normalization. -/
theorem integrable_normalized_test_sq {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [Nonempty I] (μ : Measure Ω) [IsFiniteMeasure μ]
    (mass : Ω → I → ℝ) (hm : ∀ x, Measurable (fun ω => mass ω x))
    (hnonneg : ∀ ω x, 0 ≤ mass ω x) (hsum : ∀ᵐ ω ∂μ, ∑ x, mass ω x = 1)
    (w : I → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    Integrable (fun ω => |(∑ x, w x * mass ω x) -
      (Fintype.card I : ℝ)⁻¹ * ∑ x, w x| ^ 2) μ := by
  have hf : Measurable (fun ω => |(∑ x, w x * mass ω x) -
      (Fintype.card I : ℝ)⁻¹ * ∑ x, w x| ^ 2) := by
    apply Measurable.pow_const
    apply Measurable.abs
    apply Measurable.sub _ measurable_const
    exact Finset.measurable_sum _ (fun x _ => measurable_const.mul (hm x))
  apply (integrable_const (4 : ℝ)).mono' hf.aestronglyMeasurable
  filter_upwards [hsum] with ω hω
  have hb := normalized_test_abs_le_two (mass ω) (hnonneg ω) hω w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [abs_nonneg ((∑ x, w x * mass ω x) -
    (Fintype.card I : ℝ)⁻¹ * ∑ x, w x)]

/-- Joint canonical physical/Haar rotated site mass on the product law. -/
def physicalRotatedMass (p : Parameters) (α : Fin p.N)
    (z : p.SiteMatrix × (ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ)) (x : p.Site) : ℝ :=
  rotatedMass (canonicalBlockVector p α z.1) z.2 x

/-- Joint measurability of the coordinate masses. -/
theorem measurable_physicalRotatedMass (p : Parameters) (α : Fin p.N) (x : p.Site) :
    Measurable (fun z => physicalRotatedMass p α z x) := by
  change Measurable (fun z : p.SiteMatrix × (ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) =>
    ‖∑ a : Fin p.W, (z.2 x.1 : Matrix (Fin p.W) (Fin p.W) ℂ) x.2 a *
      physicalOrderedEigenvector p z.1 α (x.1, a)‖ ^ 2)
  apply Measurable.pow_const
  apply Measurable.norm
  apply Finset.measurable_sum
  intro a _
  have hU : Measurable (fun z : p.SiteMatrix × (ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) =>
      (z.2 x.1 : Matrix (Fin p.W) (Fin p.W) ℂ) x.2 a) :=
    (measurable_pi_apply a).comp ((measurable_pi_apply x.2).comp
      (measurable_subtype_coe.comp ((measurable_pi_apply x.1).comp measurable_snd)))
  exact hU.mul ((measurable_physicalOrderedEigenvector p α (x.1, a)).comp measurable_fst)

/-- The Gaussian/Haar product has unit total site mass almost surely. -/
theorem sum_physicalRotatedMass_ae (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) :
    ∀ᵐ z ∂((model.law : Measure p.SiteMatrix).prod
      (blockProbability : Measure (ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ))),
      (∑ x : p.Site, physicalRotatedMass p α z x) = 1 := by
  have h := (measurePreserving_fst (μ := (model.law : Measure p.SiteMatrix))
    (ν := (blockProbability : Measure (ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ)))).quasiMeasurePreserving.ae (sum_canonicalBlockMass_ae p model α)
  filter_upwards [h] with z hz
  change (∑ x : p.Site, rotatedMass (canonicalBlockVector p α z.1) z.2 x) = 1
  rw [Fintype.sum_prod_type]
  simp_rw [sum_rotatedMass]
  exact hz

/-- The joint squared fluctuation in the physical site normalization. -/
def physicalRotatedStatistic (p : Parameters) (α : Fin p.N) (w : p.Site → ℝ)
    (z : p.SiteMatrix × (ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ)) : ℝ :=
  |fluctuation (physicalRotatedMass p α) (p.N : ℝ)⁻¹ w z| ^ 2

/-- Integrability of the joint statistic on the Gaussian/Haar product law (the hypothesis of
Fubini's theorem). -/
theorem integrable_physicalRotatedStatistic (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (w : p.Site → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    Integrable (physicalRotatedStatistic p α w)
      ((model.law : Measure p.SiteMatrix).prod
        (blockProbability : Measure (ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ))) := by
  have h := integrable_normalized_test_sq
    ((model.law : Measure p.SiteMatrix).prod
      (blockProbability : Measure (ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ)))
    (physicalRotatedMass p α) (measurable_physicalRotatedMass p α)
    (fun z x => sq_nonneg _) (sum_physicalRotatedMass_ae p model α) w hw
  unfold physicalRotatedStatistic
  simpa only [fluctuation, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, physicalSite_card, mul_comm] using h

/-- Joint block conjugation is measurable on the raw physical/Haar product. -/
theorem measurable_joint_blockConjugation (p : Parameters) :
    Measurable (fun z : p.SiteMatrix × (ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) =>
      p.blockUnitaryConjugation z.2 z.1) := by
  have hB : Continuous (fun z : p.SiteMatrix ×
      (ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) => p.blockUnitaryMatrix z.2) :=
    (Parameters.continuous_blockUnitaryMatrix p).comp continuous_snd
  exact ((hB.matrix_mul continuous_fst).matrix_mul hB.matrix_conjTranspose).measurable

/-- Canonical squared site fluctuations are measurable under the raw law. -/
theorem measurable_canonicalStatistic (p : Parameters) (α : Fin p.N) (w : p.Site → ℝ) :
    Measurable (fun H => |fluctuation (canonicalSiteMass p α) (p.N : ℝ)⁻¹ w H| ^ 2) := by
  unfold fluctuation
  exact (Finset.measurable_sum _ (fun x _ => measurable_const.mul
    (((measurable_physicalOrderedEigenvector p α x).norm.pow_const 2).sub
      measurable_const))).abs.pow_const 2

/-- The canonical squared site fluctuation is integrable, by its unit mass. -/
theorem integrable_canonicalStatistic (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (w : p.Site → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    Integrable (fun H => |fluctuation (canonicalSiteMass p α) (p.N : ℝ)⁻¹ w H| ^ 2)
      (model.law : Measure p.SiteMatrix) := by
  have hs : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∑ x, canonicalSiteMass p α H x = 1 := by
    filter_upwards [physicalOrderedEigenvector_totalMass_ae p model] with H hH
    exact hH α
  have h := integrable_normalized_test_sq (model.law : Measure p.SiteMatrix)
    (canonicalSiteMass p α)
    (fun x => (measurable_physicalOrderedEigenvector p α x).norm.pow_const 2)
    (fun H x => sq_nonneg _) hs w hw
  simpa only [fluctuation, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, physicalSite_card, mul_comm] using h

/-- A fixed block conjugation preserves the canonical physical statistic, by invariance of the
Gaussian law. -/
theorem integral_physicalRotatedStatistic (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (w : p.Site → ℝ)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) :
    (∫ H, physicalRotatedStatistic p α w (H, U) ∂(model.law : Measure p.SiteMatrix)) =
      canonicalQueStatistic p model α w := by
  have hm := integral_map (μ := (model.law : Measure p.SiteMatrix))
    (p.measurable_blockUnitaryConjugation U).aemeasurable
    (measurable_canonicalStatistic p α w).aestronglyMeasurable
  rw [model.map_blockUnitaryConjugation U] at hm
  unfold canonicalQueStatistic quadraticStatistic
  rw [hm]
  apply integral_congr_ae
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  unfold physicalRotatedStatistic fluctuation physicalRotatedMass
  simp_rw [canonical_mass_blockConjugation p H hH hsep U α]

/-- The canonical QUE statistic equals its Haar average at the same increasing rank. -/
theorem canonicalQueStatistic_eq_haar_average (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (w : p.Site → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    canonicalQueStatistic p model α w =
      ∫ H, quadraticStatistic blockProbability (rotatedMass (canonicalBlockVector p α H))
        (p.N : ℝ)⁻¹ w ∂(model.law : Measure p.SiteMatrix) := by
  have hf := integrable_physicalRotatedStatistic p model α w hw
  have hs := integral_integral_swap
    (f := fun H U => physicalRotatedStatistic p α w (H, U)) hf
  change (∫ H, ∫ U, physicalRotatedStatistic p α w (H, U) ∂blockProbability
    ∂(model.law : Measure p.SiteMatrix)) = _ at hs
  simp_rw [integral_physicalRotatedStatistic p model α w] at hs
  change (∫ H, quadraticStatistic blockProbability
    (rotatedMass (canonicalBlockVector p α H)) (p.N : ℝ)⁻¹ w
    ∂(model.law : Measure p.SiteMatrix)) = _ at hs
  simpa only [integral_const, probReal_univ, one_smul] using hs.symm

/-- The block statistic is integrable under the original Gaussian law. -/
theorem integrable_canonicalBlockStatistic (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (w : p.Site → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    Integrable (fun H => |blockFluctuation (canonicalBlockVector p α H) (p.N : ℝ)⁻¹ w| ^ 2)
      (model.law : Measure p.SiteMatrix) := by
  have hc : ∀ x : p.Site, |constantPart w x| ≤ 1 :=
    fun x => average_abs_le_one w hw x.1
  have h := (integrable_physicalRotatedStatistic p model α (constantPart w) hc).integral_prod_left
  change Integrable (fun H => ∫ U,
    |fluctuation (rotatedMass (canonicalBlockVector p α H)) (p.N : ℝ)⁻¹
      (constantPart w) U| ^ 2 ∂blockProbability) _ at h
  simp_rw [fluctuation_constant_rotated] at h
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- The physical Haar bridge at a fixed rank, with the outer expectation split. -/
theorem canonical_physical_haar_bridge (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (w : p.Site → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    canonicalQueStatistic p model α w =
      (∫ H, |blockFluctuation (canonicalBlockVector p α H) (p.N : ℝ)⁻¹ w| ^ 2
        ∂(model.law : Measure p.SiteMatrix)) +
      (1 / ((p.W : ℝ) + 1)) *
        (∫ H, ∑ b : ZMod p.n, blockMass (canonicalBlockVector p α H) b ^ 2 *
          ((∑ a : Fin p.W, w (b, a) ^ 2) / (p.W : ℝ) - average w b ^ 2)
          ∂(model.law : Measure p.SiteMatrix)) := by
  have hi := (integrable_physicalRotatedStatistic p model α w hw).integral_prod_left
  change Integrable (fun H => quadraticStatistic blockProbability
    (rotatedMass (canonicalBlockVector p α H)) (p.N : ℝ)⁻¹ w) _ at hi
  have hb := integrable_canonicalBlockStatistic p model α w hw
  have hr := hi.sub hb
  change Integrable (fun H => quadraticStatistic blockProbability
    (rotatedMass (canonicalBlockVector p α H)) (p.N : ℝ)⁻¹ w -
    |blockFluctuation (canonicalBlockVector p α H) (p.N : ℝ)⁻¹ w| ^ 2) _ at hr
  simp_rw [rotated_site_bridge_average, Fintype.card_fin, add_sub_cancel_left] at hr
  rw [canonicalQueStatistic_eq_haar_average p model α w hw]
  simp_rw [rotated_site_bridge_average, Fintype.card_fin]
  rw [integral_add hb hr, integral_const_mul]

/-- Physical site fluctuation is bounded by the block statistic plus
`1/(W+1)` uniformly over all ranks and deterministic tests bounded by one. -/
theorem canonical_physical_haar_bound (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (w : p.Site → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    canonicalQueStatistic p model α w ≤
      (∫ H, |blockFluctuation (canonicalBlockVector p α H) (p.N : ℝ)⁻¹ w| ^ 2
        ∂(model.law : Measure p.SiteMatrix)) + 1 / ((p.W : ℝ) + 1) := by
  rw [canonicalQueStatistic_eq_haar_average p model α w hw]
  have hi := (integrable_physicalRotatedStatistic p model α w hw).integral_prod_left
  change Integrable (fun H => quadraticStatistic blockProbability
    (rotatedMass (canonicalBlockVector p α H)) (p.N : ℝ)⁻¹ w) _ at hi
  have hb := (integrable_canonicalBlockStatistic p model α w hw).add (integrable_const (1 / ((p.W : ℝ) + 1)))
  have hh : (∫ H, quadraticStatistic blockProbability
      (rotatedMass (canonicalBlockVector p α H)) (p.N : ℝ)⁻¹ w
      ∂(model.law : Measure p.SiteMatrix)) ≤
      ∫ H, |blockFluctuation (canonicalBlockVector p α H) (p.N : ℝ)⁻¹ w| ^ 2 +
        1 / ((p.W : ℝ) + 1) ∂(model.law : Measure p.SiteMatrix) := by
    apply integral_mono_ae hi hb
    filter_upwards [sum_canonicalBlockMass_ae p model α] with H hH
    change quadraticStatistic blockProbability (rotatedMass (canonicalBlockVector p α H))
      (p.N : ℝ)⁻¹ w ≤
      |blockFluctuation (canonicalBlockVector p α H) (p.N : ℝ)⁻¹ w| ^ 2 +
        1 / ((p.W : ℝ) + 1)
    simpa only [Fintype.card_fin] using
      rotated_site_le_block_add_width (canonicalBlockVector p α H) (p.N : ℝ)⁻¹ hH w hw
  simpa only [integral_add (integrable_canonicalBlockStatistic p model α w hw)
    (integrable_const _), integral_const, probReal_univ, one_smul] using hh

/-- The physical block mass of a realization at an increasing rank. -/
def physicalBlockMass {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (α : Fin p.N)
    (H : p.SiteMatrix) (b : ZMod p.n) : ℝ :=
  ∑ a : Fin p.W, physicalSiteMass spectral α H (b, a)

/-- Block masses agree with the canonical same-rank masses under the law. -/
theorem spectral_blockMass_eq_canonical_ae {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ α : Fin p.N, ∀ b : ZMod p.n,
      physicalBlockMass spectral α H b = blockMass (canonicalBlockVector p α H) b := by
  filter_upwards [spectral_mass_eq_canonical_ae spectral] with H hH
  intro α b
  unfold physicalBlockMass blockMass canonicalBlockVector
  simp_rw [hH α]

/-- The site baseline induces the block baseline `1/n`. -/
theorem width_mul_inv_site_count (p : Parameters) :
    (p.W : ℝ) * (p.N : ℝ)⁻¹ = (p.n : ℝ)⁻¹ := by
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n_pos.ne'
  have hW : (p.W : ℝ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  simp only [Parameters.N, Nat.cast_mul]
  field_simp

/-- **The physical complex Haar bridge** for every spectral realization, every increasing rank and
every deterministic site test bounded by one, under the Gaussian law; the eigenvector phases need
not be measurable. -/
theorem physical_haar_bridge {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (α : Fin p.N)
    (w : p.Site → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    spectral.queStatistic α w =
      (∫ H, |∑ b : ZMod p.n, average w b *
        (physicalBlockMass spectral α H b - (p.n : ℝ)⁻¹)| ^ 2
        ∂(model.law : Measure p.SiteMatrix)) +
      (1 / ((p.W : ℝ) + 1)) *
        (∫ H, ∑ b : ZMod p.n, physicalBlockMass spectral α H b ^ 2 *
          ((∑ a : Fin p.W, w (b, a) ^ 2) / (p.W : ℝ) - average w b ^ 2)
          ∂(model.law : Measure p.SiteMatrix)) := by
  rw [queStatistic_eq_canonical, canonical_physical_haar_bridge p model α w hw]
  congr 1
  · apply integral_congr_ae
    filter_upwards [spectral_blockMass_eq_canonical_ae spectral] with H hH
    unfold blockFluctuation
    simp only [Fintype.card_fin, width_mul_inv_site_count]
    simp_rw [hH α]
  · congr 1
    apply integral_congr_ae
    filter_upwards [spectral_blockMass_eq_canonical_ae spectral] with H hH
    simp_rw [hH α]

/-- Full physical block-to-site bound with the complex width coefficient,
uniform over all ranks and deterministic tests bounded by one. -/
theorem physical_haar_bound {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (α : Fin p.N)
    (w : p.Site → ℝ) (hw : ∀ x, |w x| ≤ 1) :
    spectral.queStatistic α w ≤
      (∫ H, |∑ b : ZMod p.n, average w b *
        (physicalBlockMass spectral α H b - (p.n : ℝ)⁻¹)| ^ 2
        ∂(model.law : Measure p.SiteMatrix)) + 1 / ((p.W : ℝ) + 1) := by
  rw [queStatistic_eq_canonical]
  have he : (∫ H, |blockFluctuation (canonicalBlockVector p α H) (p.N : ℝ)⁻¹ w| ^ 2
      ∂(model.law : Measure p.SiteMatrix)) =
      ∫ H, |∑ b : ZMod p.n, average w b *
        (physicalBlockMass spectral α H b - (p.n : ℝ)⁻¹)| ^ 2
        ∂(model.law : Measure p.SiteMatrix) := by
    apply integral_congr_ae
    filter_upwards [spectral_blockMass_eq_canonical_ae spectral] with H hH
    unfold blockFluctuation
    simp only [Fintype.card_fin, width_mul_inv_site_count]
    simp_rw [hH α]
  rw [← he]
  exact canonical_physical_haar_bound p model α w hw

end BlockBand.QUE.Haar
