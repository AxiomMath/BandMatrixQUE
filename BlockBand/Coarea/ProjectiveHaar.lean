module

public import Mathlib
public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Normalized projective Haar measure: probability, invariance, reindexing, affine chart

*Measure.* The measure `BlockBand.Internal.Contracts.CoareaPalm.projectiveHaar ι`,
the law of `g/‖g‖₂` (here `sphereNormalize g`, with `0 ↦ 0`) for the standard
circular vector `circularVectorLaw ι` (real and imaginary parts i.i.d. `N(0,1/2)`).
*Domain:* any finite index type `ι` (`ι = Fin d` for the chart formula). Everything is exact
and non-asymptotic; there is no norm or uniformity statement.

* `circularVectorLaw_eq_withDensity`: `circularVectorLaw ι` has Lebesgue density
  `π^{-card ι} e^{-Σ|g_a|²}` on `ι → ℂ` (product Lebesgue measure `volume`).
* `isProbabilityMeasure_projectiveHaar`, `ae_l2Norm_projectiveHaar`.
* `projectiveHaar_map_unitary`, `projectiveHaar_map_smul`: invariance under every unitary
  matrix and every phase `c`, `‖c‖ = 1`.
* `circularVectorLaw_map_comp_equiv`, `projectiveHaar_map_comp_equiv`: for an equivalence
  `e : ι ≃ κ` of finite types, `(projectiveHaar ι).map (fun v => v ∘ e.symm) =
  projectiveHaar κ` (used to move between `PairSite p i` and `Fin (2W)`).
* `lintegral_projectiveHaar_affineChart` (`d = n+1`) and
  `lintegral_projectiveHaar_affineChart_of_one_le` (`d ≥ 1`): for every measurable
  phase-invariant `h ≥ 0`,
  `∫⁻ h dν_d = ((d-1)!/π^{d-1}) ∫⁻_{ℂ^{d-1}} (1+‖z‖²)^{-d} h((1+‖z‖²)^{-1/2}(1,z)) dz`,
  with `‖z‖² = chartSq z = Σ|z_i|²`, `dz` the product Lebesgue measure on `Fin (d-1) → ℂ`,
  and `(1,z)` the pivot-first vector `Fin.cons 1 z` (resp. `affineLift z`).
  Proof: Gaussian density, `g = (w, w z)` (complex scaling Jacobian `|w|^{2(d-1)}`),
  phase invariance, radial Gaussian moment `∫_ℂ |w|^{2n} e^{-a|w|²} = π n!/a^{n+1}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.ProjectiveHaar

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal
open BlockBand.Internal.Contracts.CoareaPalm

theorem lintegral_pi_fin_prod {α : Type*} [MeasurableSpace α] :
    ∀ (n : ℕ) (μ : Fin n → Measure α) [∀ i, SigmaFinite (μ i)]
      (f : Fin n → α → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i
  | 0, μ, _, f, _ => by
      simp
  | n + 1, μ, _, f, hf => by
      have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
      rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [Fin.prod_univ_succ]
      have hcomp : ∀ p : α × (Fin n → α),
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm p 0 = p.1 ∧
          ∀ j : Fin n,
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm p j.succ =
              p.2 j := by
        intro p
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.cons_succ]
      simp_rw [fun p => (hcomp p).1, fun p j => (hcomp p).2 j]
      simp only [Fin.succAbove_zero]
      have hg : Measurable (fun y : Fin n → α => ∏ j, f j.succ (y j)) :=
        Finset.measurable_prod _ fun j _ => (hf j.succ).comp (measurable_pi_apply j)
      rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → α => ∏ j, f j.succ (y j))
          (hf 0).aemeasurable hg.aemeasurable,
        lintegral_pi_fin_prod n (fun j => μ j.succ) (fun j => f j.succ)
          (fun j => hf j.succ)]

theorem lintegral_pi_prod {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (f : ι → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft (fun i : ι => μ i) e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have h1 : ∀ x : Fin (Fintype.card ι) → α,
      ∏ i, f i ((MeasurableEquiv.piCongrLeft (fun _ : ι => α) e) x i) =
        ∏ j, f (e j) (x j) := by
    intro x
    rw [← e.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp_rw [h1]
  rw [lintegral_pi_fin_prod _ (fun j => μ (e j)) (fun j => f (e j)) (fun j => hf (e j))]
  exact e.prod_comp (fun i => ∫⁻ y, f i y ∂μ i)

theorem pi_withDensity {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (f : ι → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [hsf : ∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_pi_prod _ f hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

/-- Pushforward of a density measure by a measurable equivalence. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : β → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (f ∘ e)).map e = (μ.map e).withDensity f := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs hf e.measurable]
  rfl

/-- One-coordinate standard circular density `π⁻¹ e^{-|w|²}`. -/
def circularDensityOne (w : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-Complex.normSq w))

theorem measurable_circularDensityOne : Measurable circularDensityOne := by
  unfold circularDensityOne; fun_prop

/-- One-coordinate circular law: `(re, im)` independent `N(0,1/2)`. -/
def circularLawOne : Measure ℂ :=
  (Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map Complex.measurableEquivPi.symm

instance : IsProbabilityMeasure circularLawOne := by
  unfold circularLawOne
  infer_instance

theorem gaussianPDF_half (x : ℝ) :
    gaussianPDF 0 (1 / 2 : ℝ≥0) x =
      ENNReal.ofReal ((Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2)) := by
  rw [gaussianPDF, gaussianPDFReal]
  congr 1
  push_cast
  congr 2
  · ring_nf
  · ring_nf

theorem circularLawOne_eq : circularLawOne = volume.withDensity circularDensityOne := by
  have hG : gaussianReal 0 (1 / 2 : ℝ≥0) = volume.withDensity (gaussianPDF 0 (1 / 2 : ℝ≥0)) :=
    gaussianReal_of_var_ne_zero 0 (by norm_num)
  have hsf : ∀ _ : Fin 2, SigmaFinite ((volume : Measure ℝ).withDensity
      (gaussianPDF 0 (1 / 2 : ℝ≥0))) := fun _ => by rw [← hG]; infer_instance
  unfold circularLawOne
  simp_rw [hG]
  rw [pi_withDensity (fun _ : Fin 2 => (volume : Measure ℝ)) (fun _ => gaussianPDF 0 (1 / 2 : ℝ≥0))
    (fun _ => measurable_gaussianPDF 0 _) (hsf := hsf)]
  have hfun : (fun x : Fin 2 → ℝ => ∏ i, gaussianPDF 0 (1 / 2 : ℝ≥0) (x i)) =
      circularDensityOne ∘ Complex.measurableEquivPi.symm := by
    funext x
    simp only [Fin.prod_univ_two, gaussianPDF_half, Function.comp_apply,
      Complex.measurableEquivPi_symm_apply, circularDensityOne]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hnorm : Complex.normSq ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) = x 0 ^ 2 + x 1 ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    rw [hnorm]
    have hpi : (Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹ = Real.pi⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt Real.pi_pos.le]
    calc (Real.sqrt Real.pi)⁻¹ * Real.exp (-x 0 ^ 2) * ((Real.sqrt Real.pi)⁻¹ * Real.exp (-x 1 ^ 2))
        = ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹) *
            (Real.exp (-x 0 ^ 2) * Real.exp (-x 1 ^ 2)) := by ring
      _ = _ := by rw [hpi, ← Real.exp_add]; ring_nf
  rw [hfun, ← volume_pi, map_withDensity_equiv _ _ _ measurable_circularDensityOne,
    (Complex.volume_preserving_equiv_pi.symm _).map_eq]

theorem circularVectorLaw_eq_pi (ι : Type*) [Fintype ι] :
    circularVectorLaw ι = Measure.pi fun _ : ι => circularLawOne := by
  have hcurry := Measure.infinitePi_map_curry
    (fun (_ : ι) (_ : Fin 2) => gaussianReal 0 (1 / 2 : ℝ≥0))
  simp only [Measure.infinitePi_eq_pi] at hcurry
  have hφ : (fun (r : ι × Fin 2 → ℝ) (a : ι) => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I) =
      (fun y : ι → Fin 2 → ℝ => fun a => Complex.measurableEquivPi.symm (y a)) ∘
        (MeasurableEquiv.curry ι (Fin 2) ℝ) := by
    funext r a
    simp [Complex.measurableEquivPi_symm_apply]
  have hmeas : Measurable
      (fun y : ι → Fin 2 → ℝ => fun a => Complex.measurableEquivPi.symm (y a)) := by
    fun_prop
  rw [circularVectorLaw, hφ, ← Measure.map_map hmeas (MeasurableEquiv.measurable _), hcurry,
    Measure.pi_map_pi (fun _ => Complex.measurableEquivPi.symm.measurable.aemeasurable)]
  rfl

/-- Joint standard circular density `π^{-d} e^{-Σ|g_a|²}`. -/
def circularDensity (ι : Type*) [Fintype ι] (g : ι → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.pi ^ Fintype.card ι)⁻¹ * Real.exp (-∑ a, Complex.normSq (g a)))

theorem measurable_circularDensity (ι : Type*) [Fintype ι] : Measurable (circularDensity ι) := by
  unfold circularDensity; fun_prop

theorem prod_circularDensityOne (ι : Type*) [Fintype ι] (g : ι → ℂ) :
    ∏ a, circularDensityOne (g a) = circularDensity ι g := by
  unfold circularDensityOne circularDensity
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ← Real.exp_sum, ← Finset.sum_neg_distrib, inv_pow]

theorem circularVectorLaw_eq_withDensity (ι : Type*) [Fintype ι] :
    circularVectorLaw ι = volume.withDensity (circularDensity ι) := by
  have hsf : ∀ _ : ι, SigmaFinite ((volume : Measure ℂ).withDensity circularDensityOne) :=
    fun _ => by rw [← circularLawOne_eq]; infer_instance
  rw [circularVectorLaw_eq_pi, circularLawOne_eq,
    pi_withDensity (fun _ : ι => (volume : Measure ℂ)) (fun _ => circularDensityOne)
      (fun _ => measurable_circularDensityOne) (hsf := hsf), ← volume_pi]
  congr 1
  funext g
  exact prod_circularDensityOne ι g

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (circularVectorLaw ι) := by
  rw [circularVectorLaw_eq_pi]; infer_instance

/-!
### Normalization map and probability
-/

/-- The normalization map `g ↦ g/‖g‖₂` onto the unit sphere (sending `0` to `0`); named
`sphereNormalize` to avoid the root `normalize` of `NormalizationMonoid`. -/
def sphereNormalize {ι : Type*} [Fintype ι] (g : ι → ℂ) : ι → ℂ := ((l2Norm g)⁻¹ : ℂ) • g

theorem projectiveHaar_eq_map (ι : Type*) [Fintype ι] :
    projectiveHaar ι = (circularVectorLaw ι).map sphereNormalize := rfl

theorem continuous_l2Norm (ι : Type*) [Fintype ι] : Continuous (l2Norm (ι := ι)) := by
  unfold l2Norm; fun_prop

theorem measurable_sphereNormalize (ι : Type*) [Fintype ι] :
    Measurable (sphereNormalize (ι := ι)) := by
  unfold sphereNormalize
  have := (continuous_l2Norm ι).measurable
  fun_prop

theorem l2Norm_sq_eq_sum_normSq {ι : Type*} [Fintype ι] (g : ι → ℂ) :
    l2Norm g ^ 2 = ∑ a, Complex.normSq (g a) := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Complex.normSq_eq_norm_sq]

theorem l2Norm_nonneg {ι : Type*} [Fintype ι] (g : ι → ℂ) : 0 ≤ l2Norm g := Real.sqrt_nonneg _

theorem l2Norm_smul {ι : Type*} [Fintype ι] (c : ℂ) (g : ι → ℂ) :
    l2Norm (c • g) = ‖c‖ * l2Norm g := by
  unfold l2Norm
  have : ∑ k, ‖(c • g) k‖ ^ 2 = ‖c‖ ^ 2 * ∑ k, ‖g k‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Pi.smul_apply, mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem l2Norm_pos {ι : Type*} [Fintype ι] {g : ι → ℂ} (hg : g ≠ 0) : 0 < l2Norm g := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hg
  unfold l2Norm
  apply Real.sqrt_pos.mpr
  have hk' : 0 < ‖g k‖ ^ 2 := by positivity
  exact lt_of_lt_of_le hk' (Finset.single_le_sum (f := fun k => ‖g k‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ k))

theorem l2Norm_sphereNormalize {ι : Type*} [Fintype ι] {g : ι → ℂ} (hg : g ≠ 0) :
    l2Norm (sphereNormalize g) = 1 := by
  unfold sphereNormalize
  rw [l2Norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (l2Norm_nonneg g), inv_mul_cancel₀ (l2Norm_pos hg).ne']

theorem isProbabilityMeasure_projectiveHaar (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (projectiveHaar ι) := by
  rw [projectiveHaar_eq_map]; infer_instance

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (projectiveHaar ι) :=
  isProbabilityMeasure_projectiveHaar ι

theorem circularVectorLaw_ae_ne_zero (ι : Type*) [Fintype ι] [Nonempty ι] :
    ∀ᵐ g ∂circularVectorLaw ι, g ≠ 0 := by
  rw [circularVectorLaw_eq_withDensity]
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  have h0 : (volume : Measure (ι → ℂ)) {0} = 0 := measure_singleton 0
  exact measure_eq_zero_iff_ae_notMem.mp h0

theorem ae_l2Norm_projectiveHaar (ι : Type*) [Fintype ι] [Nonempty ι] :
    ∀ᵐ v ∂projectiveHaar ι, l2Norm v = 1 := by
  rw [projectiveHaar_eq_map, ae_map_iff (measurable_sphereNormalize ι).aemeasurable
    (measurableSet_eq_fun (continuous_l2Norm ι).measurable measurable_const)]
  filter_upwards [circularVectorLaw_ae_ne_zero ι] with g hg
  exact l2Norm_sphereNormalize hg

/-!
### Invariance
-/

/-- A complex-linear map of unit-modulus determinant preserves Lebesgue measure on `ι → ℂ`. -/
theorem map_volume_of_norm_det {ι : Type*} [Fintype ι]
    (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (hT : ‖LinearMap.det T‖ = 1) :
    (volume : Measure (ι → ℂ)).map T = volume := by
  have hdet : LinearMap.det (T.restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, hT,
      one_pow]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (ι → ℂ)))
    (f := T.restrictScalars ℝ) (by rw [hdet]; norm_num)
  rw [hdet] at h
  simpa using h

/-- A measure-preserving map fixing the density fixes the density measure. -/
theorem map_withDensity_of_invariant {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {T : α → α} (hT : Measurable T) (hμ : μ.map T = μ) {ρ : α → ℝ≥0∞} (hρ : Measurable ρ)
    (hρT : ∀ x, ρ (T x) = ρ x) :
    (μ.withDensity ρ).map T = μ.withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs]
  conv_rhs => rw [← hμ]
  rw [setLIntegral_map hs hρ hT]
  simp_rw [hρT]

theorem circularVectorLaw_map_linear {ι : Type*} [Fintype ι]
    (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (hT : ‖LinearMap.det T‖ = 1)
    (hnorm : ∀ g, ∑ a, Complex.normSq (T g a) = ∑ a, Complex.normSq (g a)) :
    (circularVectorLaw ι).map T = circularVectorLaw ι := by
  rw [circularVectorLaw_eq_withDensity]
  refine map_withDensity_of_invariant _ (T.continuous_of_finiteDimensional.measurable)
    (map_volume_of_norm_det T hT) (measurable_circularDensity ι) fun g => ?_
  simp only [circularDensity, hnorm]

theorem projectiveHaar_map_linear {ι : Type*} [Fintype ι]
    (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (hT : ‖LinearMap.det T‖ = 1)
    (hnorm : ∀ g, ∑ a, Complex.normSq (T g a) = ∑ a, Complex.normSq (g a)) :
    (projectiveHaar ι).map T = projectiveHaar ι := by
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have hl2 : ∀ g, l2Norm (T g) = l2Norm g := fun g => by
    unfold l2Norm
    simp only [← Complex.normSq_eq_norm_sq]
    rw [hnorm]
  have hcomm : (T : (ι → ℂ) → (ι → ℂ)) ∘ sphereNormalize = sphereNormalize ∘ T := by
    funext g
    simp [sphereNormalize, hl2]
  rw [projectiveHaar_eq_map, Measure.map_map hTm (measurable_sphereNormalize ι), hcomm,
    ← Measure.map_map (measurable_sphereNormalize ι) hTm, circularVectorLaw_map_linear T hT hnorm]

theorem sum_normSq_eq_re_dotProduct {ι : Type*} [Fintype ι] (g : ι → ℂ) :
    ∑ a, Complex.normSq (g a) = (star g ⬝ᵥ g).re := by
  simp [dotProduct, Complex.re_sum, Complex.normSq_apply, Complex.mul_re]

theorem sum_normSq_unitary_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) (g : ι → ℂ) :
    ∑ a, Complex.normSq ((U *ᵥ g) a) = ∑ a, Complex.normSq (g a) := by
  rw [sum_normSq_eq_re_dotProduct, sum_normSq_eq_re_dotProduct, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [h1, Matrix.one_mulVec]

/-- Unitary invariance of the normalized projective Haar measure. -/
theorem projectiveHaar_map_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (projectiveHaar ι).map (fun v => U *ᵥ v) = projectiveHaar ι := by
  have hdet : ‖LinearMap.det (Matrix.toLin' U)‖ = 1 := by
    rw [LinearMap.det_toLin']
    exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
  exact projectiveHaar_map_linear (Matrix.toLin' U) hdet (sum_normSq_unitary_mulVec hU)

/-- Phase invariance of the normalized projective Haar measure. -/
theorem projectiveHaar_map_smul {ι : Type*} [Fintype ι] {c : ℂ} (hc : ‖c‖ = 1) :
    (projectiveHaar ι).map (fun v => c • v) = projectiveHaar ι := by
  have hdet : ‖LinearMap.det (c • LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))‖ = 1 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, norm_pow, hc, one_pow]
  have hnormSq : Complex.normSq c = 1 := by rw [Complex.normSq_eq_norm_sq, hc, one_pow]
  exact projectiveHaar_map_linear (c • LinearMap.id) hdet fun g => by
    simp [Complex.normSq_mul, hnormSq]

/-!
### Radial Gaussian moment in `ℂ`
-/

theorem lintegral_ofReal_eq_of_integral_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) {c : ℝ} (hc : 0 < c)
    (h : ∫ x, f x ∂μ = c) : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ENNReal.ofReal c := by
  rw [integral_eq_lintegral_of_nonneg_ae hf hfm] at h
  have hL : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞ := by
    intro hL
    rw [hL, ENNReal.toReal_top] at h
    linarith
  rw [← h, ENNReal.ofReal_toReal hL]

/-- `∫₀^∞ r^{2n+1} e^{-a r²} dr = n!/(2 a^{n+1})`. -/
theorem integral_Ioi_pow_mul_exp_neg_mul_sq (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ r in Set.Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-a * r ^ 2) =
      n.factorial / (2 * a ^ (n + 1)) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (2 * n + 1 : ℕ)) (b := a)
    (by norm_num) (by have : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) ha
  have hcongr : ∫ r in Set.Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-a * r ^ 2) =
      ∫ r in Set.Ioi (0 : ℝ), r ^ ((2 * n + 1 : ℕ) : ℝ) * Real.exp (-a * r ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [Real.rpow_natCast]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hcongr, h]
  have hq : (-(((2 * n + 1 : ℕ) : ℝ) + 1) / 2) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
  have hg : ((((2 * n + 1 : ℕ) : ℝ) + 1) / 2) = (n : ℝ) + 1 := by push_cast; ring
  rw [hq, hg, Real.Gamma_nat_eq_factorial, Real.rpow_neg ha.le, Real.rpow_natCast]
  field_simp

/-- `∫_ℂ |w|^{2n} e^{-a|w|²} dw = π n!/a^{n+1}`. -/
theorem lintegral_normSq_pow_mul_exp (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫⁻ w : ℂ, ENNReal.ofReal (Complex.normSq w ^ n * Real.exp (-a * Complex.normSq w)) =
      ENNReal.ofReal (Real.pi * n.factorial / a ^ (n + 1)) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hns : ∀ p : ℝ × ℝ, Complex.normSq (Complex.polarCoord.symm p) = p.1 ^ 2 := by
    intro p
    rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, sq_abs]
  simp_rw [hns]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (by fun_prop)]
  simp only [smul_eq_mul, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  have hin : ∫⁻ r in Set.Ioi (0 : ℝ),
      ENNReal.ofReal r * ENNReal.ofReal ((r ^ 2) ^ n * Real.exp (-a * r ^ 2)) =
      ENNReal.ofReal (n.factorial / (2 * a ^ (n + 1))) := by
    have hc : 0 < (n.factorial : ℝ) / (2 * a ^ (n + 1)) := by positivity
    rw [← lintegral_ofReal_eq_of_integral_eq (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (f := fun r => r ^ (2 * n + 1) * Real.exp (-a * r ^ 2)) ?_ (by fun_prop) hc
      (integral_Ioi_pow_mul_exp_neg_mul_sq n ha)]
    · refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      rw [← ENNReal.ofReal_mul (le_of_lt hr)]
      congr 1
      ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have : 0 < r := hr
      positivity
  rw [lintegral_mul_const _ (by fun_prop), hin, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-!
### Complex scaling of Lebesgue measure and chart algebra
-/

/-- Complex scaling `z ↦ w • z` on `ι → ℂ`: `dy = |w|^{2·card ι} dz`. -/
theorem lintegral_comp_smul_complex {ι : Type*} [Fintype ι] {w : ℂ} (hw : w ≠ 0)
    {G : (ι → ℂ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y, G y = ENNReal.ofReal (Complex.normSq w ^ Fintype.card ι) * ∫⁻ z, G (w • z) := by
  let T : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) :=
    (w • LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)).restrictScalars ℝ
  have hdet : LinearMap.det T = Complex.normSq w ^ Fintype.card ι := by
    simp only [T]
    rw [LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
      map_pow, Algebra.norm_complex_apply, Module.finrank_fintype_fun_eq_card]
  have hpos : 0 < Complex.normSq w ^ Fintype.card ι := pow_pos (Complex.normSq_pos.mpr hw) _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (ι → ℂ)))
    (f := T) (by rw [hdet]; exact hpos.ne')
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have hcomp : ∫⁻ z, G (w • z) = ∫⁻ y, G y ∂((volume : Measure (ι → ℂ)).map T) := by
    rw [lintegral_map hG hTm]
    rfl
  rw [hcomp, hmap, lintegral_smul_measure, hdet, smul_eq_mul, ← mul_assoc,
    abs_of_pos (inv_pos.mpr hpos), ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne',
    ENNReal.ofReal_one,
    one_mul]

/-- Squared Euclidean norm `‖z‖² = Σ|z_i|²` of a chart coordinate. -/
def chartSq {n : Type*} [Fintype n] (z : n → ℂ) : ℝ := ∑ i, Complex.normSq (z i)

theorem chartSq_nonneg {n : Type*} [Fintype n] (z : n → ℂ) : 0 ≤ chartSq z :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The normalized affine-chart point `(1, z)/√(1+‖z‖²)`, pivot coordinate `0` first. -/
def affineChartPoint {n : ℕ} (z : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  ((Real.sqrt (1 + chartSq z))⁻¹ : ℂ) • (Fin.cons 1 z : Fin (n + 1) → ℂ)

theorem sum_normSq_cons {n : ℕ} (w : ℂ) (z : Fin n → ℂ) :
    ∑ i, Complex.normSq ((Fin.cons w z : Fin (n + 1) → ℂ) i) = Complex.normSq w + chartSq z := by
  rw [Fin.sum_univ_succ]
  simp [chartSq]

theorem l2Norm_cons_one {n : ℕ} (z : Fin n → ℂ) :
    l2Norm (Fin.cons 1 z : Fin (n + 1) → ℂ) = Real.sqrt (1 + chartSq z) := by
  rw [← Real.sqrt_sq (l2Norm_nonneg _), l2Norm_sq_eq_sum_normSq, sum_normSq_cons, map_one]

theorem cons_smul {n : ℕ} (w : ℂ) (z : Fin n → ℂ) :
    (Fin.cons w (w • z) : Fin (n + 1) → ℂ) = w • (Fin.cons 1 z : Fin (n + 1) → ℂ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

theorem sphereNormalize_cons_one {n : ℕ} (z : Fin n → ℂ) :
    sphereNormalize (Fin.cons 1 z : Fin (n + 1) → ℂ) = affineChartPoint z := by
  rw [sphereNormalize, l2Norm_cons_one]; rfl

theorem sphereNormalize_smul {ι : Type*} [Fintype ι] {w : ℂ} (hw : w ≠ 0) (g : ι → ℂ) :
    sphereNormalize (w • g) = ((w / (‖w‖ : ℂ)) : ℂ) • sphereNormalize g := by
  have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hw)
  unfold sphereNormalize
  rw [l2Norm_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  by_cases hg : (l2Norm g : ℂ) = 0
  · simp [hg]
  · field_simp

theorem circularDensity_smul_cons {n : ℕ} (w : ℂ) (z : Fin n → ℂ) :
    circularDensity (Fin (n + 1)) (w • (Fin.cons 1 z : Fin (n + 1) → ℂ)) =
      ENNReal.ofReal ((Real.pi ^ (n + 1))⁻¹ *
        Real.exp (-((1 + chartSq z) * Complex.normSq w))) := by
  unfold circularDensity
  have : ∑ a, Complex.normSq ((w • (Fin.cons 1 z : Fin (n + 1) → ℂ)) a) =
      (1 + chartSq z) * Complex.normSq w := by
    simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
    rw [← Finset.mul_sum, sum_normSq_cons, map_one]
    ring
  rw [this, Fintype.card_fin]

theorem measurable_cons_pair {n : ℕ} :
    Measurable (fun p : ℂ × (Fin n → ℂ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℂ)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_chartSq {n : Type*} [Fintype n] : Measurable (chartSq (n := n)) := by
  unfold chartSq; fun_prop

theorem measurable_affineChartPoint {n : ℕ} : Measurable (affineChartPoint (n := n)) := by
  have h1 : Measurable (fun z : Fin n → ℂ => (Fin.cons 1 z : Fin (n + 1) → ℂ)) :=
    measurable_cons_pair.comp (measurable_const.prodMk measurable_id)
  have h2 := measurable_chartSq (n := Fin n)
  unfold affineChartPoint
  fun_prop

/-- **Affine-chart formula** for the normalized projective Haar measure, `d = n + 1`. -/
theorem lintegral_projectiveHaar_affineChart (n : ℕ) {h : (Fin (n + 1) → ℂ) → ℝ≥0∞}
    (hh : Measurable h) (hphase : ∀ c : ℂ, ‖c‖ = 1 → ∀ v, h (c • v) = h v) :
    ∫⁻ v, h v ∂projectiveHaar (Fin (n + 1)) =
      ENNReal.ofReal (n.factorial / Real.pi ^ n) *
        ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((1 + chartSq z) ^ (n + 1))⁻¹) *
          h (affineChartPoint z) := by
  have hN := measurable_sphereNormalize (Fin (n + 1))
  have hρ := measurable_circularDensity (Fin (n + 1))
  have hF : Measurable (fun g => circularDensity (Fin (n + 1)) g * h (sphereNormalize g)) :=
    hρ.mul (hh.comp hN)
  have hP := measurable_affineChartPoint (n := n)
  rw [projectiveHaar_eq_map, lintegral_map hh hN, circularVectorLaw_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ hρ (g := fun g => h (sphereNormalize g)) (hh.comp hN)]
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ))
    0).symm
  have hsymm : ∀ p : ℂ × (Fin n → ℂ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm p =
        Fin.cons p.1 p.2 := by
    intro p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
  rw [volume_pi, ← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp only [Pi.mul_apply, hsymm]
  have hFc : Measurable (fun a : ℂ × (Fin n → ℂ) =>
      circularDensity (Fin (n + 1)) (Fin.cons a.1 a.2) * h (sphereNormalize (Fin.cons a.1 a.2))) :=
    hF.comp measurable_cons_pair
  rw [lintegral_prod _ hFc.aemeasurable]
  have hstep : ∀ᵐ w ∂(volume : Measure ℂ),
      ∫⁻ y, circularDensity (Fin (n + 1)) (Fin.cons w y) * h (sphereNormalize (Fin.cons w y)) =
        ∫⁻ z, ENNReal.ofReal (Complex.normSq w ^ n) *
          (ENNReal.ofReal ((Real.pi ^ (n + 1))⁻¹ *
            Real.exp (-((1 + chartSq z) * Complex.normSq w))) * h (affineChartPoint z)) := by
    have h0 : (volume : Measure ℂ) {0} = 0 := measure_singleton 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw
    have hw : w ≠ 0 := hw
    have hG : Measurable (fun y : Fin n → ℂ =>
        circularDensity (Fin (n + 1)) (Fin.cons w y) * h (sphereNormalize (Fin.cons w y))) :=
      hF.comp (measurable_cons_pair.comp (measurable_const.prodMk measurable_id))
    rw [lintegral_comp_smul_complex hw hG, Fintype.card_fin]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun z => ?_
    have hc : ‖w / (‖w‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr hw)]
    rw [cons_smul, circularDensity_smul_cons, sphereNormalize_smul hw, hphase _ hc,
      sphereNormalize_cons_one]
  rw [← volume_pi, lintegral_congr_ae hstep]
  have hswap : Measurable (Function.uncurry fun (w : ℂ) (z : Fin n → ℂ) =>
      ENNReal.ofReal (Complex.normSq w ^ n) *
        (ENNReal.ofReal ((Real.pi ^ (n + 1))⁻¹ *
          Real.exp (-((1 + chartSq z) * Complex.normSq w))) * h (affineChartPoint z))) := by
    have hs := measurable_chartSq (n := Fin n)
    have hhP := hh.comp hP
    unfold Function.uncurry
    fun_prop
  rw [lintegral_lintegral_swap hswap.aemeasurable]
  have hinner : ∀ z : Fin n → ℂ,
      ∫⁻ w, ENNReal.ofReal (Complex.normSq w ^ n) *
        (ENNReal.ofReal ((Real.pi ^ (n + 1))⁻¹ *
          Real.exp (-((1 + chartSq z) * Complex.normSq w))) * h (affineChartPoint z)) =
      ENNReal.ofReal (n.factorial / Real.pi ^ n) *
        (ENNReal.ofReal (((1 + chartSq z) ^ (n + 1))⁻¹) * h (affineChartPoint z)) := by
    intro z
    have hA : 0 < 1 + chartSq z := by linarith [chartSq_nonneg z]
    have hrw : ∀ w : ℂ, ENNReal.ofReal (Complex.normSq w ^ n) *
        (ENNReal.ofReal ((Real.pi ^ (n + 1))⁻¹ *
          Real.exp (-((1 + chartSq z) * Complex.normSq w))) * h (affineChartPoint z)) =
        ENNReal.ofReal ((Real.pi ^ (n + 1))⁻¹) *
          ENNReal.ofReal (Complex.normSq w ^ n *
            Real.exp (-(1 + chartSq z) * Complex.normSq w)) * h (affineChartPoint z) := by
      intro w
      have h1 : 0 ≤ Complex.normSq w ^ n := pow_nonneg (Complex.normSq_nonneg w) n
      rw [← mul_assoc, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring_nf
    simp_rw [hrw]
    have hmeas : Measurable (fun w : ℂ => ENNReal.ofReal ((Real.pi ^ (n + 1))⁻¹) *
        ENNReal.ofReal (Complex.normSq w ^ n *
          Real.exp (-(1 + chartSq z) * Complex.normSq w))) := by
      fun_prop
    rw [lintegral_mul_const _ hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_normSq_pow_mul_exp n hA, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Pivot-first embedding `z ↦ (1, z) ∈ ℂ^d` of a chart coordinate `z ∈ ℂ^{d-1}`:
coordinate `0` is `1` and coordinate `i ≥ 1` is `z_{i-1}`. -/
def affineLift {d : ℕ} (z : Fin (d - 1) → ℂ) : Fin d → ℂ :=
  fun i => if hi : (i : ℕ) = 0 then 1 else z ⟨(i : ℕ) - 1, by omega⟩

theorem affineLift_eq_cons {n : ℕ} (z : Fin n → ℂ) :
    affineLift (d := n + 1) z = (Fin.cons 1 z : Fin (n + 1) → ℂ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [affineLift]
  · simp [affineLift, Fin.cons_succ]

/-- **Affine-chart formula**, dimension `d ≥ 1` form. -/
theorem lintegral_projectiveHaar_affineChart_of_one_le (d : ℕ) (hd : 1 ≤ d)
    {h : (Fin d → ℂ) → ℝ≥0∞} (hh : Measurable h)
    (hphase : ∀ c : ℂ, ‖c‖ = 1 → ∀ v, h (c • v) = h v) :
    ∫⁻ v, h v ∂projectiveHaar (Fin d) =
      ENNReal.ofReal ((d - 1).factorial / Real.pi ^ (d - 1)) *
        ∫⁻ z : Fin (d - 1) → ℂ, ENNReal.ofReal (((1 + chartSq z) ^ d)⁻¹) *
          h (((Real.sqrt (1 + chartSq z))⁻¹ : ℂ) • affineLift z) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have key := lintegral_projectiveHaar_affineChart n hh hphase
  show _ = ENNReal.ofReal (n.factorial / Real.pi ^ n) *
        ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((1 + chartSq z) ^ (n + 1))⁻¹) *
          h (((Real.sqrt (1 + chartSq z))⁻¹ : ℂ) • affineLift (d := n + 1) z)
  simp_rw [affineLift_eq_cons]
  exact key

/-- Unitary invariance of the standard circular Gaussian vector law. -/
theorem circularVectorLaw_map_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (circularVectorLaw ι).map (fun g => U *ᵥ g) = circularVectorLaw ι := by
  have hdet : ‖LinearMap.det (Matrix.toLin' U)‖ = 1 := by
    rw [LinearMap.det_toLin']
    exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
  exact circularVectorLaw_map_linear (Matrix.toLin' U) hdet (sum_normSq_unitary_mulVec hU)

/-!
### Reindexing by an equivalence of finite index types
-/

/-- A product of identical laws is invariant under reindexing by an equivalence. -/
theorem pi_const_map_comp_symm {α β X : Type*} [Fintype α] [Fintype β] [MeasurableSpace X]
    (e : α ≃ β) (ν : Measure X) [SigmaFinite ν] :
    (Measure.pi fun _ : α => ν).map (fun x => x ∘ e.symm) = Measure.pi fun _ : β => ν :=
  (measurePreserving_arrowCongr' (fun _ : α => ν) (fun _ : β => ν) e (MeasurableEquiv.refl X)
    fun _ => MeasurePreserving.id ν).map_eq

/-- `l2Norm` is invariant under reindexing. -/
theorem l2Norm_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (g : ι → ℂ) :
    l2Norm (g ∘ e.symm) = l2Norm g := by
  unfold l2Norm
  congr 1
  exact e.symm.sum_comp (fun i => ‖g i‖ ^ 2)

/-- `sphereNormalize` commutes with reindexing. -/
theorem sphereNormalize_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (g : ι → ℂ) : sphereNormalize (g ∘ e.symm) = sphereNormalize g ∘ e.symm := by
  funext k
  simp only [sphereNormalize, l2Norm_comp_equiv, Pi.smul_apply, Function.comp_apply]

/-- Reindexing invariance of the standard circular vector law: for `e : ι ≃ κ`,
`(circularVectorLaw ι).map (· ∘ e.symm) = circularVectorLaw κ`. -/
theorem circularVectorLaw_map_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    (circularVectorLaw ι).map (fun g => g ∘ e.symm) = circularVectorLaw κ := by
  rw [circularVectorLaw_eq_pi, circularVectorLaw_eq_pi, pi_const_map_comp_symm]

/-- Reindexing invariance of `ν_d`: for an equivalence `e : ι ≃ κ` of finite
types, `(projectiveHaar ι).map (fun v => v ∘ e.symm) = projectiveHaar κ`. -/
theorem projectiveHaar_map_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    (projectiveHaar ι).map (fun v => v ∘ e.symm) = projectiveHaar κ := by
  have hc : Measurable (fun g : ι → ℂ => g ∘ e.symm) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  rw [projectiveHaar_eq_map, projectiveHaar_eq_map,
    Measure.map_map hc (measurable_sphereNormalize ι), ← circularVectorLaw_map_comp_equiv e,
    Measure.map_map (measurable_sphereNormalize κ) hc]
  congr 1
  funext g
  exact (sphereNormalize_comp_equiv e g).symm

/-- Normalization cross-check (`h = 1`): `∫_{ℂ^n} (1+‖z‖²)^{-(n+1)} d^{2n}z = π^n/n!`,
derived from `IsProbabilityMeasure (projectiveHaar (Fin (n+1)))` and the chart formula. -/
theorem lintegral_affineChart_density (n : ℕ) :
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((1 + chartSq z) ^ (n + 1))⁻¹) =
      ENNReal.ofReal (Real.pi ^ n / n.factorial) := by
  have key := lintegral_projectiveHaar_affineChart n (h := fun _ => 1) measurable_const
    (fun _ _ _ => rfl)
  simp only [lintegral_const, measure_univ, mul_one] at key
  have hc : 0 < (n.factorial : ℝ) / Real.pi ^ n := by
    have := Real.pi_pos; positivity
  rw [mul_comm] at key
  rw [ENNReal.eq_inv_of_mul_eq_one_left key.symm, ← ENNReal.ofReal_inv_of_pos hc, inv_div]

end BlockBand.Coarea.ProjectiveHaar
