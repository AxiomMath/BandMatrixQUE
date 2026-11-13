module

public import BlockBand.Endpoints.Response.RemoteHigherWindowGauss

/-!
# Gaussian likelihoods in coordinates: shifted GUE blocks and rescaled Ginibre bonds

The laws are coordinate pushforwards: `gueMeasure ι t` is the image of standard real
coordinates under `r ↦ √(t/2)(X + X*)`, `X = (r₀ + i r₁)/√2` (`fap_sample`), and
`ginibreMeasure ι κ s` the image of `N(0, s/2)` coordinates under `r ↦ r₀ + i r₁`. A Hermitian
shift of a GUE block is a coordinate shift (`rhw_fapSample_shift`), a real rescaling of a
Ginibre bond a coordinate rescaling, and both coordinate maps have explicit product likelihoods.

* `rhw_lintegral_comp_holder` — the transfer principle: if `S ∘ τ = F ∘ S` and the law of `τ`
  has density `ρ`, then `∫ g∘F d(S_*ν) ≤ (∫ρ^{a'})^{1/a'} (∫ g^a d(S_*ν))^{1/a}`.
* `rhw_gue_pi_shift_holder` — independent GUE blocks shifted by Hermitian `h_j`:
  the constant is `exp((a'-1) Σ_j ‖h_j‖²_F/(2t))`.
* `rhw_gin_pi_scale_holder` — independent Ginibre bonds rescaled by `λ > 0`: the constant is
  `(λ^{-a'}(1 - a'(1 - λ⁻²))^{-1/2})^{d/a'}`, `d` the number of real coordinates.
* `rhw_gin_pi_exp_normSq` — `∫ exp(Σ_j ‖P_j‖²_F/(2s)) d(Gin(s)^{⊗J}) = 2^{|J||ι||κ|}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
  BlockBand.SourceProcess
open scoped ENNReal NNReal ComplexConjugate

/-- `‖M‖²_F = Σ_{x,y} |M_{xy}|²`. -/
def rhwNormSq {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) : ℝ :=
  ∑ x, ∑ y, Complex.normSq (M x y)

theorem rhw_normSq_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) :
    0 ≤ rhwNormSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-!
## 1. The transfer principle
-/

theorem rhw_lintegral_comp_holder {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {ν : Measure Ω} {S : Ω → X} (hS : Measurable S) {τ : Ω → Ω} (hτ : Measurable τ)
    {ρ : Ω → ℝ≥0∞} (hρ : Measurable ρ) (hlaw : ν.map τ = ν.withDensity ρ) {F : X → X}
    (hF : Measurable F) (hcomm : ∀ ω, F (S ω) = S (τ ω)) {g : X → ℝ≥0∞} (hg : Measurable g)
    {a a' : ℝ} (ha : a.HolderConjugate a') :
    ∫⁻ x, g (F x) ∂ν.map S ≤
      (∫⁻ ω, ρ ω ^ a' ∂ν) ^ (1 / a') * (∫⁻ x, g x ^ a ∂ν.map S) ^ (1 / a) := by
  have hm1 := lintegral_map (μ := ν) (hg.comp hF) hS
  simp only [Function.comp] at hm1
  rw [hm1, lintegral_map (hg.pow_const a) hS]
  have h1 : ∫⁻ ω, g (F (S ω)) ∂ν = ∫⁻ ω, g (S ω) ∂ν.map τ := by
    have hm2 := lintegral_map (μ := ν) (hg.comp hS) hτ
    simp only [Function.comp] at hm2
    rw [hm2]
    exact lintegral_congr fun ω => by rw [hcomm]
  rw [h1, hlaw]
  exact rhw_lintegral_withDensity_holder hρ (hg.comp hS).aemeasurable ha

/-- A coordinatewise map with coordinatewise densities has the product density. -/
theorem rhw_pi_map_withDensity {K : Type*} [Fintype K] {Y : K → Type*}
    [∀ k, MeasurableSpace (Y k)] (μ : ∀ k, Measure (Y k)) [∀ k, IsProbabilityMeasure (μ k)]
    (φ : ∀ k, Y k → Y k) (hφ : ∀ k, Measurable (φ k)) (ρ : ∀ k, Y k → ℝ≥0∞)
    (hρ : ∀ k, Measurable (ρ k)) (h : ∀ k, (μ k).map (φ k) = (μ k).withDensity (ρ k)) :
    (Measure.pi μ).map (fun r k => φ k (r k)) =
      (Measure.pi μ).withDensity (fun r => ∏ k, ρ k (r k)) := by
  have : ∀ k, IsProbabilityMeasure ((μ k).map (φ k)) := fun k =>
    inferInstance
  have : ∀ k, SigmaFinite ((μ k).withDensity (ρ k)) := fun k => by
    rw [← h k]; infer_instance
  rw [Measure.pi_map_pi (fun k => (hφ k).aemeasurable),
    show (fun k => (μ k).map (φ k)) = fun k => (μ k).withDensity (ρ k) from funext h]
  exact rhw_pi_withDensity μ ρ hρ

theorem rhw_lintegral_prod_rpow {K : Type*} [Fintype K] {Y : K → Type*}
    [∀ k, MeasurableSpace (Y k)] (μ : ∀ k, Measure (Y k)) [∀ k, IsProbabilityMeasure (μ k)]
    (ρ : ∀ k, Y k → ℝ≥0∞) (hρ : ∀ k, Measurable (ρ k)) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ r, (∏ k, ρ k (r k)) ^ s ∂Measure.pi μ = ∏ k, ∫⁻ y, ρ k y ^ s ∂μ k := by
  refine (lintegral_congr fun (r : ∀ k, Y k) => (ENNReal.prod_rpow_of_nonneg (s := Finset.univ)
    (f := fun k => ρ k (r k)) hs).symm).trans ?_
  exact rhw_lintegral_prod_pi μ (fun k y => ρ k y ^ s) fun k => (hρ k).pow_const s

/-!
## 2. GUE blocks: Hermitian shifts
-/

section GUE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate shift of a Hermitian shift `h` of `GUE(t)`. -/
def rhwGueShift (t : ℝ≥0) (h : Matrix ι ι ℂ) : ((ι × ι) × Fin 2) → ℝ :=
  fun k => (if k.2 = 0 then (h k.1.1 k.1.2).re else (h k.1.1 k.1.2).im) / Real.sqrt t

omit [Fintype ι] [DecidableEq ι] in
theorem rhw_fapSample_shift (t : ℝ≥0) (ht : t ≠ 0) {h : Matrix ι ι ℂ} (hh : h.IsHermitian)
    (r : ((ι × ι) × Fin 2) → ℝ) :
    fap_sample t (r + rhwGueShift t h) = fap_sample t r + h := by
  have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.2 (fun h => ht (NNReal.coe_eq_zero.mp h.symm))
  have hts : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr htpos).ne'
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : Real.sqrt ((t : ℝ) / 2) = Real.sqrt t / Real.sqrt 2 :=
    Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)
  have key : ∀ R : ℝ, Real.sqrt t / Real.sqrt 2 * (2 * (R / Real.sqrt t)) / Real.sqrt 2 = R := by
    intro R
    field_simp
    linear_combination (-R) * h22
  ext a b
  have h0 : conj (h b a) = h a b := by
    simpa [Matrix.conjTranspose_apply] using congrArg (fun M => M a b) hh
  have hba : h b a = conj (h a b) := by rw [← h0, Complex.conj_conj]
  have hre : (h b a).re = (h a b).re := by rw [hba, Complex.conj_re]
  have him : (h b a).im = -(h a b).im := by rw [hba, Complex.conj_im]
  simp only [fap_sample, gueSample, circularBrownianCoordinates, rhwGueShift, Matrix.of_apply,
    Matrix.add_apply, Pi.add_apply]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofReal_re, Complex.conj_re, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.mul_im, Complex.conj_im, Complex.div_ofReal_im, Complex.ofReal_add, Fin.isValue,
      ite_true, one_ne_zero, ite_false, hre, him, hsq, map_div₀, Complex.conj_ofReal]
    linear_combination key (h a b).re
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofReal_re, Complex.conj_re, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.mul_im, Complex.conj_im, Complex.div_ofReal_im, Complex.ofReal_add, Fin.isValue,
      ite_true, one_ne_zero, ite_false, hre, him, hsq, map_div₀, Complex.conj_ofReal]
    linear_combination key (h a b).im

omit [DecidableEq ι] in
theorem rhw_sum_gueShift_sq (t : ℝ≥0) (ht : t ≠ 0) (h : Matrix ι ι ℂ) :
    ∑ k, rhwGueShift t h k ^ 2 = rhwNormSq h / t := by
  have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.2 (fun h => ht (NNReal.coe_eq_zero.mp h.symm))
  have htt : Real.sqrt t ^ 2 = t := Real.sq_sqrt htpos.le
  simp only [rhwGueShift, rhwNormSq, Fintype.sum_prod_type, Fin.sum_univ_two, ite_true,
    one_ne_zero, ite_false, div_pow, htt, Complex.normSq_apply,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

omit [DecidableEq ι] in
theorem rhw_gue_eq_map (t : ℝ≥0) : gueMeasure ι t = (fap_coordLaw ι).map (fap_sample t) := by
  unfold gueMeasure commonCircularIncrementLaw
  rw [Measure.map_map (fap_measurable_gueSample t) fap_measurable_circular]
  rfl

omit [DecidableEq ι] in
theorem rhw_coordLaw_map_shift (m : ((ι × ι) × Fin 2) → ℝ) :
    (fap_coordLaw ι).map (fun r k => r k + m k) =
      (fap_coordLaw ι).withDensity (fun r => ∏ k, fa_ratio (m k) 1 (r k)) := by
  refine rhw_pi_map_withDensity _ (fun k y => y + m k) (fun k => measurable_add_const _)
    (fun k => fa_ratio (m k) 1) (fun k => fa_measurable_ratio _ _) fun k => ?_
  rw [gaussianReal_map_add_const, zero_add, fa_withDensity_ratio _ one_ne_zero]

omit [DecidableEq ι] in
theorem rhw_coordPi_map_shift {J : Type*} [Fintype J] (M : J → ((ι × ι) × Fin 2) → ℝ) :
    (Measure.pi fun _ : J => fap_coordLaw ι).map (fun r j k => r j k + M j k) =
      (Measure.pi fun _ : J => fap_coordLaw ι).withDensity
        (fun r => ∏ j, ∏ k, fa_ratio (M j k) 1 (r j k)) :=
  rhw_pi_map_withDensity (fun _ : J => fap_coordLaw ι) (fun j y k => y k + M j k)
    (fun _ => by fun_prop) (fun j y => ∏ k, fa_ratio (M j k) 1 (y k))
    (fun j => Finset.measurable_prod _ fun k _ =>
      (fa_measurable_ratio _ _).comp (measurable_pi_apply k))
    fun j => rhw_coordLaw_map_shift (M j)

omit [DecidableEq ι] in
theorem rhw_coordPi_ratio_moment {J : Type*} [Fintype J] (M : J → ((ι × ι) × Fin 2) → ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ r, (∏ j, ∏ k, fa_ratio (M j k) 1 (r j k)) ^ s ∂(Measure.pi fun _ : J => fap_coordLaw ι) =
      ENNReal.ofReal (Real.exp (s * (s - 1) * (∑ j, ∑ k, M j k ^ 2) / 2)) := by
  rw [rhw_lintegral_prod_rpow (fun _ : J => fap_coordLaw ι)
    (fun j y => ∏ k, fa_ratio (M j k) 1 (y k)) (fun j => Finset.measurable_prod _ fun k _ =>
      (fa_measurable_ratio _ _).comp (measurable_pi_apply k)) hs]
  have h1 : ∀ j, ∫⁻ y, (∏ k, fa_ratio (M j k) 1 (y k)) ^ s ∂fap_coordLaw ι =
      ENNReal.ofReal (Real.exp (s * (s - 1) * (∑ k, M j k ^ 2) / 2)) := by
    intro j
    rw [rhw_lintegral_prod_rpow (fun _ => gaussianReal 0 1) (fun k => fa_ratio (M j k) 1)
      (fun k => fa_measurable_ratio _ _) hs]
    simp_rw [rhw_lintegral_ratio_rpow _ hs]
    rw [← ENNReal.ofReal_prod_of_nonneg fun k _ => (Real.exp_pos _).le, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum, Finset.sum_div]
  simp_rw [h1]
  rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le, ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum, Finset.sum_div]

omit [DecidableEq ι] in
/-- **Independent GUE blocks under Hermitian shifts** (Hölder form). -/
theorem rhw_gue_pi_shift_holder {J : Type*} [Fintype J] {t : ℝ≥0} (ht : t ≠ 0)
    (h : J → Matrix ι ι ℂ) (hh : ∀ j, (h j).IsHermitian) {g : (J → Matrix ι ι ℂ) → ℝ≥0∞}
    (hg : Measurable g) {a a' : ℝ} (ha : a.HolderConjugate a') :
    ∫⁻ A, g (fun j => A j + h j) ∂Measure.pi (fun _ : J => gueMeasure ι t) ≤
      ENNReal.ofReal (Real.exp ((a' - 1) * (∑ j, rhwNormSq (h j)) / (2 * t))) *
        (∫⁻ A, g A ^ a ∂Measure.pi (fun _ : J => gueMeasure ι t)) ^ (1 / a) := by
  have ha' : 0 < a' := ha.symm.pos
  have hpi : Measure.pi (fun _ : J => gueMeasure ι t) =
      (Measure.pi fun _ : J => fap_coordLaw ι).map (fun r j => fap_sample t (r j)) := by
    simp_rw [rhw_gue_eq_map]
    exact (Measure.pi_map_pi (fun _ => (fap_measurable_sample t).aemeasurable)).symm
  have hS : Measurable (fun (r : J → ((ι × ι) × Fin 2) → ℝ) j => fap_sample t (r j)) :=
    measurable_pi_iff.mpr fun j => (fap_measurable_sample t).comp (measurable_pi_apply j)
  have hρ : Measurable (fun r : J → ((ι × ι) × Fin 2) → ℝ =>
      ∏ j, ∏ k, fa_ratio (rhwGueShift t (h j) k) 1 (r j k)) := by
    refine Finset.measurable_prod _ fun j _ => Finset.measurable_prod _ fun k _ => ?_
    exact (fa_measurable_ratio _ _).comp ((measurable_pi_apply k).comp (measurable_pi_apply j))
  have hF : Measurable (fun (A : J → Matrix ι ι ℂ) j => A j + h j) :=
    measurable_pi_iff.mpr fun j => (measurable_pi_apply j).add_const _
  rw [hpi]
  refine (rhw_lintegral_comp_holder hS (by fun_prop) hρ
    (rhw_coordPi_map_shift fun j => rhwGueShift t (h j)) hF (fun r => ?_) hg ha).trans ?_
  · funext j
    exact (rhw_fapSample_shift t ht (hh j) (r j)).symm
  · gcongr
    rw [rhw_coordPi_ratio_moment _ ha'.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_of_eq ?_))
    simp_rw [rhw_sum_gueShift_sq t ht, ← Finset.sum_div]
    have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.2 (fun h => ht (NNReal.coe_eq_zero.mp h.symm))
    field_simp

end GUE

/-!
## 3. Ginibre bonds: real rescalings
-/

section Ginibre

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The flat Ginibre sample `r ↦ (r₀ + i r₁)`. -/
def rhwGinSample (r : ι × κ × Fin 2 → ℝ) : Matrix ι κ ℂ :=
  Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I

omit [Fintype ι] [Fintype κ] in
theorem rhw_measurable_ginSample : Measurable (rhwGinSample (ι := ι) (κ := κ)) := by
  rw [Matrix.measurable_iff]
  intro x y
  unfold rhwGinSample
  simp only [Matrix.of_apply]
  fun_prop

theorem rhw_gin_eq_map (s : ℝ≥0) :
    ginibreMeasure ι κ s =
      (Measure.pi fun _ : ι × κ × Fin 2 => gaussianReal 0 (s / 2)).map rhwGinSample := rfl

omit [Fintype ι] [Fintype κ] in
theorem rhw_ginSample_smul (lam : ℝ) (r : ι × κ × Fin 2 → ℝ) :
    (lam : ℂ) • rhwGinSample r = rhwGinSample (fun k => lam * r k) := by
  ext x y
  simp only [rhwGinSample, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem rhw_normSq_ginSample (r : ι × κ × Fin 2 → ℝ) :
    rhwNormSq (rhwGinSample r) = ∑ k, r k ^ 2 := by
  simp only [rhwNormSq, rhwGinSample, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem rhw_gaussian_map_mul {μ : ℝ} (hμ : 0 < μ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 v).map (fun y => μ * y) = (gaussianReal 0 v).withDensity (rhwScaleRatio μ v) := by
  rw [gaussianReal_map_const_mul, mul_zero, rhw_withDensity_scaleRatio hμ hv]

/-- The coordinate law of `J` independent Ginibre bonds. -/
abbrev rhwGinCoordLaw (J : Type*) [Fintype J] (s : ℝ≥0) :
    Measure (J → ι × κ × Fin 2 → ℝ) :=
  Measure.pi fun _ : J => Measure.pi fun _ : ι × κ × Fin 2 => gaussianReal 0 (s / 2)

theorem rhw_gin_pi_eq_map {J : Type*} [Fintype J] (s : ℝ≥0) :
    Measure.pi (fun _ : J => ginibreMeasure ι κ s) =
      (rhwGinCoordLaw (ι := ι) (κ := κ) J s).map (fun r j => rhwGinSample (r j)) := by
  simp_rw [rhw_gin_eq_map]
  exact (Measure.pi_map_pi (fun _ => rhw_measurable_ginSample.aemeasurable)).symm

theorem rhw_ginCoord_map_scale {J : Type*} [Fintype J] {s : ℝ≥0} (hs : s ≠ 0) {lam : ℝ}
    (hlam : 0 < lam) :
    (rhwGinCoordLaw (ι := ι) (κ := κ) J s).map (fun r j k => lam * r j k) =
      (rhwGinCoordLaw (ι := ι) (κ := κ) J s).withDensity
        (fun r => ∏ j, ∏ k, rhwScaleRatio lam (s / 2) (r j k)) := by
  have hs2 : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
  refine rhw_pi_map_withDensity (fun _ : J => Measure.pi fun _ : ι × κ × Fin 2 =>
      gaussianReal 0 (s / 2)) (fun _ y k => lam * y k) (fun _ => by fun_prop)
    (fun _ y => ∏ k, rhwScaleRatio lam (s / 2) (y k))
    (fun _ => Finset.measurable_prod _ fun k _ =>
      (rhw_measurable_scaleRatio _ _).comp (measurable_pi_apply k)) fun _ => ?_
  exact rhw_pi_map_withDensity (fun _ : ι × κ × Fin 2 => gaussianReal 0 (s / 2))
    (fun _ y => lam * y) (fun _ => measurable_const_mul _) (fun _ => rhwScaleRatio lam (s / 2))
    (fun _ => rhw_measurable_scaleRatio _ _) fun _ => rhw_gaussian_map_mul hlam hs2

theorem rhw_ginCoord_scale_moment {J : Type*} [Fintype J] {s : ℝ≥0} (hs : s ≠ 0) {lam : ℝ}
    (hlam : 0 < lam) {a' : ℝ} (ha' : 0 ≤ a') (hκ : 0 < 1 - a' * (1 - (lam ^ 2)⁻¹)) :
    ∫⁻ r, (∏ j, ∏ k, rhwScaleRatio lam (s / 2) (r j k)) ^ a'
        ∂rhwGinCoordLaw (ι := ι) (κ := κ) J s =
      ENNReal.ofReal (lam ^ (-a') * (1 - a' * (1 - (lam ^ 2)⁻¹)) ^ (-(1 / 2 : ℝ))) ^
        (Fintype.card J * Fintype.card (ι × κ × Fin 2)) := by
  have hs2 : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
  rw [rhw_lintegral_prod_rpow (fun _ : J => Measure.pi fun _ : ι × κ × Fin 2 =>
      gaussianReal 0 (s / 2)) (fun _ y => ∏ k, rhwScaleRatio lam (s / 2) (y k))
    (fun _ => Finset.measurable_prod _ fun k _ =>
      (rhw_measurable_scaleRatio _ _).comp (measurable_pi_apply k)) ha']
  have h1 : ∫⁻ y, (∏ k, rhwScaleRatio lam (s / 2) (y k)) ^ a'
      ∂(Measure.pi fun _ : ι × κ × Fin 2 => gaussianReal 0 (s / 2)) =
      ENNReal.ofReal (lam ^ (-a') * (1 - a' * (1 - (lam ^ 2)⁻¹)) ^ (-(1 / 2 : ℝ))) ^
        Fintype.card (ι × κ × Fin 2) := by
    rw [rhw_lintegral_prod_rpow (fun _ : ι × κ × Fin 2 => gaussianReal 0 (s / 2))
      (fun _ => rhwScaleRatio lam (s / 2)) (fun _ => rhw_measurable_scaleRatio _ _) ha']
    simp_rw [rhw_lintegral_scaleRatio_rpow hlam hs2 ha' hκ]
    rw [Finset.prod_const, Finset.card_univ]
  simp_rw [h1]
  rw [Finset.prod_const, Finset.card_univ, ← pow_mul, Nat.mul_comm (Fintype.card (ι × κ × Fin 2))]

/-- **Independent Ginibre bonds under a real rescaling `λ > 0`** (Hölder form). -/
theorem rhw_gin_pi_scale_holder {J : Type*} [Fintype J] {s : ℝ≥0} (hs : s ≠ 0) {lam : ℝ}
    (hlam : 0 < lam) {f : (J → Matrix ι κ ℂ) → ℝ≥0∞} (hf : Measurable f) {a a' : ℝ}
    (ha : a.HolderConjugate a') (hκ : 0 < 1 - a' * (1 - (lam ^ 2)⁻¹)) :
    ∫⁻ P, f (fun j => (lam : ℂ) • P j) ∂Measure.pi (fun _ : J => ginibreMeasure ι κ s) ≤
      (ENNReal.ofReal (lam ^ (-a') * (1 - a' * (1 - (lam ^ 2)⁻¹)) ^ (-(1 / 2 : ℝ))) ^
          (Fintype.card J * Fintype.card (ι × κ × Fin 2))) ^ (1 / a') *
        (∫⁻ P, f P ^ a ∂Measure.pi (fun _ : J => ginibreMeasure ι κ s)) ^ (1 / a) := by
  have ha' : 0 < a' := ha.symm.pos
  have hS : Measurable (fun (r : J → ι × κ × Fin 2 → ℝ) j => rhwGinSample (r j)) :=
    measurable_pi_iff.mpr fun j => rhw_measurable_ginSample.comp (measurable_pi_apply j)
  have hρ : Measurable (fun r : J → ι × κ × Fin 2 → ℝ =>
      ∏ j, ∏ k, rhwScaleRatio lam (s / 2) (r j k)) := by
    refine Finset.measurable_prod _ fun j _ => Finset.measurable_prod _ fun k _ => ?_
    exact (rhw_measurable_scaleRatio _ _).comp
      ((measurable_pi_apply k).comp (measurable_pi_apply j))
  have hF : Measurable (fun (P : J → Matrix ι κ ℂ) j => (lam : ℂ) • P j) := by fun_prop
  rw [rhw_gin_pi_eq_map]
  refine (rhw_lintegral_comp_holder hS (by fun_prop) hρ (rhw_ginCoord_map_scale hs hlam) hF
    (fun r => ?_) hf ha).trans ?_
  · funext j
    exact rhw_ginSample_smul lam (r j)
  · rw [rhw_ginCoord_scale_moment hs hlam ha'.le hκ]

/-- **The exponential moment of the bond mass**:
`∫ exp(Σ_j ‖P_j‖²_F/(2s)) d(Gin(s)^{⊗J}) = 2^{|J| |ι × κ|}`. -/
theorem rhw_gin_pi_exp_normSq {J : Type*} [Fintype J] {s : ℝ≥0} (hs : s ≠ 0) :
    ∫⁻ P, ENNReal.ofReal (Real.exp ((∑ j, rhwNormSq (P j)) / (2 * s)))
        ∂Measure.pi (fun _ : J => ginibreMeasure ι κ s) =
      2 ^ (Fintype.card J * Fintype.card (ι × κ)) := by
  have hs2 : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
  have hspos : (0 : ℝ) < s := lt_of_le_of_ne s.2 (fun h => hs (NNReal.coe_eq_zero.mp h.symm))
  have hS : Measurable (fun (r : J → ι × κ × Fin 2 → ℝ) j => rhwGinSample (r j)) :=
    measurable_pi_iff.mpr fun j => rhw_measurable_ginSample.comp (measurable_pi_apply j)
  have hm : Measurable fun P : J → Matrix ι κ ℂ =>
      ENNReal.ofReal (Real.exp ((∑ j, rhwNormSq (P j)) / (2 * s))) := by
    unfold rhwNormSq
    fun_prop
  have he : ∀ y : ℝ, ENNReal.ofReal (Real.exp (y ^ 2 / (2 * s))) = ENNReal.ofReal
      (Real.exp (y ^ 2 * (1 - (Real.sqrt 2 ^ 2)⁻¹) / (2 * ((s / 2 : ℝ≥0) : ℝ)))) := by
    intro y
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), NNReal.coe_div, NNReal.coe_ofNat]
    congr 2
    field_simp
    ring
  have hpt : ∀ r : J → ι × κ × Fin 2 → ℝ,
      ENNReal.ofReal (Real.exp ((∑ j, rhwNormSq (rhwGinSample (r j))) / (2 * s))) =
        ∏ j, ∏ k, ENNReal.ofReal (Real.exp (r j k ^ 2 / (2 * s))) := by
    intro r
    simp_rw [rhw_normSq_ginSample, Finset.sum_div, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg fun j _ => Finset.prod_nonneg fun k _ => (Real.exp_pos _).le]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_prod_of_nonneg fun k _ => (Real.exp_pos _).le]
  rw [rhw_gin_pi_eq_map, lintegral_map hm hS]
  simp_rw [hpt]
  have hem : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (y ^ 2 / (2 * s))) := by fun_prop
  rw [rhw_lintegral_prod_pi (fun _ : J => Measure.pi fun _ : ι × κ × Fin 2 =>
      gaussianReal 0 (s / 2)) (fun _ y => ∏ k, ENNReal.ofReal (Real.exp (y k ^ 2 / (2 * s))))
    (fun _ => Finset.measurable_prod _ fun k _ => hem.comp (measurable_pi_apply k))]
  have h1 : ∫⁻ y, ∏ k, ENNReal.ofReal (Real.exp (y k ^ 2 / (2 * s)))
      ∂(Measure.pi fun _ : ι × κ × Fin 2 => gaussianReal 0 (s / 2)) =
      ENNReal.ofReal (Real.sqrt 2) ^ Fintype.card (ι × κ × Fin 2) := by
    rw [rhw_lintegral_prod_pi (fun _ : ι × κ × Fin 2 => gaussianReal 0 (s / 2))
      (fun _ y => ENNReal.ofReal (Real.exp (y ^ 2 / (2 * s)))) (fun _ => hem)]
    simp_rw [he, rhw_lintegral_exp_sq (by positivity : (0 : ℝ) < Real.sqrt 2) hs2]
    rw [Finset.prod_const, Finset.card_univ]
  simp_rw [h1]
  rw [Finset.prod_const, Finset.card_univ, ← pow_mul, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_prod]
  have h2 : ENNReal.ofReal (Real.sqrt 2) ^ 2 = 2 := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
    simp
  rw [show Fintype.card ι * (Fintype.card κ * 2) * Fintype.card J =
      (Fintype.card J * (Fintype.card ι * Fintype.card κ)) * 2 by ring, pow_mul', h2]

end Ginibre

end BlockBand.Endpoints
