module

public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Model.Construction.GaussianIntegrationByParts

/-!
# Bilinear Ornstein–Uhlenbeck covariance identity

The Gaussian interpolation step in the proof of the trace–matrix lemma: in real Gaussian
coordinates `x`, let `x_t = e^{-t}x + √(1−e^{-2t}) x'` with `x'` independent; differentiating this
interpolation gives the bilinear covariance identity
`Cov(f(x),U(x)) = ∫_0^∞ e^{-t} E[∇f(x)·Σ∇U(x_t)] dt`, where `Σ` is the real-coordinate covariance
(no conjugation is inserted).

Law: `μ = gaussianProduct v` on `ι → ℝ` (finite `ι`, any variances `v : ι → ℝ≥0`; zero
variances are allowed), `x, x'` independent, i.e. the law `μ ⊗ μ`. Partial derivatives are
the Fréchet partials `∂ᵢ f(x) = Df(x) eᵢ`, `eᵢ = Pi.single i 1`, as in
`Inputs.weightedGradientNorm`. Class: `f : (ι → ℝ) → ℂ` and `g : (ι → ℝ) → E` (`E` any complete
normed `ℂ`-space, e.g. `ℂ` or matrices) are `C¹`, bounded, with bounded derivative; no
second derivative is used (weaker than a `C²` assumption).

Proof: `φ(t) = E[f(x) • g(x_t)]`; `φ(0) = E[f g]`, `φ(∞) = E f • E g` (dominated convergence);
for `t > 0`, `φ'(t) = (e^{-t}/s_t) E[f(X) Dg(Y) Z]` with `(Y, Z) = R_θ(X, X')`,
`cos θ = e^{-t}`, `sin θ = s_t = √(1-e^{-2t})`. Rotation invariance of `μ ⊗ μ`
(Mathlib `IsGaussian.map_rotation_eq_self`) and one Gaussian integration by parts in the
rotated coordinate give `φ'(t) = -e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)]`; then
`integral_Ioi_of_hasDerivAt_of_tendsto`. The multivariate integration by parts `ou_ibp` is
proved here from the one-dimensional `gaussian_integration_by_parts` and the coordinate
splitting `ou_map_update`; `MultivariateGaussianIBP` is not used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory BlockBand.Internal.Contracts.Inputs
open scoped NNReal

variable {ι : Type} [Fintype ι]

/-- Coordinate marginals of the product Gaussian. -/
theorem ou_eval_mp (v : ι → ℝ≥0) (i : ι) :
    MeasurePreserving (fun x : ι → ℝ => x i) (gaussianProduct v) (gaussianReal 0 (v i)) :=
  measurePreserving_eval (fun i => gaussianReal 0 (v i)) i

/-- The product Gaussian is a Gaussian measure. -/
instance ou_isGaussian (v : ι → ℝ≥0) : IsGaussian (gaussianProduct v) := by
  have hind : iIndepFun (fun i (x : ι → ℝ) => x i) (gaussianProduct v) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hlaw : ∀ i, HasGaussianLaw (fun x : ι → ℝ => x i) (gaussianProduct v) := fun i =>
    { aemeasurable := (ou_eval_mp v i).measurable.aemeasurable
      isGaussian_map := by
        rw [(ou_eval_mp v i).map_eq]
        infer_instance }
  have h := (hind.hasGaussianLaw hlaw).isGaussian_map
  simpa using h

/-- The product Gaussian is centred. -/
theorem ou_integral_id (v : ι → ℝ≥0) : ∫ x, id x ∂gaussianProduct v = 0 := by
  funext i
  have hi : ∀ j, Integrable (fun x : ι → ℝ => x j) (gaussianProduct v) := fun j =>
    (ou_eval_mp v j).integrable_comp_of_integrable
      (IsGaussian.integrable_id (μ := gaussianReal 0 (v j)))
  show (∫ x, x ∂gaussianProduct v) i = 0
  rw [eval_integral hi i]
  have h := integral_map (μ := gaussianProduct v) (f := fun y : ℝ => y)
    (ou_eval_mp v i).measurable.aemeasurable aestronglyMeasurable_id
  rw [(ou_eval_mp v i).map_eq, integral_id_gaussianReal] at h
  exact h.symm

/-- Generic integrability on a Gaussian measure under an affine norm bound. -/
theorem ou_integrable_of_norm_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [SecondCountableTopology X]
    {F : Type*} [NormedAddCommGroup F]
    (ν : Measure X) [IsGaussian ν] {G : X → F} (hG : AEStronglyMeasurable G ν) (A B : ℝ)
    (h : ∀ p, ‖G p‖ ≤ A + B * ‖p‖) : Integrable G ν :=
  Integrable.mono' ((integrable_const A).add (IsGaussian.integrable_id.norm.const_mul B)) hG
    (Filter.Eventually.of_forall fun p => by simpa using h p)

/-- Rotation invariance of `μ ⊗ μ` for the product Gaussian, in integral form. -/
theorem ou_integral_rotation (v : ι → ℝ≥0) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (θ : ℝ) {G : (ι → ℝ) × (ι → ℝ) → F}
    (hG : AEStronglyMeasurable G ((gaussianProduct v).prod (gaussianProduct v))) :
    ∫ p, G (ContinuousLinearMap.rotation θ p) ∂(gaussianProduct v).prod (gaussianProduct v) =
      ∫ p, G p ∂(gaussianProduct v).prod (gaussianProduct v) := by
  have hrot := IsGaussian.map_rotation_eq_self (μ := gaussianProduct v) (ou_integral_id v) θ
  rw [← integral_map (ContinuousLinearMap.rotation θ).continuous.aemeasurable (by rwa [hrot]),
    hrot]

variable [DecidableEq ι]

/-- Splitting off coordinate `i`: `μ = (N(0,v_i) ⊗ μ).map (fun q => update q.2 i q.1)`. -/
theorem ou_map_update (v : ι → ℝ≥0) (i : ι) :
    ((gaussianReal 0 (v i)).prod (gaussianProduct v)).map
      (fun q : ℝ × (ι → ℝ) => Function.update q.2 i q.1) = gaussianProduct v := by
  have hmeas : Measurable (fun q : ℝ × (ι → ℝ) => Function.update q.2 i q.1) :=
    (continuous_snd.update i continuous_fst).measurable
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun q : ℝ × (ι → ℝ) => Function.update q.2 i q.1) ⁻¹' Set.univ.pi s =
      s i ×ˢ Set.univ.pi (Function.update s i Set.univ) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h i, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h1
      · simpa [Function.update_of_ne hj] using h2 j
  rw [hpre, Measure.prod_prod]
  unfold gaussianProduct
  rw [Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ (fun j => (gaussianReal 0 (v j))
      (Function.update s i Set.univ j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => (gaussianReal 0 (v j)) (s j))
      (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- `‖Df(x) eᵢ‖ ≤ ‖Df(x)‖`. -/
theorem ou_partial_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (ι → ℝ) →L[ℝ] F) (i : ι) : ‖L (Pi.single i 1)‖ ≤ ‖L‖ := by
  calc _ ≤ ‖L‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ := L.le_opNorm _
    _ = ‖L‖ := by rw [Pi.norm_single, norm_one, mul_one]

/-- **Multivariate Gaussian integration by parts** for bounded `C¹` functions with bounded
derivative (no hypothesis on `v`): `E[xᵢ k(x)] = vᵢ E[∂ᵢ k(x)]`. -/
theorem ou_ibp (v : ι → ℝ≥0) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (i : ι) {k : (ι → ℝ) → F} (hk : ContDiff ℝ 1 k) {C C' : ℝ}
    (hkC : ∀ x, ‖k x‖ ≤ C) (hk'C : ∀ x, ‖fderiv ℝ k x‖ ≤ C') :
    ∫ x, x i • k x ∂gaussianProduct v =
      (v i : ℝ) • ∫ x, fderiv ℝ k x (Pi.single i 1) ∂gaussianProduct v := by
  set N := gaussianReal 0 (v i)
  set μ := gaussianProduct v
  let u : ℝ × (ι → ℝ) → (ι → ℝ) := fun q => Function.update q.2 i q.1
  have hu : Continuous u := continuous_snd.update i continuous_fst
  have hmap : (N.prod μ).map u = μ := ou_map_update v i
  have hkc : Continuous k := hk.continuous
  have hk'c : Continuous (fun x => fderiv ℝ k x (Pi.single i 1)) :=
    (hk.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hd1 : ∀ x, ‖fderiv ℝ k x (Pi.single i 1)‖ ≤ C' := fun x =>
    (ou_partial_le _ i).trans (hk'C x)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hkC 0)
  have hL : ∫ x, x i • k x ∂μ = ∫ q, q.1 • k (u q) ∂(N.prod μ) := by
    conv_lhs => rw [← hmap]
    have hc : Continuous (fun x : ι → ℝ => x i • k x) := by fun_prop
    rw [integral_map (f := fun x : ι → ℝ => x i • k x) hu.aemeasurable hc.aestronglyMeasurable]
    simp [u]
  have hR : ∫ x, fderiv ℝ k x (Pi.single i 1) ∂μ =
      ∫ q, fderiv ℝ k (u q) (Pi.single i 1) ∂(N.prod μ) := by
    conv_lhs => rw [← hmap]
    rw [integral_map hu.aemeasurable hk'c.aestronglyMeasurable]
  have hIL : Integrable (fun q : ℝ × (ι → ℝ) => q.1 • k (u q)) (N.prod μ) :=
    ou_integrable_of_norm_le _ ((continuous_fst.smul (hkc.comp hu)).aestronglyMeasurable) 0 C
      (fun q => by
        rw [norm_smul]
        have h1 := norm_fst_le q
        have h2 := hkC (u q)
        nlinarith [norm_nonneg q.1, norm_nonneg (k (u q))])
  have hIR : Integrable (fun q : ℝ × (ι → ℝ) => fderiv ℝ k (u q) (Pi.single i 1)) (N.prod μ) :=
    ou_integrable_of_norm_le _ ((hk'c.comp hu).aestronglyMeasurable) C' 0
      (fun q => by simpa using hd1 (u q))
  rw [hL, hR, integral_prod_symm _ hIL, integral_prod_symm _ hIR, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hux : Continuous (fun y : ℝ => Function.update x i y) :=
    continuous_const.update i continuous_id
  have hder : ∀ y, HasDerivAt (fun y => k (Function.update x i y))
      (fderiv ℝ k (Function.update x i y) (Pi.single i 1)) y := fun y =>
    ((hk.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt y (hasDerivAt_update x i y)
  have h1 := BlockBand.Model.Construction.gaussian_integration_by_parts 0 (v i) hder
    (ou_integrable_of_norm_le N (hkc.comp hux).aestronglyMeasurable C 0
      (fun y => by simpa using hkC _))
    (ou_integrable_of_norm_le N (hk'c.comp hux).aestronglyMeasurable C' 0
      (fun y => by simpa using hd1 _))
    (ou_integrable_of_norm_le N ((continuous_id.sub continuous_const).smul
      (hkc.comp hux)).aestronglyMeasurable 0 C (fun y => by
        rw [norm_smul, sub_zero]
        have h2 := hkC (Function.update x i y)
        nlinarith [norm_nonneg y, norm_nonneg (k (Function.update x i y))]))
  simpa [u] using h1

omit [DecidableEq ι] in
/-- Derivative of `z ↦ f (c • y - s • z)`. -/
theorem ou_hasFDerivAt_shift {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (c s : ℝ)
    (y z : ι → ℝ) :
    HasFDerivAt (fun z => f (c • y - s • z))
      ((fderiv ℝ f (c • y - s • z)).comp (0 - s • ContinuousLinearMap.id ℝ (ι → ℝ))) z :=
  ((hf.differentiable one_ne_zero) _).hasFDerivAt.comp z
    ((hasFDerivAt_const (c • y) z).sub ((hasFDerivAt_id z).const_smul s))

omit [DecidableEq ι] in
/-- Integrability of `x'ᵢ f(c x - s x') a(x)` on `μ ⊗ μ`. -/
theorem ou_integrable_T (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : ι) {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) {a : (ι → ℝ) → E}
    (ha : Continuous a) {Ca : ℝ} (haC : ∀ y, ‖a y‖ ≤ Ca) (c s : ℝ) :
    Integrable (fun p : (ι → ℝ) × (ι → ℝ) => p.2 i • (f (c • p.1 - s • p.2) • a p.1))
      ((gaussianProduct v).prod (gaussianProduct v)) := by
  have hfc : Continuous f := hf.continuous
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans (hfC 0)
  have hm : Continuous (fun p : (ι → ℝ) × (ι → ℝ) => c • p.1 - s • p.2) := by fun_prop
  refine ou_integrable_of_norm_le _ ?_ 0 (Cf * Ca) (fun p => ?_)
  · exact (((continuous_apply i).comp continuous_snd).smul
      ((hfc.comp hm).smul (ha.comp continuous_fst))).aestronglyMeasurable
  · rw [norm_smul, norm_smul]
    have h1 : ‖p.2 i‖ ≤ ‖p‖ := (norm_le_pi_norm p.2 i).trans (norm_snd_le p)
    have h4 : ‖f (c • p.1 - s • p.2)‖ * ‖a p.1‖ ≤ Cf * Ca :=
      mul_le_mul (hfC _) (haC _) (norm_nonneg _) hCf
    nlinarith [norm_nonneg (p.2 i), mul_nonneg (norm_nonneg (f (c • p.1 - s • p.2)))
      (norm_nonneg (a p.1))]

/-- Integrability of `∂ᵢ f(c x - s x') a(x)` on `μ ⊗ μ`. -/
theorem ou_integrable_J (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : ι) {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf' : ℝ}
    (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {a : (ι → ℝ) → E}
    (ha : Continuous a) {Ca : ℝ} (haC : ∀ y, ‖a y‖ ≤ Ca) (c s : ℝ) :
    Integrable (fun p : (ι → ℝ) × (ι → ℝ) =>
      fderiv ℝ f (c • p.1 - s • p.2) (Pi.single i 1) • a p.1)
      ((gaussianProduct v).prod (gaussianProduct v)) := by
  have hf'c : Continuous (fun x => fderiv ℝ f x (Pi.single i 1)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hm : Continuous (fun p : (ι → ℝ) × (ι → ℝ) => c • p.1 - s • p.2) := by fun_prop
  refine ou_integrable_of_norm_le _ ?_ (Cf' * Ca) 0 (fun p => ?_)
  · exact ((hf'c.comp hm).smul (ha.comp continuous_fst)).aestronglyMeasurable
  · rw [norm_smul, zero_mul, add_zero]
    exact mul_le_mul ((ou_partial_le _ i).trans (hf'C _)) (haC _) (norm_nonneg _)
      ((norm_nonneg _).trans (hf'C 0))

/-- Gaussian integration by parts in the second factor of `μ ⊗ μ`, for the integrands of the
interpolation: `E[x'ᵢ f(c x - s x') a(x)] = -s vᵢ E[∂ᵢ f(c x - s x') a(x)]`. -/
theorem ou_ibp_prod (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (i : ι) {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {a : (ι → ℝ) → E}
    (ha : Continuous a) {Ca : ℝ} (haC : ∀ y, ‖a y‖ ≤ Ca) (c s : ℝ) :
    ∫ p, p.2 i • (f (c • p.1 - s • p.2) • a p.1)
        ∂(gaussianProduct v).prod (gaussianProduct v) =
      (-s * v i) • ∫ p, fderiv ℝ f (c • p.1 - s • p.2) (Pi.single i 1) • a p.1
        ∂(gaussianProduct v).prod (gaussianProduct v) := by
  set μ := gaussianProduct v
  have hfc : Continuous f := hf.continuous
  have hf'c : Continuous (fun x => fderiv ℝ f x (Pi.single i 1)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans (haC 0)
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans (hfC 0)
  have hIL := ou_integrable_T v i hf hfC ha haC c s
  have hIR := ou_integrable_J v i hf hf'C ha haC c s
  rw [integral_prod _ hIL, integral_prod _ hIR, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  simp_rw [← smul_assoc]
  rw [integral_smul_const, integral_smul_const]
  -- the scalar identity
  have hk : ContDiff ℝ 1 (fun z => f (c • y - s • z)) :=
    hf.comp (contDiff_const.sub (contDiff_id.const_smul s))
  have hder : ∀ z, fderiv ℝ (fun z => f (c • y - s • z)) z (Pi.single i 1) =
      (-s) • fderiv ℝ f (c • y - s • z) (Pi.single i 1) := fun z => by
    rw [(ou_hasFDerivAt_shift hf c s y z).fderiv]
    simp
  have hnorm : ∀ z, ‖fderiv ℝ (fun z => f (c • y - s • z)) z‖ ≤ Cf' * |s| := fun z => by
    rw [(ou_hasFDerivAt_shift hf c s y z).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hf'C _) ?_ (norm_nonneg _)
      ((norm_nonneg _).trans (hf'C 0)))
    rw [zero_sub, norm_neg]
    refine (norm_smul_le s (ContinuousLinearMap.id ℝ (ι → ℝ))).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg s) (ContinuousLinearMap.norm_id_le)
  have h1 := ou_ibp v i hk (fun z => hfC _) hnorm
  rw [h1]
  simp_rw [hder]
  rw [integral_smul, smul_smul, smul_assoc]
  congr 1
  ring

/-- The bilinear Dirichlet integrand `Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(y)` (no conjugation). -/
def ouDir (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : (ι → ℝ) → ℂ) (g : (ι → ℝ) → E) (x y : ι → ℝ) : E :=
  ∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f x (Pi.single i 1)) • fderiv ℝ g y (Pi.single i 1)

theorem ou_continuous_dir (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {g : (ι → ℝ) → E} (hg : ContDiff ℝ 1 g) :
    Continuous (fun q : (ι → ℝ) × (ι → ℝ) => ouDir v f g q.1 q.2) := by
  unfold ouDir
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_const.mul (((hf.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply
    continuous_const)).smul (((hg.continuous_fderiv one_ne_zero).comp continuous_snd).clm_apply
    continuous_const)

theorem ou_norm_dir_le (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : (ι → ℝ) → ℂ} {g : (ι → ℝ) → E} {Cf' Cg' : ℝ} (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf')
    (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') (x y : ι → ℝ) :
    ‖ouDir v f g x y‖ ≤ (∑ i, (v i : ℝ)) * Cf' * Cg' := by
  unfold ouDir
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
  have hCf : 0 ≤ Cf' := (norm_nonneg _).trans (hf'C 0)
  have h1 := (ou_partial_le (fderiv ℝ f x) i).trans (hf'C x)
  have h2 := (ou_partial_le (fderiv ℝ g y) i).trans (hg'C y)
  have h3 : (v i : ℝ) * ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ (v i : ℝ) * Cf' :=
    mul_le_mul_of_nonneg_left h1 (v i).2
  exact mul_le_mul h3 h2 (norm_nonneg _) (mul_nonneg (v i).2 hCf)

/-- Expansion of a linear map on `ι → ℝ` in coordinates. -/
theorem ou_clm_expand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (ι → ℝ) →L[ℝ] F) (z : ι → ℝ) : L z = ∑ i, z i • L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]

omit [Fintype ι] [DecidableEq ι] in
theorem ou_rot_inv (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (a b : ι → ℝ) :
    c • (c • a + s • b) - s • (-s • a + c • b) = a := by
  rw [show c • (c • a + s • b) - s • (-s • a + c • b) = (c ^ 2 + s ^ 2) • a by module, hcs,
    one_smul]

/-- **Rotated derivative identity.** With `(Y, Z) = R_θ(X, X')`,
`E[f(X) Dg(Y) Z] = -sin θ · E[Σᵢ vᵢ ∂ᵢ f(X) ∂ᵢ g(Y)]`: rotation invariance of `μ ⊗ μ`, one
Gaussian integration by parts in the rotated second coordinate, and rotation back. -/
theorem ou_rotated_derivative (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg' : ℝ} (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') (θ : ℝ) :
    ∫ p, f p.1 • fderiv ℝ g (Real.cos θ • p.1 + Real.sin θ • p.2)
        (-Real.sin θ • p.1 + Real.cos θ • p.2) ∂(gaussianProduct v).prod (gaussianProduct v) =
      (-Real.sin θ) • ∫ p, ouDir v f g p.1 (Real.cos θ • p.1 + Real.sin θ • p.2)
        ∂(gaussianProduct v).prod (gaussianProduct v) := by
  set μ := gaussianProduct v
  set c := Real.cos θ
  set s := Real.sin θ
  have hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hfc : Continuous f := hf.continuous
  have hg'c : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hm : Continuous (fun p : (ι → ℝ) × (ι → ℝ) => c • p.1 - s • p.2) := by fun_prop
  have hgi : ∀ i, Continuous (fun y => fderiv ℝ g y (Pi.single i 1)) := fun i =>
    hg'c.clm_apply continuous_const
  have hgiC : ∀ i y, ‖fderiv ℝ g y (Pi.single i 1)‖ ≤ Cg' := fun i y =>
    (ou_partial_le _ i).trans (hg'C y)
  -- rotate forward
  let H : (ι → ℝ) × (ι → ℝ) → E := fun q => f (c • q.1 - s • q.2) • fderiv ℝ g q.1 q.2
  have hHc : Continuous H := (hfc.comp hm).smul (hg'c.comp continuous_fst |>.clm_apply
    continuous_snd)
  have h1 : ∫ p, f p.1 • fderiv ℝ g (c • p.1 + s • p.2) (-s • p.1 + c • p.2) ∂μ.prod μ =
      ∫ p, H p ∂μ.prod μ := by
    rw [← ou_integral_rotation v θ hHc.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [H, ContinuousLinearMap.rotation_apply]
    rw [ou_rot_inv c s hcs]
  -- expand in coordinates
  have h2 : ∀ q, H q = ∑ i, q.2 i • (f (c • q.1 - s • q.2) • fderiv ℝ g q.1 (Pi.single i 1)) :=
    fun q => by
      simp only [H]
      rw [ou_clm_expand (fderiv ℝ g q.1) q.2, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm]
  have h3 : ∫ p, H p ∂μ.prod μ = ∑ i, ((-s * v i) • ∫ p, fderiv ℝ f (c • p.1 - s • p.2)
      (Pi.single i 1) • fderiv ℝ g p.1 (Pi.single i 1) ∂μ.prod μ) := by
    simp_rw [h2]
    rw [integral_finsetSum _ fun i _ => ou_integrable_T v i hf hfC (hgi i) (hgiC i) c s]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact ou_ibp_prod v i hf hfC hf'C (hgi i) (hgiC i) c s
  -- rotate back
  let J : (ι → ℝ) × (ι → ℝ) → E := fun q => ouDir v f g (c • q.1 - s • q.2) q.1
  have hJc : Continuous J :=
    (ou_continuous_dir v hf hg).comp (hm.prodMk continuous_fst)
  have h4 : ∫ p, ouDir v f g p.1 (c • p.1 + s • p.2) ∂μ.prod μ = ∫ p, J p ∂μ.prod μ := by
    rw [← ou_integral_rotation v θ hJc.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [J, ContinuousLinearMap.rotation_apply]
    rw [ou_rot_inv c s hcs]
  have h5 : ∫ p, J p ∂μ.prod μ = ∑ i, ((v i : ℝ) • ∫ p, fderiv ℝ f (c • p.1 - s • p.2)
      (Pi.single i 1) • fderiv ℝ g p.1 (Pi.single i 1) ∂μ.prod μ) := by
    simp only [J, ouDir]
    rw [integral_finsetSum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only
      rw [mul_smul, Complex.coe_smul]
    · simp_rw [mul_smul, Complex.coe_smul]
      exact (ou_integrable_J v i hf hf'C (hgi i) (hgiC i) c s).smul _
  rw [h1, h3, h4, h5, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]

/-!
## The Ornstein–Uhlenbeck interpolation in time
-/

/-- `(e^{-t})² = e^{-2t}`. -/
theorem ou_exp_sq (t : ℝ) : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
  rw [← Real.exp_nat_mul]; ring_nf

theorem ou_one_sub_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-2 * t) := by
  have : Real.exp (-2 * t) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem ou_sqrt_pos {t : ℝ} (ht : 0 < t) : 0 < Real.sqrt (1 - Real.exp (-2 * t)) :=
  Real.sqrt_pos.mpr (ou_one_sub_pos ht)

/-- Derivative of `t ↦ √(1 - e^{-2t})` for `t > 0`. -/
theorem ou_hasDerivAt_sqrt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => Real.sqrt (1 - Real.exp (-2 * τ)))
      (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) t := by
  have h1 : HasDerivAt (fun τ => 1 - Real.exp (-2 * τ)) (-(Real.exp (-2 * t) * (-2 * 1))) t :=
    (((hasDerivAt_id t).const_mul (-2)).exp).const_sub 1
  refine (h1.sqrt (ou_one_sub_pos ht).ne').congr_deriv ?_
  have := (ou_sqrt_pos ht).ne'
  field_simp

omit [DecidableEq ι] in
/-- Integrability of a bounded continuous function on `μ ⊗ μ`. -/
theorem ou_integrable_bdd (v : ι → ℝ≥0) {F : Type*} [NormedAddCommGroup F]
    {G : (ι → ℝ) × (ι → ℝ) → F} (hG : Continuous G) {C : ℝ} (hC : ∀ p, ‖G p‖ ≤ C) :
    Integrable G ((gaussianProduct v).prod (gaussianProduct v)) :=
  ou_integrable_of_norm_le _ hG.aestronglyMeasurable C 0 (fun p => by simpa using hC p)

/-- **Time derivative of the interpolation** `φ(t) = E[f(x) g(e^{-t}x + √(1-e^{-2t}) x')]`:
for `t > 0`, `φ'(t) = -e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)]`. -/
theorem ou_hasDerivAt_interp (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg Cg' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ Cg)
    (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => ∫ p, f p.1 • g (Real.exp (-τ) • p.1 +
        Real.sqrt (1 - Real.exp (-2 * τ)) • p.2) ∂(gaussianProduct v).prod (gaussianProduct v))
      (-Real.exp (-t) • ∫ p, ouDir v f g p.1 (Real.exp (-t) • p.1 +
        Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
          ∂(gaussianProduct v).prod (gaussianProduct v)) t := by
  set μ := gaussianProduct v
  let c : ℝ → ℝ := fun τ => Real.exp (-τ)
  let s : ℝ → ℝ := fun τ => Real.sqrt (1 - Real.exp (-2 * τ))
  let F : ℝ → (ι → ℝ) × (ι → ℝ) → E := fun τ p => f p.1 • g (c τ • p.1 + s τ • p.2)
  let F' : ℝ → (ι → ℝ) × (ι → ℝ) → E := fun τ p =>
    f p.1 • fderiv ℝ g (c τ • p.1 + s τ • p.2) ((-c τ) • p.1 + (Real.exp (-2 * τ) / s τ) • p.2)
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans (hfC 0)
  have hCg' : 0 ≤ Cg' := (norm_nonneg _).trans (hg'C 0)
  have hFc : ∀ τ, Continuous (F τ) := fun τ =>
    (hfc.comp continuous_fst).smul (hgc.comp (by fun_prop))
  have hF'c : Continuous (F' t) :=
    (hfc.comp continuous_fst).smul ((hg'c.comp (by fun_prop)).clm_apply (by fun_prop))
  set s0 := Real.sqrt (1 - Real.exp (-t)) with hs0def
  have hs0 : 0 < s0 := by
    have := ou_sqrt_pos (t := t / 2) (by linarith)
    rwa [show -2 * (t / 2) = -t by ring] at this
  have hsτ : ∀ τ ∈ Set.Ioi (t / 2), s0 ≤ s τ := fun τ hτ => by
    refine Real.sqrt_le_sqrt ?_
    have : Real.exp (-2 * τ) ≤ Real.exp (-t) :=
      Real.exp_le_exp.mpr (by simp only [Set.mem_Ioi] at hτ; linarith)
    linarith
  have hbound : ∀ᵐ p ∂μ.prod μ, ∀ τ ∈ Set.Ioi (t / 2),
      ‖F' τ p‖ ≤ Cf * Cg' * ((1 + s0⁻¹) * ‖p‖) := Filter.Eventually.of_forall fun p τ hτ => by
    have hτ0 : 0 < τ := by simp only [Set.mem_Ioi] at hτ; linarith
    have hc1 : c τ ≤ 1 := by
      simp only [c]; rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    have hc0 : 0 ≤ c τ := (Real.exp_pos _).le
    have hsp : 0 < s τ := ou_sqrt_pos hτ0
    have he1 : Real.exp (-2 * τ) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    have hq : Real.exp (-2 * τ) / s τ ≤ s0⁻¹ := by
      rw [div_le_iff₀ hsp]
      calc Real.exp (-2 * τ) ≤ 1 := he1
        _ = s0⁻¹ * s0 := (inv_mul_cancel₀ hs0.ne').symm
        _ ≤ s0⁻¹ * s τ := mul_le_mul_of_nonneg_left (hsτ τ hτ) (inv_nonneg.mpr hs0.le)
    have hw : ‖(-c τ) • p.1 + (Real.exp (-2 * τ) / s τ) • p.2‖ ≤ (1 + s0⁻¹) * ‖p‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg hc0,
        abs_of_nonneg (div_nonneg (Real.exp_pos _).le hsp.le)]
      have h1 := norm_fst_le p
      have h2 := norm_snd_le p
      have h3 : c τ * ‖p.1‖ ≤ 1 * ‖p‖ := mul_le_mul hc1 h1 (norm_nonneg _) zero_le_one
      have h4 : Real.exp (-2 * τ) / s τ * ‖p.2‖ ≤ s0⁻¹ * ‖p‖ :=
        mul_le_mul hq h2 (norm_nonneg _) (inv_nonneg.mpr hs0.le)
      linarith
    calc ‖F' τ p‖ = ‖f p.1‖ * ‖fderiv ℝ g (c τ • p.1 + s τ • p.2)
          ((-c τ) • p.1 + (Real.exp (-2 * τ) / s τ) • p.2)‖ := norm_smul _ _
      _ ≤ Cf * (Cg' * ((1 + s0⁻¹) * ‖p‖)) := by
        refine mul_le_mul (hfC _) ?_ (norm_nonneg _) hCf
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        exact mul_le_mul (hg'C _) hw (norm_nonneg _) hCg'
      _ = Cf * Cg' * ((1 + s0⁻¹) * ‖p‖) := by ring
  have hbint : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => Cf * Cg' * ((1 + s0⁻¹) * ‖p‖))
      (μ.prod μ) :=
    (IsGaussian.integrable_id.norm.const_mul _).const_mul _
  have hdiff : ∀ᵐ p ∂μ.prod μ, ∀ τ ∈ Set.Ioi (t / 2),
      HasDerivAt (fun τ => F τ p) (F' τ p) τ := Filter.Eventually.of_forall fun p τ hτ => by
    have hτ0 : 0 < τ := by simp only [Set.mem_Ioi] at hτ; linarith
    have hcd : HasDerivAt c (-c τ) τ :=
      ((hasDerivAt_neg τ).exp).congr_deriv (by simp [c])
    have hY : HasDerivAt (fun τ => c τ • p.1 + s τ • p.2)
        ((-c τ) • p.1 + (Real.exp (-2 * τ) / s τ) • p.2) τ :=
      (hcd.smul_const p.1).add ((ou_hasDerivAt_sqrt hτ0).smul_const p.2)
    exact (((hg.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt τ hY).const_smul
      (f p.1)
  obtain ⟨-, h_der⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.prod μ)
    (F := F) (F' := F') (x₀ := t) (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Filter.Eventually.of_forall fun τ => (hFc τ).aestronglyMeasurable)
    (ou_integrable_bdd v (hFc t) (C := Cf * Cg) (fun p => by
      rw [norm_smul]; exact mul_le_mul (hfC _) (hgC _) (norm_nonneg _) hCf))
    hF'c.aestronglyMeasurable hbound hbint hdiff
  refine h_der.congr_deriv ?_
  -- evaluate the derivative through the rotated identity
  have hst : 0 < s t := ou_sqrt_pos ht
  have hc01 : c t ≤ 1 := by
    simp only [c]; rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hθc : Real.cos (Real.arccos (c t)) = c t :=
    Real.cos_arccos (by linarith [(Real.exp_pos (-t)).le]) hc01
  have hθs : Real.sin (Real.arccos (c t)) = s t := by
    rw [Real.sin_arccos]; simp only [c, s]; rw [ou_exp_sq]
  have hK := ou_rotated_derivative v hf hfC hf'C hg hg'C (Real.arccos (c t))
  rw [hθc, hθs] at hK
  have hpt : ∀ p : (ι → ℝ) × (ι → ℝ), F' t p = (c t / s t) •
      (f p.1 • fderiv ℝ g (c t • p.1 + s t • p.2) (-s t • p.1 + c t • p.2)) := fun p => by
    have e1 : -c t = (c t / s t) * (-s t) := by field_simp
    have e2 : Real.exp (-2 * t) / s t = (c t / s t) * c t := by
      rw [← ou_exp_sq]; simp only [c]; ring
    simp only [F']
    rw [e1, e2, ← smul_smul, ← smul_smul, ← smul_add, map_smul, smul_comm]
  simp_rw [hpt]
  rw [integral_smul, hK, smul_smul]
  congr 1
  field_simp
  rfl

/-- The time kernel `t ↦ E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)]` is continuous on `ℝ`. -/
theorem ou_continuous_kernel (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf' : ℝ}
    (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg' : ℝ} (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    Continuous (fun t : ℝ => ∫ p, ouDir v f g p.1 (Real.exp (-t) • p.1 +
        Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
          ∂(gaussianProduct v).prod (gaussianProduct v)) := by
  have hd := ou_continuous_dir v hf hg
  have h1 : ∀ t : ℝ, Continuous (fun p : (ι → ℝ) × (ι → ℝ) => (p.1, Real.exp (-t) • p.1 +
      Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) := fun t => by fun_prop
  have h2 : ∀ p : (ι → ℝ) × (ι → ℝ), Continuous (fun t : ℝ => (p.1, Real.exp (-t) • p.1 +
      Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) := fun p => by fun_prop
  exact continuous_of_dominated (bound := fun _ => (∑ i, (v i : ℝ)) * Cf' * Cg')
    (fun t => (hd.comp (h1 t)).aestronglyMeasurable)
    (fun t => Filter.Eventually.of_forall fun p => ou_norm_dir_le v hf'C hg'C _ _)
    (integrable_const _) (Filter.Eventually.of_forall fun p => hd.comp (h2 p))

/-- The time kernel is bounded by `(Σᵢ vᵢ) ‖Df‖_∞ ‖Dg‖_∞`. -/
theorem ou_norm_kernel_le (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : (ι → ℝ) → ℂ} {Cf' : ℝ}
    (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    {Cg' : ℝ} (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') (t : ℝ) :
    ‖∫ p, ouDir v f g p.1 (Real.exp (-t) • p.1 +
        Real.sqrt (1 - Real.exp (-2 * t)) • p.2) ∂(gaussianProduct v).prod (gaussianProduct v)‖ ≤
      (∑ i, (v i : ℝ)) * Cf' * Cg' := by
  have h := norm_integral_le_of_norm_le_const (μ := (gaussianProduct v).prod (gaussianProduct v))
    (Filter.Eventually.of_forall fun p => ou_norm_dir_le v hf'C hg'C p.1
      (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2))
  simpa using h

/-- Integrability of `t ↦ e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)]` on `(0, ∞)`. -/
theorem ou_integrableOn_kernel (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf' : ℝ}
    (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg' : ℝ} (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    IntegrableOn (fun t : ℝ => Real.exp (-t) • ∫ p, ∑ i,
        (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ g (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v))
      (Set.Ioi 0) := by
  have hc := ou_continuous_kernel v hf hf'C hg hg'C
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul
    ((∑ i, (v i : ℝ)) * Cf' * Cg')) ((Real.continuous_exp.comp continuous_neg).smul
      hc).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_one_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (ou_norm_kernel_le v hf'C hg'C t) (Real.exp_pos _).le

/-- **Bilinear Ornstein–Uhlenbeck covariance identity** (the trace–matrix lemma),
vector-valued form: for `μ = gaussianProduct v`, `f : (ι → ℝ) → ℂ` and `g : (ι → ℝ) → E`
`C¹`, bounded, with bounded derivative,
`E[f g] - E f • E g = ∫₀^∞ e^{-t} E_{μ⊗μ}[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(e^{-t}x + √(1-e^{-2t}) x')] dt`.
No conjugation; no hypothesis on `v`. -/
theorem ou_covariance_smul (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg Cg' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ Cg)
    (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    (∫ x, f x • g x ∂gaussianProduct v) -
        (∫ x, f x ∂gaussianProduct v) • (∫ x, g x ∂gaussianProduct v) =
      ∫ t in Set.Ioi 0, Real.exp (-t) • ∫ p, ∑ i,
        (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ g (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v) := by
  set μ := gaussianProduct v
  let Ψ : ℝ → E := fun τ => ∫ p, f p.1 • g (Real.exp (-τ) • p.1 +
    Real.sqrt (1 - Real.exp (-2 * τ)) • p.2) ∂μ.prod μ
  let G : ℝ → E := fun τ => ∫ p, ouDir v f g p.1 (Real.exp (-τ) • p.1 +
    Real.sqrt (1 - Real.exp (-2 * τ)) • p.2) ∂μ.prod μ
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans (hfC 0)
  have hfg : ∀ x y, ‖f x • g y‖ ≤ Cf * Cg := fun x y => by
    rw [norm_smul]; exact mul_le_mul (hfC _) (hgC _) (norm_nonneg _) hCf
  have hΨc : Continuous Ψ :=
    continuous_of_dominated (bound := fun _ => Cf * Cg)
      (fun τ => ((hfc.comp continuous_fst).smul (hgc.comp (by fun_prop))).aestronglyMeasurable)
      (fun τ => Filter.Eventually.of_forall fun p => hfg _ _) (integrable_const _)
      (Filter.Eventually.of_forall fun p => (hfc.comp continuous_const).smul
        (hgc.comp (by fun_prop)))
  have hΨ0 : Ψ 0 = ∫ x, f x • g x ∂μ := by
    simp only [Ψ, neg_zero, Real.exp_zero, mul_zero, sub_self, Real.sqrt_zero, one_smul,
      zero_smul, add_zero]
    rw [integral_fun_fst (fun x => f x • g x)]
    simp
  have hlim : Filter.Tendsto Ψ Filter.atTop (nhds ((∫ x, f x ∂μ) • (∫ x, g x ∂μ))) := by
    rw [← integral_prod_smul]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Cf * Cg)
      (Filter.Eventually.of_forall fun τ =>
        ((hfc.comp continuous_fst).smul (hgc.comp (by fun_prop))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun τ => Filter.Eventually.of_forall fun p => hfg _ _)
      (integrable_const _) (Filter.Eventually.of_forall fun p => ?_)
    have hc : Filter.Tendsto (fun τ : ℝ => Real.exp (-τ)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have he : Filter.Tendsto (fun τ : ℝ => Real.exp (-2 * τ)) Filter.atTop (nhds 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
      refine this.congr fun τ => ?_
      simp [neg_mul]
    have hs : Filter.Tendsto (fun τ : ℝ => Real.sqrt (1 - Real.exp (-2 * τ))) Filter.atTop
        (nhds 1) := by
      have := ((Real.continuous_sqrt.tendsto (1 - 0)).comp (he.const_sub 1))
      simpa [Function.comp_def] using this
    have hY : Filter.Tendsto (fun τ : ℝ => Real.exp (-τ) • p.1 +
        Real.sqrt (1 - Real.exp (-2 * τ)) • p.2) Filter.atTop (nhds p.2) := by
      have := (hc.smul_const p.1).add (hs.smul_const p.2)
      simpa using this
    exact ((hgc.tendsto _).comp hY).const_smul (f p.1)
  have hint : IntegrableOn (fun τ => -Real.exp (-τ) • G τ) (Set.Ioi 0) := by
    simp_rw [neg_smul]
    exact (ou_integrableOn_kernel v hf hf'C hg hg'C).neg
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hΨc.continuousWithinAt
    (fun τ hτ => ou_hasDerivAt_interp v hf hfC hf'C hg hgC hg'C hτ) hint hlim
  rw [hΨ0] at hmain
  simp_rw [neg_smul] at hmain
  rw [integral_neg] at hmain
  change _ = ∫ t in Set.Ioi 0, Real.exp (-t) • G t
  rw [← neg_sub, ← hmain, neg_neg]

/-- **Bilinear Ornstein–Uhlenbeck covariance identity**, complex scalar form (the trace–matrix
lemma): `Cov(f, g) = ∫₀^∞ e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)] dt` over `μ ⊗ μ`,
`x_t = e^{-t}x + √(1-e^{-2t}) x'`, bilinear (no conjugation). -/
theorem ou_covariance (v : ι → ℝ≥0) {f g : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) {Cf Cf' Cg Cg' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf')
    (hgC : ∀ x, ‖g x‖ ≤ Cg) (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    (∫ x, f x * g x ∂gaussianProduct v) -
        (∫ x, f x ∂gaussianProduct v) * (∫ x, g x ∂gaussianProduct v) =
      ∫ t in Set.Ioi 0, (Real.exp (-t) : ℂ) * ∫ p, ∑ i,
        ((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1) *
          fderiv ℝ g (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v) := by
  have h := ou_covariance_smul v hf hfC hf'C hg hgC hg'C
  simpa only [smul_eq_mul, Complex.real_smul] using h

/-- Norm form of the covariance identity:
`‖E[f g] - E f • E g‖ ≤ ∫₀^∞ e^{-t} ‖E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)]‖ dt`. -/
theorem ou_covariance_norm_le (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg Cg' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ Cg)
    (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    ‖(∫ x, f x • g x ∂gaussianProduct v) -
        (∫ x, f x ∂gaussianProduct v) • (∫ x, g x ∂gaussianProduct v)‖ ≤
      ∫ t in Set.Ioi 0, Real.exp (-t) * ‖∫ p, ∑ i,
        (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ g (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v)‖ := by
  rw [ou_covariance_smul v hf hfC hf'C hg hgC hg'C]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Uniform bound: `‖E[f g] - E f • E g‖ ≤ (Σᵢ vᵢ) ‖Df‖_∞ ‖Dg‖_∞`. -/
theorem ou_covariance_norm_le_const (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg Cg' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ Cg)
    (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    ‖(∫ x, f x • g x ∂gaussianProduct v) -
        (∫ x, f x ∂gaussianProduct v) • (∫ x, g x ∂gaussianProduct v)‖ ≤
      (∑ i, (v i : ℝ)) * Cf' * Cg' := by
  rw [ou_covariance_smul v hf hfC hf'C hg hgC hg'C]
  refine (norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi 0).const_mul
    ((∑ i, (v i : ℝ)) * Cf' * Cg')) (Filter.Eventually.of_forall fun t => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (ou_norm_kernel_le v hf'C hg'C t) (Real.exp_pos _).le
  · rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

/-- Integrability of the complex time integrand of `ou_covariance` on `(0, ∞)`. -/
theorem ou_integrableOn_kernel_complex (v : ι → ℝ≥0) {f g : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {Cf' Cg' : ℝ}
    (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) : ℂ) * ∫ p, ∑ i,
        ((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1) *
          fderiv ℝ g (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v))
      (Set.Ioi 0) := by
  have h := ou_integrableOn_kernel v hf hf'C hg hg'C
  simpa only [smul_eq_mul, Complex.real_smul] using h

open scoped Matrix.Norms.L2Operator in
/-- Matrix-valued covariance identity (Euclidean operator norm on `Matrix κ κ' ℂ`, the
convention of `Inputs`): `E[f G] - E f • E G = ∫₀^∞ e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) • ∂ᵢ G(x_t)] dt`. -/
theorem ou_covariance_matrix (v : ι → ℝ≥0) {κ κ' : Type*} [Fintype κ] [Fintype κ']
    [DecidableEq κ'] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf')
    {G : (ι → ℝ) → Matrix κ κ' ℂ} (hG : ContDiff ℝ 1 G) {CG CG' : ℝ}
    (hGC : ∀ x, ‖G x‖ ≤ CG) (hG'C : ∀ x, ‖fderiv ℝ G x‖ ≤ CG') :
    (∫ x, f x • G x ∂gaussianProduct v) -
        (∫ x, f x ∂gaussianProduct v) • (∫ x, G x ∂gaussianProduct v) =
      ∫ t in Set.Ioi 0, Real.exp (-t) • ∫ p, ∑ i,
        (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ G (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v) :=
  ou_covariance_smul v hf hfC hf'C hG hGC hG'C

end BlockBand.Layers
