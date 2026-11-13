module

public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Model.Construction.GaussianIntegrationByParts

/-!
# Bilinear Ornstein–Uhlenbeck covariance identity, part 1: Gaussian integration by parts

The Gaussian interpolation step in the proof of the trace-matrix lemma: in real Gaussian
coordinates `x`, let `x_t = e^{-t}x + √(1−e^{-2t}) x'` with `x'` independent. Differentiation of
this interpolation gives the bilinear covariance identity
`Cov(f(x),U(x)) = ∫_0^∞ e^{-t} E[∇f(x)·Σ∇U(x_t)] dt`. Here `Σ` is the real-coordinate
covariance, and no conjugation is inserted in this bilinear identity. The development is split
in three files (`OUIbp`, `OURot`, `OUCov`).

Law: `μ = gaussianProduct v` on `ι → ℝ` (finite `ι`, any variances `v : ι → ℝ≥0`; zero
variances are allowed), `x, x'` independent, i.e. the law `μ ⊗ μ`. Partial derivatives are
the Fréchet partials `∂ᵢ f(x) = Df(x) eᵢ`, `eᵢ = Pi.single i 1`, as in
`Inputs.weightedGradientNorm`. Class: `f : (ι → ℝ) → ℂ` and `g : (ι → ℝ) → E` (`E` any complete
normed `ℂ`-space, e.g. `ℂ` or matrices) are `C¹`, bounded, with bounded derivative; no
second derivative is used (weaker than a `C²` class).

Proof: `φ(t) = E[f(x) • g(x_t)]`; `φ(0) = E[f g]`, `φ(∞) = E f • E g` (dominated convergence);
for `t > 0`, `φ'(t) = (e^{-t}/s_t) E[f(X) Dg(Y) Z]` with `(Y, Z) = R_θ(X, X')`,
`cos θ = e^{-t}`, `sin θ = s_t = √(1-e^{-2t})`. Rotation invariance of `μ ⊗ μ`
(Mathlib `IsGaussian.map_rotation_eq_self`) and one Gaussian integration by parts in the
rotated coordinate give `φ'(t) = -e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)]`; then
`integral_Ioi_of_hasDerivAt_of_tendsto`. The multivariate integration by parts `ou_ibp` is
proved here from the one-dimensional `gaussian_integration_by_parts` and the coordinate
splitting `ou_map_update`; the hypothesis `MultivariateGaussianIBP` is not used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Transmission.PassiveLayer

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

end BlockBand.Transmission.PassiveLayer
