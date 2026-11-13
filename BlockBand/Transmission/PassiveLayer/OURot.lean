module

public import BlockBand.Transmission.PassiveLayer.OUIbp

/-!
# Bilinear Ornstein–Uhlenbeck covariance identity, part 2: the rotated derivative identity

`ouDir v f g x y = Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(y)` (bilinear, no conjugation) and
`ou_rotated_derivative`: with `(Y, Z) = R_θ(X, X')`,
`E[f(X) Dg(Y) Z] = -sin θ · E[ouDir f g X Y]` under `μ ⊗ μ`, `μ = gaussianProduct v`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory ProbabilityTheory BlockBand.Internal.Contracts.Inputs
open scoped NNReal

variable {ι : Type} [Fintype ι] [DecidableEq ι]

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

end BlockBand.Transmission.PassiveLayer
