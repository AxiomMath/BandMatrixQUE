module

public import BlockBand.Model.Construction.GaussianSmoothCutoff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Distributional weak Gaussian integration by parts on the real line

Gaussian integration by parts `E[(X - μ) f(X)] = v E[f'(X)]` for functions with a distributional
weak derivative, under integrability hypotheses only, via the smooth cutoffs of
`gaussianSmoothCutoff`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ContDiff

/-- Standard distributional real weak derivative: local integrability and
integration against every smooth compactly supported real scalar test.
The target may be a complete real normed vector space. -/
def HasRealWeakDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) : Prop :=
  LocallyIntegrable f volume ∧ LocallyIntegrable g volume ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, deriv φ x • f x) = -(∫ x, φ x • g x)

/-- Every Gaussian density is smooth as a real function. -/
theorem contDiff_gaussianDensity (μ : ℝ) (v : ℝ≥0) :
    ContDiff ℝ ∞ (gaussianPDFReal μ v) := by
  unfold gaussianPDFReal
  fun_prop

/-- The standard distributional weak derivative suffices for Gaussian
integration by parts under exactly the three integrability assumptions. The scalar coordinate
variance normalization is `v`, including the degenerate zero-variance law. -/
theorem gaussian_weak_integration_by_parts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : ℝ) (v : ℝ≥0) {f f' : ℝ → E}
    (hweak : HasRealWeakDerivative f f')
    (hf : Integrable f (gaussianReal μ v))
    (hf' : Integrable f' (gaussianReal μ v))
    (hcoord : Integrable (fun x => (x - μ) • f x) (gaussianReal μ v)) :
    (∫ x, (x - μ) • f x ∂gaussianReal μ v) =
      (v : ℝ) • (∫ x, f' x ∂gaussianReal μ v) := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  let F : ℝ → E := fun x => gaussianPDFReal μ v x • f x
  let D : ℝ → E := fun x => gaussianPDFReal μ v x • f' x
  let C : ℝ → E := fun x => gaussianPDFReal μ v x • ((x - μ) • f x)
  have hF : Integrable F := (integrable_gaussian_iff_density μ v hv f).mp hf
  have hD : Integrable D := (integrable_gaussian_iff_density μ v hv f').mp hf'
  have hC : Integrable C := (integrable_gaussian_iff_density μ v hv _).mp hcoord
  have hcint (g : ℝ → E) (hg : Integrable g) (n : ℕ) :
      Integrable (fun x => gaussianSmoothCutoff n x • g x) := by
    apply hg.norm.mono'
      ((gaussianSmoothCutoff n).continuous.aestronglyMeasurable.smul hg.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      change ‖gaussianSmoothCutoff n x • g x‖ ≤ ‖g x‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gaussianSmoothCutoff n).nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) (gaussianSmoothCutoff n).le_one
  obtain ⟨B, hB0, hB⟩ := exists_bound_deriv_gaussianSmoothCutoff
  have hdint (n : ℕ) : Integrable (fun x => deriv (gaussianSmoothCutoff n) x • F x) := by
    have hd : Continuous (deriv (gaussianSmoothCutoff n)) :=
      (show ContDiff ℝ 1 (gaussianSmoothCutoff n) from (gaussianSmoothCutoff n).contDiff).continuous_deriv le_rfl
    apply (hF.norm.const_mul B).mono' (hd.aestronglyMeasurable.smul hF.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      change ‖deriv (gaussianSmoothCutoff n) x • F x‖ ≤ B * ‖F x‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hB n x) (norm_nonneg _)
  have heq (n : ℕ) :
      -((v : ℝ)⁻¹) • (∫ x, gaussianSmoothCutoff n x • C x) +
        (∫ x, deriv (gaussianSmoothCutoff n) x • F x) =
      -(∫ x, gaussianSmoothCutoff n x • D x) := by
    let φ : ℝ → ℝ := fun x => gaussianPDFReal μ v x * gaussianSmoothCutoff n x
    have hφ : ContDiff ℝ ∞ φ :=
      (contDiff_gaussianDensity μ v).mul (gaussianSmoothCutoff n).contDiff
    have hφsupport : HasCompactSupport φ :=
      (gaussianSmoothCutoff n).hasCompactSupport.mul_left
    have hdφ (x : ℝ) : deriv φ x =
        (-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x) * gaussianSmoothCutoff n x +
          gaussianPDFReal μ v x * deriv (gaussianSmoothCutoff n) x := by
      exact ((hasDerivAt_gaussianDensity μ v hv x).mul
        (((show ContDiff ℝ 1 (gaussianSmoothCutoff n) from
          (gaussianSmoothCutoff n).contDiff).differentiable (by norm_num) x).hasDerivAt)).deriv
    have htest := hweak.2.2 φ hφ hφsupport
    have hleft (x : ℝ) : deriv φ x • f x =
        -((v : ℝ)⁻¹) • (gaussianSmoothCutoff n x • C x) +
          deriv (gaussianSmoothCutoff n) x • F x := by
      rw [hdφ]
      dsimp [C, F]
      simp only [add_smul, smul_smul, div_eq_mul_inv]
      module
    have hright (x : ℝ) : φ x • f' x = gaussianSmoothCutoff n x • D x := by
      dsimp [φ, D]
      simp only [smul_smul]
      rw [mul_comm]
    simp_rw [hleft, hright] at htest
    have hs : Integrable (fun x => -((v : ℝ)⁻¹) • (gaussianSmoothCutoff n x • C x)) :=
      Integrable.fun_smul _ (hcint C hC n)
    rw [integral_add hs (hdint n), integral_smul] at htest
    exact htest
  have hL := ((integral_gaussianSmoothCutoff_tendsto volume hC).const_smul
      (-((v : ℝ)⁻¹))).add (integral_deriv_gaussianSmoothCutoff_tendsto volume hF)
  have hR := (integral_gaussianSmoothCutoff_tendsto volume hD).neg
  have hR' : Tendsto (fun n : ℕ =>
      -((v : ℝ)⁻¹) • (∫ x, gaussianSmoothCutoff n x • C x) +
        (∫ x, deriv (gaussianSmoothCutoff n) x • F x)) atTop (𝓝 (-(∫ x, D x))) := by
    exact hR.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
  have h := tendsto_nhds_unique hL hR'
  have h' : (v : ℝ)⁻¹ • (∫ x, C x) = ∫ x, D x := by
    apply neg_inj.mp
    simpa only [add_zero, neg_smul] using h
  have hscaled := congrArg (fun z : E => (v : ℝ) • z) h'
  simp only [smul_smul, mul_inv_cancel₀ hvR, one_smul] at hscaled
  rw [integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv]
  exact hscaled

end BlockBand.Model.Construction
