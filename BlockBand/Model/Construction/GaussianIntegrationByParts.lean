module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian integration by parts without boundary assumptions

Real one-dimensional Gaussian integration by parts `E[(X - μ) f(X)] = v E[f'(X)]` for everywhere
differentiable, vector-valued `f` under integrability hypotheses only, including the degenerate
variance-zero case.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Exact derivative of the nondegenerate Gaussian density, with mean and
variance normalization preserved. -/
theorem hasDerivAt_gaussianDensity (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v)
      (-((x - μ) / (v : ℝ)) * gaussianPDFReal μ v x) x := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  let c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  have hinner : HasDerivAt
      (fun y : ℝ => -(y - μ) ^ 2 / (2 * (v : ℝ)))
      (-((x - μ) / (v : ℝ))) x := by
    convert ((((hasDerivAt_id x).sub_const μ).pow 2).neg).div_const
      (2 * (v : ℝ)) using 1
    · funext y
      simp [id_eq]
    · simp [id_eq]
      field_simp
  have h := (hasDerivAt_const x c).mul ((Real.hasDerivAt_exp _).comp x hinner)
  convert h using 1
  · funext y
    simp [gaussianPDFReal, c]
  · simp [gaussianPDFReal, c]
    ring

/-- The Gaussian integrability hypothesis is exactly density-weighted
Lebesgue integrability in every normed real target. -/
theorem integrable_gaussian_iff_density {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ → E) :
    Integrable f (gaussianReal μ v) ↔
      Integrable (fun x => gaussianPDFReal μ v x • f x) := by
  rw [gaussianReal_of_var_ne_zero μ hv]
  simpa only [toReal_gaussianPDF] using
    (integrable_withDensity_iff_integrable_smul'
      (μ := volume) (g := f) (measurable_gaussianPDF μ v)
      (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top))

/-- Real-coordinate Gaussian integration by parts for everywhere differentiable
functions under precisely the three integrability hypotheses. The degenerate
variance-zero case is included. This is the differentiable, vector-valued
form; the locally weak form is proved separately. -/
theorem gaussian_integration_by_parts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : ℝ) (v : ℝ≥0) {f f' : ℝ → E}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal μ v))
    (hf' : Integrable f' (gaussianReal μ v))
    (hcoord : Integrable (fun x => (x - μ) • f x) (gaussianReal μ v)) :
    (∫ x, (x - μ) • f x ∂gaussianReal μ v) =
      (v : ℝ) • (∫ x, f' x ∂gaussianReal μ v) := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hF := (integrable_gaussian_iff_density μ v hv f).mp hf
  have hD := (integrable_gaussian_iff_density μ v hv f').mp hf'
  have hC := (integrable_gaussian_iff_density μ v hv
    (fun x => (x - μ) • f x)).mp hcoord
  let G : ℝ → E := fun x => gaussianPDFReal μ v x • f x
  let D : ℝ → E := fun x => gaussianPDFReal μ v x • f' x -
    (v : ℝ)⁻¹ • (gaussianPDFReal μ v x • ((x - μ) • f x))
  have hGD (x : ℝ) : HasDerivAt G (D x) x := by
    have h := (hasDerivAt_gaussianDensity μ v hv x).smul (hderiv x)
    convert h using 1
    dsimp [D]
    simp only [sub_eq_add_neg, smul_smul, div_eq_mul_inv]
    module
  have hV : Integrable (fun x => (v : ℝ)⁻¹ •
      (gaussianPDFReal μ v x • ((x - μ) • f x))) := by
    exact Integrable.fun_smul (v : ℝ)⁻¹ hC
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hGD
    (hD.sub hV) hF
  change (∫ x, gaussianPDFReal μ v x • f' x -
    (v : ℝ)⁻¹ • (gaussianPDFReal μ v x • ((x - μ) • f x))) = 0 at hzero
  rw [integral_sub hD hV, integral_smul] at hzero
  rw [← integral_gaussianReal_eq_integral_smul hv,
    ← integral_gaussianReal_eq_integral_smul hv] at hzero
  have heq := congrArg (fun z : E => (v : ℝ) • z) hzero
  simp only [smul_sub, smul_smul, mul_inv_cancel₀ hvR, one_smul, smul_zero] at heq
  exact (sub_eq_zero.mp heq).symm

/-- Centred real Gaussian scalar normalization `E[X f(X)] = v E[f'(X)]`. -/
theorem centered_gaussian_integration_by_parts (v : ℝ≥0) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 v))
    (hf' : Integrable f' (gaussianReal 0 v))
    (hcoord : Integrable (fun x => x * f x) (gaussianReal 0 v)) :
    (∫ x, x * f x ∂gaussianReal 0 v) = (v : ℝ) * ∫ x, f' x ∂gaussianReal 0 v := by
  simpa only [sub_zero, smul_eq_mul] using
    gaussian_integration_by_parts 0 v hderiv hf hf'
      (by simpa only [sub_zero, smul_eq_mul] using hcoord)

end BlockBand.Model.Construction
