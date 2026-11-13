module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Circular Gaussian moments

This file formalizes the moment part of the Gaussian identities lemma (the Wick
formula).  The normalization is that a standard circular complex Gaussian has independent real and imaginary
parts of variance `1/2`, hence total second moment one.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory ProbabilityTheory

namespace BlockBand.Counting

/-- The centered real Gaussian fourth moment, in the normalization used to
construct a circular complex Gaussian. -/
theorem integral_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  calc
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v =
        iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 := by
      rw [iteratedDeriv_mgf_zero] <;> simp
    _ = iteratedDeriv 4 (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2)) 0 := by
      rw [mgf_fun_id_gaussianReal]
      simp
    _ = 3 * (v : ℝ) ^ 2 := by
      let f : ℝ → ℝ := fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)
      let f₁ : ℝ → ℝ := fun t => (v : ℝ) * t * f t
      let f₂ : ℝ → ℝ := fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t
      let f₃ : ℝ → ℝ := fun t =>
        (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t
      let f₄ : ℝ → ℝ := fun t =>
        (3 * (v : ℝ) ^ 2 + 6 * (v : ℝ) ^ 3 * t ^ 2 +
          (v : ℝ) ^ 4 * t ^ 4) * f t
      have hfd : Differentiable ℝ f := by
        dsimp [f]
        fun_prop
      have hf : deriv f = f₁ := by
        ext t
        dsimp [f, f₁]
        rw [_root_.deriv_exp (by fun_prop)]
        simp [deriv_div_const, deriv_fun_mul, deriv_fun_pow, deriv_id'']
        ring
      have hf₁ : deriv f₁ = f₂ := by
        ext t
        dsimp [f₁, f₂]
        rw [deriv_fun_mul (by fun_prop) hfd.differentiableAt, hf]
        dsimp [f₁]
        simp
        ring
      have hf₂ : deriv f₂ = f₃ := by
        ext t
        dsimp [f₂, f₃]
        rw [deriv_fun_mul (by fun_prop) hfd.differentiableAt, hf]
        dsimp [f₁]
        simp [deriv_const', deriv_fun_mul, deriv_fun_pow, deriv_id'']
        ring
      have hf₃ : deriv f₃ = f₄ := by
        ext t
        dsimp [f₃, f₄]
        rw [deriv_fun_mul (by fun_prop) hfd.differentiableAt, hf]
        dsimp [f₁]
        change (deriv ((fun u : ℝ => 3 * (v : ℝ) ^ 2 * u) +
          (fun u : ℝ => (v : ℝ) ^ 3 * u ^ 3)) t) * f t + _ = _
        rw [deriv_add (by fun_prop) (by fun_prop)]
        simp [deriv_fun_mul, deriv_fun_pow, deriv_id'']
        ring
      change iteratedDeriv 4 f 0 = _
      simp [iteratedDeriv_succ, hf, hf₁, hf₂, hf₃, f₄, f]

/-- The real component law of a standard circular Gaussian: centered Gaussian
with variance `1/2`. -/
def standardCircularReal : Measure ℝ := gaussianReal 0 (1 / 2 : ℝ≥0)

/-- The explicit product law on real and imaginary components. -/
def standardCircularGaussian : Measure (ℝ × ℝ) :=
  standardCircularReal.prod standardCircularReal

instance : IsProbabilityMeasure standardCircularReal := by
  unfold standardCircularReal
  infer_instance

instance : IsProbabilityMeasure standardCircularGaussian := by
  unfold standardCircularGaussian
  infer_instance

/-- The complex coordinate on the product sample space. -/
def circularGaussianCoordinate (z : ℝ × ℝ) : ℂ := (z.1 : ℂ) + Complex.I * z.2

/-- A centered real Gaussian's second moment is its variance. -/
theorem integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  rw [← variance_id_gaussianReal (μ := 0) (v := v)]
  rw [variance_eq_integral (by fun_prop)]
  simp [integral_id_gaussianReal]

/-- Each real component of the standard circular law has second moment `1/2`. -/
theorem integral_sq_standardCircularReal :
    ∫ x : ℝ, x ^ 2 ∂standardCircularReal = 1 / 2 := by
  simpa [standardCircularReal] using integral_sq_gaussianReal (1 / 2 : ℝ≥0)

/-- Each real component of the standard circular law has fourth moment `3/4`. -/
theorem integral_pow_four_standardCircularReal :
    ∫ x : ℝ, x ^ 4 ∂standardCircularReal = 3 / 4 := by
  convert integral_pow_four_gaussianReal (1 / 2 : ℝ≥0) using 1 <;>
    norm_num [standardCircularReal]

/-- Squaring a real component remains integrable under the standard component law. -/
theorem integrable_sq_standardCircularReal :
    Integrable (fun x : ℝ => x ^ 2) standardCircularReal := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (2 : ℝ≥0)).integrable_norm_pow
    (p := 2) (by norm_num)
  simpa [standardCircularReal, Real.norm_eq_abs, sq_abs] using h

/-- Taking the fourth power of a real component remains integrable. -/
theorem integrable_pow_four_standardCircularReal :
    Integrable (fun x : ℝ => x ^ 4) standardCircularReal := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (4 : ℝ≥0)).integrable_norm_pow
    (p := 4) (by norm_num)
  unfold standardCircularReal
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  change |x| ^ 4 = x ^ 4
  rw [← abs_pow, abs_of_nonneg (by positivity)]

/-- The explicit circular product law has total second moment one. -/
theorem integral_circular_normSq :
    ∫ z : ℝ × ℝ, (z.1 ^ 2 + z.2 ^ 2) ∂standardCircularGaussian = 1 := by
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) standardCircularReal := integrable_const 1
  have hx : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) standardCircularGaussian := by
    simpa [standardCircularGaussian] using integrable_sq_standardCircularReal.smul_prod h1
  have hy : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) standardCircularGaussian := by
    simpa [standardCircularGaussian] using h1.smul_prod integrable_sq_standardCircularReal
  rw [integral_add hx hy]
  unfold standardCircularGaussian
  have ex : (∫ z : ℝ × ℝ, z.1 ^ 2 ∂standardCircularReal.prod standardCircularReal) =
      (∫ x : ℝ, x ^ 2 ∂standardCircularReal) * ∫ _ : ℝ, (1 : ℝ) ∂standardCircularReal := by
    simpa using integral_prod_mul (μ := standardCircularReal) (ν := standardCircularReal)
      (fun x : ℝ => x ^ 2) (fun _ : ℝ => (1 : ℝ))
  have ey : (∫ z : ℝ × ℝ, z.2 ^ 2 ∂standardCircularReal.prod standardCircularReal) =
      (∫ _ : ℝ, (1 : ℝ) ∂standardCircularReal) * ∫ y : ℝ, y ^ 2 ∂standardCircularReal := by
    simpa using integral_prod_mul (μ := standardCircularReal) (ν := standardCircularReal)
      (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y ^ 2)
  rw [ex, ey]
  simp [integral_sq_standardCircularReal]
  norm_num

/-- The explicit circular product law has fourth modulus moment two:
`E |Z|⁴ = 2`. -/
theorem integral_circular_normSq_sq :
    ∫ z : ℝ × ℝ, (z.1 ^ 2 + z.2 ^ 2) ^ 2 ∂standardCircularGaussian = 2 := by
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) standardCircularReal := integrable_const 1
  have hx4 : Integrable (fun z : ℝ × ℝ => z.1 ^ 4) standardCircularGaussian := by
    simpa [standardCircularGaussian] using integrable_pow_four_standardCircularReal.smul_prod h1
  have hy4 : Integrable (fun z : ℝ × ℝ => z.2 ^ 4) standardCircularGaussian := by
    simpa [standardCircularGaussian] using h1.smul_prod integrable_pow_four_standardCircularReal
  have hxy : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 * z.2 ^ 2)
      standardCircularGaussian := by
    simpa [standardCircularGaussian] using
      integrable_sq_standardCircularReal.smul_prod integrable_sq_standardCircularReal
  rw [show (fun z : ℝ × ℝ => (z.1 ^ 2 + z.2 ^ 2) ^ 2) =
      (fun z : ℝ × ℝ => z.1 ^ 4 + 2 * (z.1 ^ 2 * z.2 ^ 2) + z.2 ^ 4) by
        funext z
        ring]
  change ∫ z : ℝ × ℝ,
      ((((fun z : ℝ × ℝ => z.1 ^ 4) +
        (fun z : ℝ × ℝ => (2 : ℝ) * (z.1 ^ 2 * z.2 ^ 2))) +
        (fun z : ℝ × ℝ => z.2 ^ 4)) z) ∂standardCircularGaussian = (2 : ℝ)
  rw [integral_add' (hx4.add (hxy.const_mul 2)) hy4,
    integral_add' hx4 (hxy.const_mul 2), integral_const_mul]
  unfold standardCircularGaussian
  have ex4 : (∫ z : ℝ × ℝ, z.1 ^ 4 ∂standardCircularReal.prod standardCircularReal) =
      (∫ x : ℝ, x ^ 4 ∂standardCircularReal) * ∫ _ : ℝ, (1 : ℝ) ∂standardCircularReal := by
    simpa using integral_prod_mul (μ := standardCircularReal) (ν := standardCircularReal)
      (fun x : ℝ => x ^ 4) (fun _ : ℝ => (1 : ℝ))
  have exy : (∫ z : ℝ × ℝ, z.1 ^ 2 * z.2 ^ 2
      ∂standardCircularReal.prod standardCircularReal) =
      (∫ x : ℝ, x ^ 2 ∂standardCircularReal) *
        ∫ y : ℝ, y ^ 2 ∂standardCircularReal := by
    exact integral_prod_mul (fun x : ℝ => x ^ 2) (fun y : ℝ => y ^ 2)
  have ey4 : (∫ z : ℝ × ℝ, z.2 ^ 4 ∂standardCircularReal.prod standardCircularReal) =
      (∫ _ : ℝ, (1 : ℝ) ∂standardCircularReal) * ∫ y : ℝ, y ^ 4 ∂standardCircularReal := by
    simpa using integral_prod_mul (μ := standardCircularReal) (ν := standardCircularReal)
      (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y ^ 4)
  rw [ex4, exy, ey4]
  simp [integral_sq_standardCircularReal, integral_pow_four_standardCircularReal]
  norm_num

/-- The squared modulus of the explicit circular coordinate is `x²+y²`. -/
theorem conj_mul_circularGaussianCoordinate (z : ℝ × ℝ) :
    conj (circularGaussianCoordinate z) * circularGaussianCoordinate z =
      ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [circularGaussianCoordinate] <;> norm_cast <;> ring

/-- In complex notation, the explicit standard circular coordinate satisfies
`E[conj Z · Z] = 1`. -/
theorem integral_conj_mul_circularGaussianCoordinate :
    ∫ z : ℝ × ℝ, conj (circularGaussianCoordinate z) * circularGaussianCoordinate z
      ∂standardCircularGaussian = 1 := by
  simp_rw [conj_mul_circularGaussianCoordinate]
  calc
    _ = ((∫ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 ∂standardCircularGaussian : ℝ) : ℂ) :=
      integral_ofReal
    _ = 1 := by rw [integral_circular_normSq]; norm_num

/-- In complex notation, the explicit standard circular coordinate satisfies
`E[(conj Z · Z)²] = 2`. -/
theorem integral_conj_mul_circularGaussianCoordinate_sq :
    ∫ z : ℝ × ℝ,
      (conj (circularGaussianCoordinate z) * circularGaussianCoordinate z) ^ 2
      ∂standardCircularGaussian = 2 := by
  simp_rw [conj_mul_circularGaussianCoordinate, ← Complex.ofReal_pow]
  calc
    _ = ((∫ z : ℝ × ℝ, (z.1 ^ 2 + z.2 ^ 2) ^ 2
        ∂standardCircularGaussian : ℝ) : ℂ) := integral_ofReal
    _ = 2 := by rw [integral_circular_normSq_sq]; norm_num

/-- Integrability of the circular squared modulus. -/
theorem integrable_circular_normSq :
    Integrable (fun z : ℝ × ℝ => z.1 ^ 2 + z.2 ^ 2) standardCircularGaussian := by
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) standardCircularReal := integrable_const 1
  have hx : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) standardCircularGaussian := by
    simpa [standardCircularGaussian] using integrable_sq_standardCircularReal.smul_prod h1
  have hy : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) standardCircularGaussian := by
    simpa [standardCircularGaussian] using h1.smul_prod integrable_sq_standardCircularReal
  exact hx.add hy

/-- Integrability of the circular fourth modulus moment. -/
theorem integrable_circular_normSq_sq :
    Integrable (fun z : ℝ × ℝ => (z.1 ^ 2 + z.2 ^ 2) ^ 2)
      standardCircularGaussian := by
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) standardCircularReal := integrable_const 1
  have hx : Integrable (fun z : ℝ × ℝ => z.1 ^ 4) standardCircularGaussian := by
    simpa [standardCircularGaussian] using integrable_pow_four_standardCircularReal.smul_prod h1
  have hy : Integrable (fun z : ℝ × ℝ => z.2 ^ 4) standardCircularGaussian := by
    simpa [standardCircularGaussian] using h1.smul_prod integrable_pow_four_standardCircularReal
  have hxy : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 * z.2 ^ 2)
      standardCircularGaussian := by
    simpa [standardCircularGaussian] using
      integrable_sq_standardCircularReal.smul_prod integrable_sq_standardCircularReal
  convert (hx.add (hxy.const_mul 2)).add hy using 1
  funext z
  simp only [Pi.add_apply]
  ring

/-- The standard complex Gaussian quadratic form for a scalar matrix.
The law is the product of two centered reals of variance one half; no moment
identity is assumed. -/
theorem integral_scalarQuadratic (a : ℂ) :
    (∫ z, a * (conj (circularGaussianCoordinate z) * circularGaussianCoordinate z)
      ∂standardCircularGaussian) = a := by
  rw [integral_const_mul, integral_conj_mul_circularGaussianCoordinate, mul_one]

/-- Exact second quadratic moment in complex dimension one.
This is the case `d = 1` of the Wick formula for arbitrary complex `A`, `B`. -/
theorem integral_scalarQuadratic_mul (a b : ℂ) :
    (∫ z, (a * (conj (circularGaussianCoordinate z) * circularGaussianCoordinate z)) *
      (b * (conj (circularGaussianCoordinate z) * circularGaussianCoordinate z))
      ∂standardCircularGaussian) = a * b + a * b := by
  simp_rw [show ∀ z : ℝ × ℝ,
    (a * (conj (circularGaussianCoordinate z) * circularGaussianCoordinate z)) *
      (b * (conj (circularGaussianCoordinate z) * circularGaussianCoordinate z)) =
    (a * b) * (conj (circularGaussianCoordinate z) * circularGaussianCoordinate z) ^ 2
      from fun z => by ring]
  rw [integral_const_mul, integral_conj_mul_circularGaussianCoordinate_sq]
  ring

end BlockBand.Counting
