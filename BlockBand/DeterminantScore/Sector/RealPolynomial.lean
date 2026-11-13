module

public import BlockBand.DeterminantScore.Sector.Statement
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Complex polynomials evaluated at real coordinates

Continuity and Fréchet derivative of `realEval P`, integrability of complex polynomials under
finite products of centered real Gaussian laws, and a polynomial majorant `polyMajorant` that is
uniform on sup-norm balls (used for dominated differentiation).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open MeasureTheory ProbabilityTheory MvPolynomial
open scoped NNReal

variable {σ : Type*} [Fintype σ]

/-- Evaluation of a complex polynomial at a real point. -/
def realEval (P : MvPolynomial σ ℂ) (x : σ → ℝ) : ℂ :=
  MvPolynomial.eval (fun i => (x i : ℂ)) P

omit [Fintype σ] in
@[simp] theorem realEval_C (a : ℂ) (x : σ → ℝ) : realEval (C a) x = a := by
  simp [realEval]

omit [Fintype σ] in
@[simp] theorem realEval_zero (x : σ → ℝ) : realEval (0 : MvPolynomial σ ℂ) x = 0 := by
  simp [realEval]

omit [Fintype σ] in
@[simp] theorem realEval_one (x : σ → ℝ) : realEval (1 : MvPolynomial σ ℂ) x = 1 := by
  simp [realEval]

omit [Fintype σ] in
@[simp] theorem realEval_X (i : σ) (x : σ → ℝ) : realEval (X i) x = (x i : ℂ) := by
  simp [realEval]

omit [Fintype σ] in
@[simp] theorem realEval_add (P Q : MvPolynomial σ ℂ) (x : σ → ℝ) :
    realEval (P + Q) x = realEval P x + realEval Q x := by
  simp [realEval]

omit [Fintype σ] in
@[simp] theorem realEval_mul (P Q : MvPolynomial σ ℂ) (x : σ → ℝ) :
    realEval (P * Q) x = realEval P x * realEval Q x := by
  simp [realEval]

omit [Fintype σ] in
@[simp] theorem realEval_pow (P : MvPolynomial σ ℂ) (n : ℕ) (x : σ → ℝ) :
    realEval (P ^ n) x = realEval P x ^ n := by
  simp [realEval]

omit [Fintype σ] in
theorem continuous_realEval (P : MvPolynomial σ ℂ) : Continuous (realEval P) :=
  (MvPolynomial.continuous_eval P).comp
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))

/-- The Fréchet derivative of `realEval P` at `x`: `w ↦ Σᵢ (∂ᵢP)(x) wᵢ`. -/
def realEvalFDeriv [DecidableEq σ] (P : MvPolynomial σ ℂ) (x : σ → ℝ) : (σ → ℝ) →L[ℝ] ℂ :=
  ∑ i, realEval (pderiv i P) x • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

theorem realEvalFDeriv_apply [DecidableEq σ] (P : MvPolynomial σ ℂ) (x w : σ → ℝ) :
    realEvalFDeriv P x w = ∑ i, realEval (pderiv i P) x * (w i : ℂ) := by
  simp [realEvalFDeriv]

theorem realEvalFDeriv_single [DecidableEq σ] (P : MvPolynomial σ ℂ) (x : σ → ℝ) (c : σ) :
    realEvalFDeriv P x (Pi.single c 1) = realEval (pderiv c P) x := by
  rw [realEvalFDeriv_apply, Finset.sum_eq_single c]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem continuous_realEvalFDeriv [DecidableEq σ] (P : MvPolynomial σ ℂ) :
    Continuous (realEvalFDeriv P) := by
  unfold realEvalFDeriv
  exact continuous_finsetSum _ fun i _ =>
    (continuous_realEval (pderiv i P)).smul continuous_const

/-- The Fréchet derivative of a polynomial evaluated at real points. -/
theorem hasFDerivAt_realEval [DecidableEq σ] (P : MvPolynomial σ ℂ) (x : σ → ℝ) :
    HasFDerivAt (realEval P) (realEvalFDeriv P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : realEvalFDeriv (C a : MvPolynomial σ ℂ) x = 0 := by
      ext w; simp [realEvalFDeriv_apply, realEval]
    have hf : realEval (C a : MvPolynomial σ ℂ) = fun _ => a := funext fun y => by simp
    rw [h, hf]
    exact hasFDerivAt_const a x
  | add P Q hP hQ =>
    have h : realEvalFDeriv (P + Q) x = realEvalFDeriv P x + realEvalFDeriv Q x := by
      ext w
      simp [realEvalFDeriv_apply, add_mul, Finset.sum_add_distrib]
    rw [h]
    have hf : realEval (P + Q) = realEval P + realEval Q := by
      funext y; simp
    rw [hf]
    exact hP.add hQ
  | mul_X P j hP =>
    have hXj : HasFDerivAt (fun y : σ → ℝ => ((y j : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)) x := by
      exact (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : σ => ℝ) j)).hasFDerivAt (x := x)
    have hmul := hP.mul hXj
    have hf : realEval (P * X j) = realEval P * fun y : σ → ℝ => ((y j : ℝ) : ℂ) := by
      funext y; simp
    rw [hf]
    convert hmul using 1
    ext w
    have h1 : (∑ i, realEval P x * realEval ((Pi.single i (1 : MvPolynomial σ ℂ) : σ → MvPolynomial σ ℂ) j) x *
        (w i : ℂ)) = realEval P x * (w j : ℂ) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi
        simp [Ne.symm hi]
      · simp
    have h2 : (realEval P x • Complex.ofRealCLM.comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ => ℝ) j) +
        (x j : ℂ) • realEvalFDeriv P x) w =
        realEval P x * (w j : ℂ) + (x j : ℂ) * realEvalFDeriv P x w := by
      simp
    rw [h2, realEvalFDeriv_apply, realEvalFDeriv_apply]
    simp only [pderiv_mul, pderiv_X, realEval_add, realEval_mul, add_mul,
      Finset.sum_add_distrib, h1, Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [realEval_X]
    ring

/-- Coordinate-line derivative of a polynomial evaluated at real points. -/
theorem hasDerivAt_realEval_update [DecidableEq σ] (P : MvPolynomial σ ℂ) (x : σ → ℝ)
    (c : σ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => realEval P (Function.update x c r))
      (realEval (pderiv c P) (Function.update x c s)) s := by
  have h := (hasFDerivAt_realEval P (Function.update x c s)).comp_hasDerivAt s
    (hasDerivAt_update x c s)
  rw [realEvalFDeriv_single] at h
  exact h

/-!
## Gaussian integrability
-/

/-- Every complex polynomial evaluated on
the real axis is integrable against a centered real Gaussian law. -/
theorem integrable_polynomial_eval_ofReal_gaussianReal
    (variance : ℝ≥0) (p : Polynomial ℂ) :
    Integrable (fun x : ℝ => p.eval (x : ℂ)) (gaussianReal 0 variance) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert hp.add hq using 1
      ext x
      simp
  | monomial n a =>
      have hpow : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 variance) :=
        integrable_pow_of_integrable_exp_mul (t := (1 : ℝ)) one_ne_zero
          (integrable_exp_mul_gaussianReal 1)
          (by simpa only [neg_one_mul] using integrable_exp_mul_gaussianReal (-1)) n
      have hcomplex : Integrable (fun x : ℝ => ((x ^ n : ℝ) : ℂ))
          (gaussianReal 0 variance) :=
        hpow.ofReal
      simpa [Polynomial.eval_monomial, mul_comm] using hcomplex.const_mul a

/-- Every complex multivariate polynomial
is integrable under an arbitrary finite product of centered real Gaussian laws. -/
theorem integrable_realEval (variance : σ → ℝ≥0) (P : MvPolynomial σ ℂ) :
    Integrable (realEval P) (Measure.pi fun i => gaussianReal 0 (variance i)) := by
  classical
  rw [show realEval P = fun x => ∑ d ∈ P.support, P.coeff d * ∏ i, (x i : ℂ) ^ d i by
    funext x
    exact MvPolynomial.eval_eq' (fun i => (x i : ℂ)) P]
  induction P.support using Finset.induction_on with
  | empty => simp
  | @insert d s hd hs =>
      have hterm : Integrable
          (fun x : σ → ℝ => P.coeff d * ∏ i, (x i : ℂ) ^ d i)
          (Measure.pi fun i => gaussianReal 0 (variance i)) := by
        apply Integrable.const_mul
        apply Integrable.fintype_prod
          (f := fun i (z : ℝ) => (z : ℂ) ^ d i)
          (μ := fun i => gaussianReal 0 (variance i))
        intro i
        simpa [Polynomial.eval_X_pow] using
          (integrable_polynomial_eval_ofReal_gaussianReal (variance i)
            (Polynomial.X ^ d i))
      convert hterm.add hs using 1
      ext x
      simp [hd]

/-!
## A majorant uniform on sup-norm balls
-/

/-- `Σ_d |coeff_d| ∏ᵢ (R + |xᵢ|)^{dᵢ}`: dominates `|P(z)|` whenever `|zᵢ - xᵢ| ≤ R`. -/
def polyMajorant (R : ℝ) (P : MvPolynomial σ ℂ) (x : σ → ℝ) : ℝ :=
  ∑ d ∈ P.support, ‖P.coeff d‖ * ∏ i, (R + |x i|) ^ d i

theorem norm_realEval_le_polyMajorant (P : MvPolynomial σ ℂ) {R : ℝ} {x z : σ → ℝ}
    (hz : ∀ i, |z i - x i| ≤ R) : ‖realEval P z‖ ≤ polyMajorant R P x := by
  unfold realEval polyMajorant
  rw [MvPolynomial.eval_eq']
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
    fun i _ => ?_) (norm_nonneg _)
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  apply pow_le_pow_left₀ (abs_nonneg _)
  have h1 := hz i
  have h2 : |z i| ≤ |z i - x i| + |x i| := by
    simpa using abs_add_le (z i - x i) (x i)
  linarith

theorem integrable_add_abs_pow_gaussianReal (variance : ℝ≥0) (R : ℝ) (n : ℕ) :
    Integrable (fun s : ℝ => (R + |s|) ^ n) (gaussianReal 0 variance) := by
  have hk (k : ℕ) : Integrable (fun s : ℝ => |s| ^ k) (gaussianReal 0 variance) := by
    have h := (memLp_id_gaussianReal' (μ := 0) (v := variance) (k : ENNReal)
      (by simp)).integrable_norm_pow'
    simpa using h
  have hexp : (fun s : ℝ => (R + |s|) ^ n) =
      fun s => ∑ k ∈ Finset.range (n + 1), R ^ k * |s| ^ (n - k) * (n.choose k : ℝ) := by
    funext s
    rw [add_pow]
  rw [hexp]
  refine integrable_finsetSum _ fun k _ => ?_
  exact ((hk (n - k)).const_mul (R ^ k)).mul_const _

theorem integrable_polyMajorant (variance : σ → ℝ≥0) (R : ℝ) (P : MvPolynomial σ ℂ) :
    Integrable (polyMajorant R P) (Measure.pi fun i => gaussianReal 0 (variance i)) := by
  unfold polyMajorant
  refine integrable_finsetSum _ fun d _ => ?_
  exact (Integrable.fintype_prod (f := fun i (s : ℝ) => (R + |s|) ^ d i)
    (μ := fun i => gaussianReal 0 (variance i))
    (fun i => integrable_add_abs_pow_gaussianReal (variance i) R (d i))).const_mul _

theorem polyMajorant_nonneg {R : ℝ} (hR : 0 ≤ R) (P : MvPolynomial σ ℂ) (x : σ → ℝ) :
    0 ≤ polyMajorant R P x := by
  unfold polyMajorant
  exact Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg fun i _ => pow_nonneg (add_nonneg hR (abs_nonneg _)) _)

end BlockBand.DeterminantScore.Sector
