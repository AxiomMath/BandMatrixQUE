module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.GaussianSquareCharacteristic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Fourier reduction for the APSSS quadratic ratio

This module formalizes the measure-theoretic and finite-product part of APSSS,
Claim 2 and (6.12)--(6.18).  The diagonal coefficients are `E`, the affine shift is
`b`, and the ambient law is the finite product of standard real Gaussians.
No quadratic-ratio tail estimate or two-dimensional Hölder bound is assumed here.

The uniform estimate of the shifted double integral in APSSS (6.24)--(6.30) is
not part of this module.  Everything before that estimate -- measurable ratio
events, the tail/full-energy split, characteristic-function factorization,
nonvanishing denominators, and Fatou's liminf step -- is proved below without
further hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

/-- The squared numerator of the diagonal APSSS ratio,
`‖Q(g+b)‖² = ∑ Eⱼ²(gⱼ+bⱼ)²`. -/
def quadraticRatioEnergy {n : ℕ} (E b g : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, E j ^ 2 * (g j + b j) ^ 2

/-- The quadratic denominator before subtracting the scalar shift `a`. -/
def quadraticRatioValue {n : ℕ} (E b g : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, E j * (g j + b j) ^ 2

/-- APSSS's `X`: the squared numerator after removing the first `r` dominant
coordinates.  Our convention `r ≤ j` agrees with the paper's one-based `j > r`. -/
def tailQuadraticRatioEnergy {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (g : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, if r ≤ (j : ℕ) then E j ^ 2 * (g j + b j) ^ 2 else 0

/-- Each tail energy is nonnegative. -/
theorem tailQuadraticRatioEnergy_nonneg {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (g : Fin n → ℝ) :
    0 ≤ tailQuadraticRatioEnergy E b r g := by
  unfold tailQuadraticRatioEnergy
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

/-- The paper's elementary split (6.11): the full Euclidean numerator is at most
its first `r` coordinate contributions plus the square root of the tail energy. -/
theorem sqrt_quadraticRatioEnergy_le_dominant_add_tail {n : ℕ}
    (E b g : Fin n → ℝ) (r : ℕ) :
    Real.sqrt (quadraticRatioEnergy E b g) ≤
      (∑ j : Fin n, if (j : ℕ) < r then |E j| * |g j + b j| else 0) +
        Real.sqrt (tailQuadraticRatioEnergy E b r g) := by
  rw [show quadraticRatioEnergy E b g =
      (∑ j : Fin n, if (j : ℕ) < r then (E j * (g j + b j)) ^ 2 else 0) +
      tailQuadraticRatioEnergy E b r g by
    unfold quadraticRatioEnergy tailQuadraticRatioEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : (j : ℕ) < r
    · simp [h, Nat.not_le_of_lt h]
      ring
    · simp [h, Nat.le_of_not_gt h]
      ]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · let f : Fin n → ℝ :=
      fun j => if (j : ℕ) < r then |E j| * |g j + b j| else 0
    have hf : ∀ j ∈ Finset.univ, 0 ≤ f j := by
      intro j _
      dsimp [f]
      split_ifs <;> positivity
    have hs := Finset.sum_sq_le_sq_sum_of_nonneg hf
    have hsq :
        (∑ j : Fin n,
          if (j : ℕ) < r then (E j * (g j + b j)) ^ 2 else 0) =
        (∑ j : Fin n, (f j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [f]
      by_cases h : (j : ℕ) < r
      · simp only [h, ↓reduceIte]
        rw [← abs_mul, sq_abs]
      · simp [h]
    rw [hsq]
    have htail := tailQuadraticRatioEnergy_nonneg E b r g
    rw [add_sq, Real.sq_sqrt htail]
    nlinarith [Real.sqrt_nonneg (tailQuadraticRatioEnergy E b r g),
      Finset.sum_nonneg hf]

/-- The joint characteristic function of APSSS's `(X,Y)`. -/
def quadraticRatioCharacteristic {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (ξ η : ℝ) : ℂ :=
  ∫ g : Fin n → ℝ,
    Complex.exp (I * ((ξ : ℂ) * tailQuadraticRatioEnergy E b r g +
      (η : ℂ) * quadraticRatioValue E b g))
    ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- Exact finite-dimensional formula for the joint characteristic function. -/
theorem quadraticRatioCharacteristic_eq_product {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (ξ η : ℝ) :
    quadraticRatioCharacteristic E b r ξ η =
      ∏ j, gaussianSquareTransform
        (weightedSquareFrequency E r (ξ : ℂ) (η : ℂ) j) (b j) := by
  unfold quadraticRatioCharacteristic tailQuadraticRatioEnergy quadraticRatioValue
  rw [show (fun g : Fin n → ℝ =>
      Complex.exp (I * ((ξ : ℂ) *
        (∑ j : Fin n, if r ≤ (j : ℕ) then E j ^ 2 * (g j + b j) ^ 2 else 0) +
        (η : ℂ) * ∑ j : Fin n, E j * (g j + b j) ^ 2))) =
      (fun g : Fin n → ℝ =>
        Complex.exp
          (∑ j : Fin n, I * weightedSquareFrequency E r (ξ : ℂ) (η : ℂ) j *
            ((g j + b j : ℝ) : ℂ) ^ 2)) by
    funext g
    congr 1
    push_cast
    unfold weightedSquareFrequency
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : (j : ℕ) < r
    · simp [h, Nat.not_le_of_lt h]
      ring
    · simp [h, Nat.le_of_not_gt h]
      ring]
  exact integral_exp_weightedSquares_pi_real E b r ξ η

/-- The positive heat kernel used in APSSS Claim 2.  It is extended by zero on
`x ≤ 0`, exactly as in the paper. -/
def fourierRatioKernel (ε x y : ℝ) : ℝ :=
  if 0 < x then Real.exp (-y ^ 2 / (4 * ε ^ 2 * x)) else 0

/-- The kernel is measurable as a function of its two real variables. -/
theorem measurable_fourierRatioKernel (ε : ℝ) :
    Measurable (fun p : ℝ × ℝ => fourierRatioKernel ε p.1 p.2) := by
  unfold fourierRatioKernel
  apply Measurable.ite
  · exact measurableSet_lt measurable_const measurable_fst
  · fun_prop
  · fun_prop

/-- The deterministic kernel majorization underlying APSSS Claim 2:
on `|y| ≤ ε √x`, the heat kernel is at least `exp (-1/4)`. -/
theorem exp_neg_one_div_four_le_fourierRatioKernel {ε x y : ℝ}
    (hε : 0 < ε) (hx : 0 < x) (hy : |y| ≤ ε * Real.sqrt x) :
    Real.exp (-(1 / 4 : ℝ)) ≤ fourierRatioKernel ε x y := by
  rw [fourierRatioKernel, ite_eq_left hx]
  apply Real.exp_le_exp.mpr
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hεsqrt : 0 ≤ ε * Real.sqrt x := mul_nonneg hε.le hsqrt
  have hy_sq : y ^ 2 ≤ ε ^ 2 * x := by
    rw [← sq_abs y, ← Real.sq_sqrt hx.le]
    convert (sq_le_sq₀ (abs_nonneg y) hεsqrt).mpr hy using 1
    all_goals ring
  have hden : 0 < 4 * ε ^ 2 * x := by positivity
  have hfrac : y ^ 2 / (4 * ε ^ 2 * x) ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  calc
    -(1 / 4 : ℝ) ≤ -(y ^ 2 / (4 * ε ^ 2 * x)) := neg_le_neg hfrac
    _ = -y ^ 2 / (4 * ε ^ 2 * x) := by ring

end PSSSNative.BlockBand.PSSS
