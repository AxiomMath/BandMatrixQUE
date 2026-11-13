module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.WeightedSquaresModulus

/-!
# The APSSS product envelope

This module proves the elementary estimates in APSSS (6.17)--(6.23) which turn the
exact continued weighted-square characteristic function into the product decay
envelope.  The contour displacement is `δ = 1 / (10 ν²)` and the accumulated
continuation loss is exactly `exp 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex MeasureTheory
open scoped ENNReal NNReal

/-- The decay factor of a dominant coordinate in APSSS (6.23). -/
def dominantDecayFactor (E b η : ℝ) : ℝ :=
  (1 + 4 * (η * E) ^ 2) ^ (-(1 / 4 : ℝ)) *
    Real.exp (-2 * b ^ 2 * (η * E) ^ 2 / (1 + 4 * (η * E) ^ 2))

/-- The decay factor of a tail coordinate in APSSS (6.23). -/
def tailDecayFactor (E b ξ η : ℝ) : ℝ :=
  (1 + 4 * (tailAffineFrequency E ξ η) ^ 2) ^ (-(1 / 4 : ℝ)) *
    Real.exp (-2 * b ^ 2 * (tailAffineFrequency E ξ η) ^ 2 /
      (1 + 4 * (tailAffineFrequency E ξ η) ^ 2))

/-- Rewriting the denominator norm as the negative quarter power of its squared
modulus. -/
theorem gaussianSquareDenominator_shifted_rpow (ζ d : ℝ) :
    ‖gaussianSquareDenominator (shiftedSquareFrequency ζ d)‖ ^ (-(1 / 2 : ℝ)) =
      ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ)) := by
  rw [← normSq_gaussianSquareDenominator_shifted]
  rw [Complex.normSq_eq_norm_sq]
  rw [← Real.rpow_natCast_mul (norm_nonneg _) 2 (-(1 / 4 : ℝ))]
  norm_num

/-- On the real Fourier axis a shifted Gaussian-square transform is exactly the
dominant-coordinate decay factor. -/
theorem gaussianSquareTransform_real_norm_eq_decay (E b η : ℝ) :
    ‖gaussianSquareTransform ((η * E : ℝ) : ℂ) b‖ =
      dominantDecayFactor E b η := by
  rw [show ((η * E : ℝ) : ℂ) = shiftedSquareFrequency (η * E) 0 by
    simp [shiftedSquareFrequency]]
  rw [gaussianSquareTransform_shifted_norm]
  rw [gaussianSquareDenominator_shifted_rpow]
  simp only [zero_mul]
  unfold dominantDecayFactor
  congr 2 <;> ring

/-- Polynomial core of the APSSS tail exponential estimate. -/
theorem shiftedSquare_exponent_le (ζ d b : ℝ) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1 / 10) :
    b ^ 2 * (d * (1 - 2 * d) - 2 * ζ ^ 2) /
        ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) ≤
      10 * d * b ^ 2 - 2 * b ^ 2 * ζ ^ 2 / (1 + 4 * ζ ^ 2) := by
  have hA : 0 < (1 - 2 * d) ^ 2 + 4 * ζ ^ 2 := by
    have : 0 < 1 - 2 * d := by nlinarith
    positivity
  have hB : 0 < 1 + 4 * ζ ^ 2 := by positivity
  apply (div_le_iff₀ hA).2
  have hrearrange :
      (10 * d * b ^ 2 - 2 * b ^ 2 * ζ ^ 2 / (1 + 4 * ζ ^ 2)) *
          ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) =
        (10 * d * b ^ 2 * ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) *
            (1 + 4 * ζ ^ 2) -
          2 * b ^ 2 * ζ ^ 2 * ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2)) /
            (1 + 4 * ζ ^ 2) := by
    field_simp
  rw [hrearrange]
  apply (le_div_iff₀ hB).2
  ring_nf
  have h0 : 0 ≤ 9 - 38 * d + 40 * d ^ 2 := by nlinarith
  have h1 : 0 ≤ 84 - 160 * d + 160 * d ^ 2 := by nlinarith
  have hbracket :
      0 ≤ (9 - 38 * d + 40 * d ^ 2) +
        (84 - 160 * d + 160 * d ^ 2) * ζ ^ 2 + 160 * ζ ^ 4 := by
    positivity
  have hprod := mul_nonneg (sq_nonneg b) (mul_nonneg hd0 hbracket)
  nlinarith

/-- Elementary denominator comparison underlying the continuation loss. -/
theorem shiftedSquare_denominator_base_le (ζ d : ℝ) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1 / 10) :
    1 + 4 * ζ ^ 2 ≤
      Real.exp (40 * d) * ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) := by
  have hexp : 1 + 40 * d ≤ Real.exp (40 * d) := by
    simpa [add_comm] using Real.add_one_le_exp (40 * d)
  have hA : 0 ≤ (1 - 2 * d) ^ 2 + 4 * ζ ^ 2 := by positivity
  calc
    1 + 4 * ζ ^ 2 ≤
        (1 + 40 * d) * ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) := by
          ring_nf
          nlinarith [sq_nonneg ζ]
    _ ≤ Real.exp (40 * d) * ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) :=
      mul_le_mul_of_nonneg_right hexp hA

/-- The shifted denominator costs at most `exp (10d)` relative to the unshifted
quarter-power decay. -/
theorem shiftedSquare_denominator_rpow_le (ζ d : ℝ) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1 / 10) :
    ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ)) ≤
      Real.exp (10 * d) * (1 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ)) := by
  have hA : 0 < (1 - 2 * d) ^ 2 + 4 * ζ ^ 2 := by
    have : 0 < 1 - 2 * d := by nlinarith
    positivity
  have hB : 0 < 1 + 4 * ζ ^ 2 := by positivity
  have hbase := shiftedSquare_denominator_base_le ζ d hd0 hd1
  have hpow := Real.rpow_le_rpow_of_nonpos hB hbase
    (show (-(1 / 4 : ℝ)) ≤ 0 by norm_num)
  rw [Real.mul_rpow (Real.exp_pos _).le hA.le] at hpow
  rw [← Real.exp_mul] at hpow
  have he : 40 * d * (-(1 / 4 : ℝ)) = -10 * d := by ring
  have hpow' :
      Real.exp (-10 * d) *
          ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ)) ≤
        (1 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ)) := by
    simpa only [he] using hpow
  have hpos : 0 < Real.exp (10 * d) := Real.exp_pos _
  calc
    ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ)) =
        Real.exp (10 * d) *
          (Real.exp (-10 * d) *
            ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ))) := by
              rw [← mul_assoc, ← Real.exp_add]
              simp
    _ ≤ Real.exp (10 * d) * (1 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow' hpos.le

/-- One continued tail factor has the exact APSSS exponential/denominator envelope.
This is the coordinate estimate used in (6.23). -/
theorem gaussianSquareTransform_shifted_norm_le_tail (ζ d b : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 10) :
    ‖gaussianSquareTransform (shiftedSquareFrequency ζ d) b‖ ≤
      Real.exp (10 * d * (1 + b ^ 2)) *
        ((1 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ)) *
          Real.exp (-2 * b ^ 2 * ζ ^ 2 / (1 + 4 * ζ ^ 2))) := by
  rw [gaussianSquareTransform_shifted_norm]
  rw [gaussianSquareDenominator_shifted_rpow]
  have hden := shiftedSquare_denominator_rpow_le ζ d hd0 hd1
  have hexponent := shiftedSquare_exponent_le ζ d b hd0 hd1
  have hexp := Real.exp_le_exp.mpr hexponent
  calc
    ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ)) *
          Real.exp
            (b ^ 2 * (d * (1 - 2 * d) - 2 * ζ ^ 2) /
              ((1 - 2 * d) ^ 2 + 4 * ζ ^ 2)) ≤
        (Real.exp (10 * d) * (1 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ))) *
          Real.exp
            (10 * d * b ^ 2 - 2 * b ^ 2 * ζ ^ 2 / (1 + 4 * ζ ^ 2)) := by
      exact mul_le_mul hden hexp (Real.exp_pos _).le (by positivity)
    _ = Real.exp (10 * d * (1 + b ^ 2)) *
        ((1 + 4 * ζ ^ 2) ^ (-(1 / 4 : ℝ)) *
          Real.exp (-2 * b ^ 2 * ζ ^ 2 / (1 + 4 * ζ ^ 2))) := by
      rw [show 10 * d * b ^ 2 - 2 * b ^ 2 * ζ ^ 2 / (1 + 4 * ζ ^ 2) =
        10 * d * b ^ 2 + (-2 * b ^ 2 * ζ ^ 2 / (1 + 4 * ζ ^ 2)) by ring]
      rw [Real.exp_add]
      rw [show 10 * d * (1 + b ^ 2) = 10 * d + 10 * d * b ^ 2 by ring]
      rw [Real.exp_add]
      ring

/-- Product form of the APSSS envelope, before expanding the two named decay
factors.  The hypotheses are exactly the paper's normalization `ν² = tail energy`
and `δ = 1/(10ν²)`. -/
theorem charfun_weightedSquares_envelope {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (_hr : r ≤ n) (ν δ : ℝ)
    (hν : ν ^ 2 = ∑ j : Fin n,
      if r ≤ (j : ℕ) then E j ^ 2 * (1 + b j ^ 2) else 0)
    (hνpos : 0 < ν) (hδ : δ = 1 / (10 * ν ^ 2)) (ξ η : ℝ) :
    ‖∏ j : Fin n, if (j : ℕ) < r then
        gaussianSquareTransform ((η * E j : ℝ) : ℂ) (b j)
      else gaussianSquareTransform
        (shiftedSquareFrequency (tailAffineFrequency (E j) ξ η) (δ * E j ^ 2)) (b j)‖ ≤
      Real.exp 1 * ∏ j : Fin n, if (j : ℕ) < r then
        dominantDecayFactor (E j) (b j) η
      else tailDecayFactor (E j) (b j) ξ η := by
  rw [norm_prod]
  have hνsq : 0 < ν ^ 2 := sq_pos_of_pos hνpos
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hpoint : ∀ j : Fin n,
      ‖if (j : ℕ) < r then
          gaussianSquareTransform ((η * E j : ℝ) : ℂ) (b j)
        else gaussianSquareTransform
          (shiftedSquareFrequency (tailAffineFrequency (E j) ξ η) (δ * E j ^ 2)) (b j)‖ ≤
        Real.exp (if (j : ℕ) < r then 0 else
          10 * δ * coefficientEnergy E b j) *
          (if (j : ℕ) < r then dominantDecayFactor (E j) (b j) η
            else tailDecayFactor (E j) (b j) ξ η) := by
    intro j
    by_cases hj : (j : ℕ) < r
    · simp only [ite_eq_left hj, Real.exp_zero, one_mul]
      exact (gaussianSquareTransform_real_norm_eq_decay (E j) (b j) η).le
    · simp only [ite_eq_right hj]
      have hcoef : coefficientEnergy E b j ≤ ν ^ 2 := by
        rw [hν]
        exact coefficientEnergy_le_tailEnergy E b r j (Nat.le_of_not_gt hj)
      have hEsq : E j ^ 2 ≤ ν ^ 2 := by
        unfold coefficientEnergy at hcoef
        nlinarith [sq_nonneg (E j), sq_nonneg (b j)]
      have hdle : δ * E j ^ 2 ≤ 1 / 10 := by
        calc
          δ * E j ^ 2 ≤ δ * ν ^ 2 := mul_le_mul_of_nonneg_left hEsq hδpos.le
          _ = 1 / 10 := by
            rw [hδ]
            field_simp
      have hone := gaussianSquareTransform_shifted_norm_le_tail
        (tailAffineFrequency (E j) ξ η) (δ * E j ^ 2) (b j)
        (mul_nonneg hδpos.le (sq_nonneg _)) hdle
      simpa only [coefficientEnergy, tailDecayFactor, mul_assoc,
        ite_eq_right hj] using hone
  calc
    ∏ j : Fin n, ‖if (j : ℕ) < r then
        gaussianSquareTransform ((η * E j : ℝ) : ℂ) (b j)
      else gaussianSquareTransform
        (shiftedSquareFrequency (tailAffineFrequency (E j) ξ η) (δ * E j ^ 2)) (b j)‖ ≤
      ∏ j : Fin n,
        (Real.exp (if (j : ℕ) < r then 0 else
          10 * δ * coefficientEnergy E b j) *
          (if (j : ℕ) < r then dominantDecayFactor (E j) (b j) η
            else tailDecayFactor (E j) (b j) ξ η)) := by
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hpoint j)
    _ = (∏ j : Fin n, Real.exp (if (j : ℕ) < r then 0 else
          10 * δ * coefficientEnergy E b j)) *
        (∏ j : Fin n, if (j : ℕ) < r then dominantDecayFactor (E j) (b j) η
          else tailDecayFactor (E j) (b j) ξ η) := by
      rw [Finset.prod_mul_distrib]
    _ = Real.exp 1 * ∏ j : Fin n, if (j : ℕ) < r then
          dominantDecayFactor (E j) (b j) η
        else tailDecayFactor (E j) (b j) ξ η := by
      congr 1
      rw [← Real.exp_sum]
      congr 1
      calc
        ∑ j : Fin n, (if (j : ℕ) < r then 0 else
            10 * δ * coefficientEnergy E b j) =
            10 * δ * ∑ j : Fin n,
              if r ≤ (j : ℕ) then coefficientEnergy E b j else 0 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                by_cases hj : (j : ℕ) < r <;> simp [hj, Nat.le_of_not_gt]
        _ = 1 := by
          rw [show (∑ j : Fin n, if r ≤ (j : ℕ) then coefficientEnergy E b j else 0) =
            ν ^ 2 by simpa only [coefficientEnergy] using hν.symm]
          rw [hδ]
          field_simp

end PSSSNative.BlockBand.PSSS
