module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic

/-!
# Positive-height covariance profile comparison

Scalar comparison of the positive-height profile `(1 + h/b) t / (a² + ((1 + h/b) b)²)` with the
zero-height profile `t/(a² + b²)`, `b = tv`: the ratio lies in `[(1 + h/b)⁻¹, 1 + h/b]`
uniformly in `a`, with the corresponding statements for fixed-order products and for diagonal
matrices in the Loewner order.
-/

open Matrix

namespace BlockBand.Palm

@[expose] public section

noncomputable section

/-- The eigenvalue of the zero-height covariance profile at centered spectral
coordinate `a`.  Here `b = t v > 0`. -/
def zeroHeightProfileEntry (t b a : ℝ) : ℝ := t / (a ^ 2 + b ^ 2)

/-- The eigenvalue of the height-`h` covariance profile. With `b = t v`, `h / b = ε_h`. -/
def positiveHeightProfileEntry (t b h a : ℝ) : ℝ :=
  (1 + h / b) * t / (a ^ 2 + ((1 + h / b) * b) ^ 2)

/-- Scalar denominator comparison underlying the positive-height covariance
profile lemma.  The statement is uniform in the centered eigenvalue `a`. -/
theorem positiveHeightProfileEntry_mem_Icc
    {t b h a : ℝ} (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h) :
    positiveHeightProfileEntry t b h a ∈ Set.Icc
      ((1 + h / b)⁻¹ * zeroHeightProfileEntry t b a)
      ((1 + h / b) * zeroHeightProfileEntry t b a) := by
  have he : 1 ≤ 1 + h / b := by
    have : 0 ≤ h / b := div_nonneg hh (le_of_lt hb)
    linarith
  have hepos : 0 < 1 + h / b := lt_of_lt_of_le (by norm_num) he
  have hd0 : 0 < a ^ 2 + b ^ 2 := by positivity
  have hd1 : 0 < a ^ 2 + ((1 + h / b) * b) ^ 2 := by positivity
  have hb_le : b ≤ (1 + h / b) * b := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (le_of_lt hb)
  have hbscale_sq : b ^ 2 ≤ ((1 + h / b) * b) ^ 2 := by
    nlinarith
  have he_sq : 1 ≤ (1 + h / b) ^ 2 := by nlinarith
  have ha_sq : a ^ 2 ≤ (1 + h / b) ^ 2 * a ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he_sq (sq_nonneg a)
  have hden_lo :
      a ^ 2 + b ^ 2 ≤ a ^ 2 + ((1 + h / b) * b) ^ 2 := by linarith
  have hden_hi :
      a ^ 2 + ((1 + h / b) * b) ^ 2 ≤
        (1 + h / b) ^ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith
  constructor
  · rw [positiveHeightProfileEntry, zeroHeightProfileEntry]
    rw [inv_mul_eq_div]
    rw [div_le_iff₀ hepos]
    rw [show (1 + h / b) * t / (a ^ 2 + ((1 + h / b) * b) ^ 2) *
        (1 + h / b) =
      (1 + h / b) ^ 2 * t / (a ^ 2 + ((1 + h / b) * b) ^ 2) by ring]
    rw [div_le_div_iff₀ hd0 hd1]
    nlinarith [mul_pos ht hepos]
  · rw [positiveHeightProfileEntry, zeroHeightProfileEntry]
    rw [show (1 + h / b) * (t / (a ^ 2 + b ^ 2)) =
      (1 + h / b) * t / (a ^ 2 + b ^ 2) by ring]
    rw [div_le_div_iff₀ hd1 hd0]
    nlinarith [mul_pos ht hepos]

/-- Directionwise relative error at the scalar spectral level.  With
`b = t v`, the right side is precisely `ε_h = h / (t v)`. -/
theorem abs_positiveHeightProfileEntry_div_sub_one_le
    {t b h a : ℝ} (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h) :
    |positiveHeightProfileEntry t b h a / zeroHeightProfileEntry t b a - 1| ≤
      h / b := by
  have heps : 0 ≤ h / b := div_nonneg hh (le_of_lt hb)
  have hzero : 0 < zeroHeightProfileEntry t b a := by
    rw [zeroHeightProfileEntry]
    positivity
  have hbounds := positiveHeightProfileEntry_mem_Icc ht hb hh (a := a)
  have hlo : (1 + h / b)⁻¹ ≤
      positiveHeightProfileEntry t b h a / zeroHeightProfileEntry t b a := by
    exact (le_div_iff₀ hzero).2 hbounds.1
  have hhi : positiveHeightProfileEntry t b h a / zeroHeightProfileEntry t b a ≤
      1 + h / b := by
    exact (div_le_iff₀ hzero).2 hbounds.2
  rw [abs_le]
  constructor
  · have hinv : (1 + h / b)⁻¹ ≥ 1 - h / b := by
      rw [ge_iff_le, inv_eq_one_div, le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg (h / b)]
    linarith
  · linarith

/-- Fixed-order products inherit the multiplicative comparison.
This is the scalar form used after simultaneously diagonalizing all tested
quadratic covariance factors. -/
theorem prod_positiveHeightProfileEntry_mem_Icc
    {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    {t b h : ℝ} (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h) :
    ∏ i ∈ s, positiveHeightProfileEntry t b h (a i) ∈ Set.Icc
      ((1 + h / b)⁻¹ ^ s.card * ∏ i ∈ s, zeroHeightProfileEntry t b (a i))
      ((1 + h / b) ^ s.card * ∏ i ∈ s, zeroHeightProfileEntry t b (a i)) := by
  have hbase : ∀ i, 0 ≤ zeroHeightProfileEntry t b (a i) := fun i =>
    le_of_lt (by rw [zeroHeightProfileEntry]; positivity)
  constructor
  · calc
      (1 + h / b)⁻¹ ^ s.card * ∏ i ∈ s, zeroHeightProfileEntry t b (a i) =
          ∏ i ∈ s, ((1 + h / b)⁻¹ * zeroHeightProfileEntry t b (a i)) := by
            simp only [Finset.prod_const, Finset.prod_mul_distrib]
      _ ≤ ∏ i ∈ s, positiveHeightProfileEntry t b h (a i) := by
        exact Finset.prod_le_prod₀ (fun i hi =>
          mul_nonneg (inv_nonneg.mpr (by
            have : 0 ≤ h / b := div_nonneg hh (le_of_lt hb)
            linarith)) (hbase i)) fun i hi =>
              (positiveHeightProfileEntry_mem_Icc ht hb hh (a := a i)).1
  · calc
      (∏ i ∈ s, positiveHeightProfileEntry t b h (a i)) ≤
          ∏ i ∈ s, ((1 + h / b) * zeroHeightProfileEntry t b (a i)) := by
        exact Finset.prod_le_prod₀ (fun i hi =>
          mul_nonneg (inv_nonneg.mpr (by
            have : 0 ≤ h / b := div_nonneg hh (le_of_lt hb)
            linarith)) (hbase i) |>.trans
              (positiveHeightProfileEntry_mem_Icc ht hb hh (a := a i)).1) fun i hi =>
              (positiveHeightProfileEntry_mem_Icc ht hb hh (a := a i)).2
      _ = (1 + h / b) ^ s.card * ∏ i ∈ s, zeroHeightProfileEntry t b (a i) := by
        simp only [Finset.prod_const, Finset.prod_mul_distrib]

/-- Loewner form of the comparison for diagonal matrices, i.e. the matrix inequality after
diagonalizing the Hermitian background. -/
theorem diagonal_positiveHeightProfile_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t b h : ℝ} (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h) (a : ι → ℝ) :
    (Matrix.diagonal (fun i => positiveHeightProfileEntry t b h (a i)) -
      Matrix.diagonal (fun i =>
        (1 + h / b)⁻¹ * zeroHeightProfileEntry t b (a i))).PosSemidef := by
  have hd : (Matrix.diagonal (fun i =>
      positiveHeightProfileEntry t b h (a i) -
        (1 + h / b)⁻¹ * zeroHeightProfileEntry t b (a i))).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i =>
      sub_nonneg.mpr (positiveHeightProfileEntry_mem_Icc ht hb hh (a := a i)).1
  simpa only [Matrix.diagonal_sub] using hd

/-- Upper simultaneous-diagonal Loewner comparison. -/
theorem diagonal_positiveHeightProfile_ge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t b h : ℝ} (ht : 0 < t) (hb : 0 < b) (hh : 0 ≤ h) (a : ι → ℝ) :
    (Matrix.diagonal (fun i =>
        (1 + h / b) * zeroHeightProfileEntry t b (a i)) -
      Matrix.diagonal (fun i =>
        positiveHeightProfileEntry t b h (a i))).PosSemidef := by
  have hd : (Matrix.diagonal (fun i =>
      (1 + h / b) * zeroHeightProfileEntry t b (a i) -
        positiveHeightProfileEntry t b h (a i))).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i =>
      sub_nonneg.mpr (positiveHeightProfileEntry_mem_Icc ht hb hh (a := a i)).2
  simpa only [Matrix.diagonal_sub] using hd

end

end

end BlockBand.Palm
