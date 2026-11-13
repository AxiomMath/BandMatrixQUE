module

public import BlockBand.QUE.ModeBound

/-!
# Mode-scale algebra in the QUE proof

With the angular-centre scale `q = n^{1/4} W^{3/4}` and `d ≥ 4/n`, the mode estimate
`(d/2) γ ≤ A/W + (B/q)√γ` gives `γ ≤ A (n/W) + (B²/4)(n/W)^{3/2}
≤ max(A, B²/4) (n/W + (n/W)^{3/2})`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.Assembly

/-- The angular-centre scale `n^(1/4) W^(3/4)`. -/
def centerScale (n W : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt n) * Real.sqrt (W * Real.sqrt W)

/-- The squared scale used after Young absorption. -/
theorem centerScale_sq {n W : ℝ} (hn : 0 < n) (hW : 0 < W) :
    centerScale n W ^ 2 = Real.sqrt n * W * Real.sqrt W := by
  unfold centerScale
  rw [mul_pow, Real.sq_sqrt (Real.sqrt_pos.mpr hn).le,
    Real.sq_sqrt (mul_nonneg hW.le (Real.sqrt_nonneg W))]
  ring

/-- The scale is positive for `n, W > 0`. -/
theorem centerScale_pos {n W : ℝ} (hn : 0 < n) (hW : 0 < W) :
    0 < centerScale n W := by
  unfold centerScale
  positivity

/-- The mode estimate with its two powers of `n/W`, as an algebraic consequence of the
angular-centre hypothesis. -/
theorem current_mode_scale_bound {γ d A B n W : ℝ}
    (hγ : 0 ≤ γ) (hn : 0 < n) (hW : 0 < W) (ha : 0 ≤ A)
    (hd : 4 / n ≤ d)
    (h : d / 2 * γ ≤ A / W + (B / centerScale n W) * Real.sqrt γ) :
    γ ≤ A * (n / W) + (B ^ 2 / 4) * ((n / W) * Real.sqrt (n / W)) := by
  have hsep : 0 < 4 / n := by positivity
  have hbase : 0 ≤ A / W := div_nonneg ha hW.le
  have hbound := BlockBand.QUE.uniform_mode_bound hγ hsep hd hbase h
  have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hsw : Real.sqrt W ≠ 0 := (Real.sqrt_pos.mpr hW).ne'
  have hq : centerScale n W ≠ 0 := (centerScale_pos hn hW).ne'
  have hnsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hwsq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW.le
  have hscale :
      4 * (A / W) / (4 / n) + 4 * (B / centerScale n W) ^ 2 / (4 / n) ^ 2 =
      A * (n / W) + (B ^ 2 / 4) * ((n / W) * Real.sqrt (n / W)) := by
    rw [Real.sqrt_div hn.le, div_pow, centerScale_sq hn hW]
    field_simp
    nlinarith [hnsq, hwsq]
  exact hscale ▸ hbound

/-- The same estimate written with the exponent `3/2`. -/
theorem current_mode_rpow_bound {γ d A B n W : ℝ}
    (hγ : 0 ≤ γ) (hn : 0 < n) (hW : 0 < W) (ha : 0 ≤ A)
    (hd : 4 / n ≤ d)
    (h : d / 2 * γ ≤ A / W + (B / centerScale n W) * Real.sqrt γ) :
    γ ≤ A * (n / W) + (B ^ 2 / 4) * (n / W) ^ (3 / 2 : ℝ) := by
  have hratio : 0 < n / W := div_pos hn hW
  have hpower : (n / W) ^ (3 / 2 : ℝ) = (n / W) * Real.sqrt (n / W) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hratio, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hpower]
  exact current_mode_scale_bound hγ hn hW ha hd h

end BlockBand.QUE.Assembly

namespace BlockBand.QUE.Assembly

/-- A single nonnegative coefficient `max(A, B²/4)` bounds both mode scales; `A, B` are chosen
before `n, W, d`. -/
theorem current_mode_uniform_bound {γ d A B n W : ℝ}
    (hγ : 0 ≤ γ) (hn : 0 < n) (hW : 0 < W) (ha : 0 ≤ A)
    (hd : 4 / n ≤ d)
    (h : d / 2 * γ ≤ A / W + (B / centerScale n W) * Real.sqrt γ) :
    γ ≤ max A (B ^ 2 / 4) * (n / W + (n / W) ^ (3 / 2 : ℝ)) := by
  have hratio : 0 ≤ n / W := (div_pos hn hW).le
  have hpower : 0 ≤ (n / W) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hratio _
  calc
    γ ≤ A * (n / W) + (B ^ 2 / 4) * (n / W) ^ (3 / 2 : ℝ) :=
      current_mode_rpow_bound hγ hn hW ha hd h
    _ ≤ max A (B ^ 2 / 4) * (n / W) +
        max A (B ^ 2 / 4) * (n / W) ^ (3 / 2 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hratio)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hpower)
    _ = _ := by ring

end BlockBand.QUE.Assembly
