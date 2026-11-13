module

public import BlockBand.SourceProcess.FullSource.TraceAlgebra

/-!
# The one-step moment inequality for a complex form

`step_pointwise`: for `u, d ∈ ℂ`, `m ≥ 1` and `W ≥ 1`, `|u + d|^{4m}` is at most `|u|^{4m}` plus
the linear term `2m|u|^{4m-2}·2 Re(ū d)` plus `stepK(2m)(W⁻¹|u|^{4m} + W^{2m-1}|d|^{4m})`, by
Young's inequality `t^{n-j}s^j ≤ W⁻¹tⁿ + W^{n-1}sⁿ` (`young_pow`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open BlockBand.SourceProcess.FullSource

/-- `t^{n-j}s^j ≤ W⁻¹tⁿ + W^{n-1}sⁿ` for `1 ≤ j ≤ n`, `W ≥ 1`. -/
theorem young_pow {t s W : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hW : 1 ≤ W) {n j : ℕ} (hj : 1 ≤ j)
    (hjn : j ≤ n) : t ^ (n - j) * s ^ j ≤ t ^ n / W + W ^ (n - 1) * s ^ n := by
  have hW0 : 0 < W := by linarith
  have hA : 0 ≤ t ^ n / W := by positivity
  have hB : 0 ≤ W ^ (n - 1) * s ^ n := by positivity
  rcases le_total t (W * s) with h | h
  · have h1 : t ^ (n - j) ≤ (W * s) ^ (n - j) := pow_le_pow_left₀ ht h _
    have h2 : W ^ (n - j) ≤ W ^ (n - 1) := pow_le_pow_right₀ hW (by omega)
    calc t ^ (n - j) * s ^ j ≤ (W * s) ^ (n - j) * s ^ j :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = W ^ (n - j) * s ^ n := by
          rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hjn]
      _ ≤ W ^ (n - 1) * s ^ n := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ _ := by linarith
  · have hsW : s ≤ t / W := by rw [le_div_iff₀ hW0]; linarith
    have h1 : s ^ j ≤ (t / W) ^ j := pow_le_pow_left₀ hs hsW _
    have h2 : W ^ 1 ≤ W ^ j := pow_le_pow_right₀ hW hj
    calc t ^ (n - j) * s ^ j ≤ t ^ (n - j) * (t / W) ^ j :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = t ^ n / W ^ j := by
          rw [div_pow, mul_div_assoc', ← pow_add, Nat.sub_add_cancel hjn]
      _ ≤ t ^ n / W := by
          rw [pow_one] at h2
          exact div_le_div_of_nonneg_left (by positivity) hW0 h2
      _ ≤ _ := by linarith

/-- The constant of the one-step inequality. -/
def stepK (n : ℕ) : ℝ := n + 2 ^ (n + 3) + 2 ^ (n + 1) + 2 ^ (3 * n) + 2 ^ (2 * n)

theorem stepK_pos (n : ℕ) : 0 < stepK n := by unfold stepK; positivity

theorem normSq_add_eq (u d : ℂ) :
    ‖u + d‖ ^ 2 = ‖u‖ ^ 2 + (2 * ((starRingEnd ℂ) u * d).re + ‖d‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_add]
  have : (u * (starRingEnd ℂ) d).re = ((starRingEnd ℂ) u * d).re := by
    simp [Complex.mul_re]
  rw [this]; ring

/-- **The pointwise one-step inequality** (`n = 2m`, `m ≥ 1`). -/
theorem step_pointwise (u d : ℂ) {m : ℕ} (hm : 1 ≤ m) {W : ℝ} (hW : 1 ≤ W) :
    (‖u + d‖ ^ 2) ^ (2 * m) ≤ (‖u‖ ^ 2) ^ (2 * m) +
      (2 * m : ℕ) * (‖u‖ ^ 2) ^ (2 * m - 1) * (2 * ((starRingEnd ℂ) u * d).re) +
      stepK (2 * m) * ((‖u‖ ^ 2) ^ (2 * m) / W + W ^ (2 * m - 1) * (‖d‖ ^ 2) ^ (2 * m)) := by
  set n := 2 * m with hn
  have hn2 : 2 ≤ n := by omega
  set t := ‖u‖ ^ 2
  set s := ‖d‖ ^ 2
  set r := 2 * ((starRingEnd ℂ) u * d).re
  have ht : 0 ≤ t := by positivity
  have hs : 0 ≤ s := by positivity
  set Z := t ^ n / W + W ^ (n - 1) * s ^ n
  have Y : ∀ j, 1 ≤ j → j ≤ n → t ^ (n - j) * s ^ j ≤ Z := fun j h1 h2 =>
    young_pow ht hs hW h1 h2
  have hab : |r| ≤ 2 * (‖u‖ * ‖d‖) := by
    have h := Complex.abs_re_le_norm ((starRingEnd ℂ) u * d)
    rw [norm_mul, Complex.norm_conj] at h
    simp only [r, abs_mul, abs_two]; linarith
  have hts : (‖u‖ * ‖d‖) ^ 2 = t * s := by simp only [t, s]; ring
  set y := r + s
  have hy : |y| ≤ 2 * (‖u‖ * ‖d‖) + s := (abs_add_le _ _).trans (by rw [abs_of_nonneg hs]; linarith)
  have hy2 : y ^ 2 ≤ 8 * (t * s) + 2 * s ^ 2 := by
    have h0 : 0 ≤ 2 * (‖u‖ * ‖d‖) + s := by positivity
    have := (sq_abs y).symm ▸ pow_le_pow_left₀ (abs_nonneg y) hy 2
    nlinarith [sq_nonneg (2 * (‖u‖ * ‖d‖) - s)]
  have hyn : |y| ^ n ≤ 2 ^ n * (2 ^ n * (t ^ (n - m) * s ^ m) + s ^ n) := by
    have h1 : |y| ^ n ≤ (2 * (‖u‖ * ‖d‖) + s) ^ n := pow_le_pow_left₀ (abs_nonneg y) hy n
    have h2 : (2 * (‖u‖ * ‖d‖) + s) ^ n ≤ 2 ^ n * ((2 * (‖u‖ * ‖d‖)) ^ n + s ^ n) := by
      have hx : 0 ≤ 2 * (‖u‖ * ‖d‖) := by positivity
      rcases le_total (2 * (‖u‖ * ‖d‖)) s with h | h
      · calc (2 * (‖u‖ * ‖d‖) + s) ^ n ≤ (2 * s) ^ n := pow_le_pow_left₀ (by positivity)
              (by linarith) n
          _ = 2 ^ n * s ^ n := mul_pow _ _ _
          _ ≤ _ := by nlinarith [pow_nonneg hx n, pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
      · calc (2 * (‖u‖ * ‖d‖) + s) ^ n ≤ (2 * (2 * (‖u‖ * ‖d‖))) ^ n :=
              pow_le_pow_left₀ (by positivity) (by linarith) n
          _ = 2 ^ n * (2 * (‖u‖ * ‖d‖)) ^ n := mul_pow _ _ _
          _ ≤ _ := by nlinarith [pow_nonneg hs n, pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
    have h3 : (2 * (‖u‖ * ‖d‖)) ^ n = 2 ^ n * (t ^ (n - m) * s ^ m) := by
      have e1 : (‖u‖ * ‖d‖) ^ n = ((‖u‖ * ‖d‖) ^ 2) ^ m := by rw [← pow_mul]
      rw [mul_pow, e1, hts, mul_pow, show n - m = m by omega]
    rw [h3] at h2; exact h1.trans h2
  have hmain := pow_add_le ht y hn2
  have hsplit : (n : ℝ) * t ^ (n - 1) * y = n * t ^ (n - 1) * r + n * (t ^ (n - 1) * s ^ 1) := by
    simp only [y, pow_one]; ring
  have hY1 := Y 1 le_rfl (by omega)
  have hY2 := Y 2 (by norm_num) hn2
  have hYm := Y m hm (by omega)
  have hYn := Y n (by omega) le_rfl
  have hyt : t ^ (n - 2) * y ^ 2 ≤ 8 * (t ^ (n - 1) * s ^ 1) + 2 * (t ^ (n - 2) * s ^ 2) := by
    have e1 : t ^ (n - 2) * (t * s) = t ^ (n - 1) * s ^ 1 := by
      rw [pow_one, ← mul_assoc, ← pow_succ, show n - 2 + 1 = n - 1 by omega]
    have := mul_le_mul_of_nonneg_left hy2 (pow_nonneg ht (n - 2))
    nlinarith
  have hsn : s ^ n = t ^ (n - n) * s ^ n := by simp
  have hZ0 : 0 ≤ Z := by positivity
  have e : ‖u + d‖ ^ 2 = t + y := normSq_add_eq u d
  rw [e]
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  calc (t + y) ^ n ≤ t ^ n + n * t ^ (n - 1) * y + 2 ^ n * (t ^ (n - 2) * y ^ 2 + |y| ^ n) :=
        hmain
    _ ≤ t ^ n + (n * t ^ (n - 1) * r + n * Z) +
        2 ^ n * ((8 * Z + 2 * Z) + 2 ^ n * (2 ^ n * Z + Z)) := by
        rw [hsplit]
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        have k1 : (n : ℝ) * (t ^ (n - 1) * s ^ 1) ≤ n * Z := mul_le_mul_of_nonneg_left hY1 hn0
        have k2 : t ^ (n - 2) * y ^ 2 + |y| ^ n ≤
            (8 * Z + 2 * Z) + 2 ^ n * (2 ^ n * Z + Z) := by
          rw [hsn] at hyn
          have a1 : 2 ^ n * (t ^ (n - m) * s ^ m) ≤ 2 ^ n * Z := mul_le_mul_of_nonneg_left hYm h2n
          have a2 : 2 ^ n * (2 ^ n * (t ^ (n - m) * s ^ m) + t ^ (n - n) * s ^ n) ≤
              2 ^ n * (2 ^ n * Z + Z) := mul_le_mul_of_nonneg_left (by linarith) h2n
          linarith
        nlinarith [mul_le_mul_of_nonneg_left k2 h2n]
    _ = t ^ n + n * t ^ (n - 1) * r + stepK n * Z := by
        simp only [stepK]; ring

end BlockBand.SourceProcess.RawTag
