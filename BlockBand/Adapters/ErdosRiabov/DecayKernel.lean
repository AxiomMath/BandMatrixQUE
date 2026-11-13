module

public import Mathlib

/-!
# The polynomial decay kernel `F_L(r) = (1 + r/L)^{-s}`

Monotonicity, squaring, halving and scale-transfer bounds for the kernel `F_L(r)`, and the
product bound `F_l(u) F_{L₀}(v) ≤ F_{L₀}(u + v)` used for the polynomial control.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

/-- `F_L(r) = ((1 + r/L)^s)⁻¹`. -/
def decayF (s L r : ℝ) : ℝ := ((1 + r / L) ^ s)⁻¹

theorem one_le_base {L r : ℝ} (hL : 0 < L) (hr : 0 ≤ r) : 1 ≤ 1 + r / L := by
  have : 0 ≤ r / L := div_nonneg hr hL.le
  linarith

theorem decayF_eq_rpow_neg {s L r : ℝ} (hL : 0 < L) (hr : 0 ≤ r) :
    (1 + r / L) ^ (-s) = decayF s L r := by
  unfold decayF
  rw [Real.rpow_neg (by linarith [one_le_base hL hr])]

theorem decayF_pos {s L r : ℝ} (hL : 0 < L) (hr : 0 ≤ r) : 0 < decayF s L r := by
  unfold decayF
  exact inv_pos.2 (Real.rpow_pos_of_pos (by linarith [one_le_base hL hr]) _)

theorem decayF_le_one {s L r : ℝ} (hs : 0 ≤ s) (hL : 0 < L) (hr : 0 ≤ r) :
    decayF s L r ≤ 1 := by
  unfold decayF
  exact inv_le_one_of_one_le₀ (Real.one_le_rpow (one_le_base hL hr) hs)

/-- `F` is antitone in the distance. -/
theorem decayF_anti {s L r r' : ℝ} (hs : 0 ≤ s) (hL : 0 < L) (hr : 0 ≤ r) (h : r ≤ r') :
    decayF s L r' ≤ decayF s L r := by
  unfold decayF
  apply inv_anti₀ (Real.rpow_pos_of_pos (by linarith [one_le_base hL hr]) _)
  apply Real.rpow_le_rpow (by linarith [one_le_base hL hr]) _ hs
  have : r / L ≤ r' / L := div_le_div_of_nonneg_right h hL.le
  linarith

/-- `F` is monotone in the scale. -/
theorem decayF_mono_scale {s L L' r : ℝ} (hs : 0 ≤ s) (hL : 0 < L) (h : L ≤ L') (hr : 0 ≤ r) :
    decayF s L r ≤ decayF s L' r := by
  unfold decayF
  apply inv_anti₀ (Real.rpow_pos_of_pos (by linarith [one_le_base (hL.trans_le h) hr]) _)
  apply Real.rpow_le_rpow (by linarith [one_le_base (hL.trans_le h) hr]) _ hs
  have : r / L' ≤ r / L := div_le_div_of_nonneg_left hr hL h
  linarith

/-- `F_D = F_{D/2}²`. -/
theorem decayF_sq {D L r : ℝ} (hL : 0 < L) (hr : 0 ≤ r) :
    decayF D L r = decayF (D / 2) L r ^ 2 := by
  unfold decayF
  have hb : 0 ≤ 1 + r / L := by linarith [one_le_base hL hr]
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hb]
  norm_num

/-- For `s ≥ 2`, `F_s ≤ (1 + r/L)^{-2}`. -/
theorem decayF_le_inv_sq {s L r : ℝ} (hs : 2 ≤ s) (hL : 0 < L) (hr : 0 ≤ r) :
    decayF s L r ≤ ((1 + r / L) ^ 2)⁻¹ := by
  unfold decayF
  have hb := one_le_base hL hr
  apply inv_anti₀ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hb (by norm_num; linarith)

/-- For `s ≥ 3`, `(1 + r/L) F_s ≤ (1 + r/L)^{-2}`. -/
theorem base_mul_decayF_le_inv_sq {s L r : ℝ} (hs : 3 ≤ s) (hL : 0 < L) (hr : 0 ≤ r) :
    (1 + r / L) * decayF s L r ≤ ((1 + r / L) ^ 2)⁻¹ := by
  unfold decayF
  have hb := one_le_base hL hr
  have hb0 : 0 < 1 + r / L := by linarith
  have h3 : (1 + r / L) ^ (3 : ℝ) ≤ (1 + r / L) ^ s :=
    Real.rpow_le_rpow_of_exponent_le hb hs
  have h3' : (1 + r / L) ^ (3 : ℝ) = (1 + r / L) * (1 + r / L) ^ 2 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [h3'] at h3
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  calc (1 + r / L) = ((1 + r / L) ^ 2)⁻¹ * ((1 + r / L) * (1 + r / L) ^ 2) := by
        field_simp
    _ ≤ ((1 + r / L) ^ 2)⁻¹ * (1 + r / L) ^ s := by gcongr

/-- `F_L(δ/2) ≤ 2^s F_L(δ)`. -/
theorem decayF_half_le {s L δ : ℝ} (hs : 0 ≤ s) (hL : 0 < L) (hδ : 0 ≤ δ) :
    decayF s L (δ / 2) ≤ 2 ^ s * decayF s L δ := by
  unfold decayF
  have h1 := one_le_base hL hδ
  have hpos : 0 < (1 + δ / L) / 2 := by linarith
  have hA : (1 + δ / L) / 2 ≤ 1 + δ / 2 / L := by
    have : δ / 2 / L = δ / L / 2 := by ring
    rw [this]; linarith
  calc ((1 + δ / 2 / L) ^ s)⁻¹ ≤ (((1 + δ / L) / 2) ^ s)⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hpos _) (Real.rpow_le_rpow hpos.le hA hs)
    _ = 2 ^ s * ((1 + δ / L) ^ s)⁻¹ := by
        rw [Real.div_rpow (by linarith) (by norm_num)]
        have : (0 : ℝ) < 2 ^ s := by positivity
        have : (0 : ℝ) < (1 + δ / L) ^ s := Real.rpow_pos_of_pos (by linarith) _
        field_simp

/-- For `δ > L₀ ≥ l > 0`: `F_l(δ/2) ≤ (4l/L₀)^s F_{L₀}(δ)`. -/
theorem decayF_transfer {s l L₀ δ : ℝ} (hs : 0 ≤ s) (hl : 0 < l) (hlL : l ≤ L₀) (hδ : L₀ < δ) :
    decayF s l (δ / 2) ≤ (4 * l / L₀) ^ s * decayF s L₀ δ := by
  unfold decayF
  have hL₀ : 0 < L₀ := hl.trans_le hlL
  have hδ0 : 0 < δ := hL₀.trans hδ
  have h2 : 0 < 1 + δ / L₀ := by positivity
  have hk : 0 < 4 * l / L₀ := by positivity
  -- `1 + δ/L₀ ≤ 2δ/L₀ = (4l/L₀)(δ/(2l)) ≤ (4l/L₀)(1 + δ/(2l))`
  have hB : (1 + δ / L₀) / (4 * l / L₀) ≤ 1 + δ / 2 / l := by
    rw [div_le_iff₀ hk]
    have e : (1 + δ / 2 / l) * (4 * l / L₀) = 4 * l / L₀ + 2 * (δ / L₀) := by
      field_simp; ring
    rw [e]
    have : 1 ≤ δ / L₀ := by rw [le_div_iff₀ hL₀]; linarith
    linarith
  have hpos : 0 < (1 + δ / L₀) / (4 * l / L₀) := div_pos h2 hk
  calc ((1 + δ / 2 / l) ^ s)⁻¹ ≤ (((1 + δ / L₀) / (4 * l / L₀)) ^ s)⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hpos _) (Real.rpow_le_rpow hpos.le hB hs)
    _ = (4 * l / L₀) ^ s * ((1 + δ / L₀) ^ s)⁻¹ := by
        rw [Real.div_rpow h2.le hk.le]
        have : (0 : ℝ) < (4 * l / L₀) ^ s := Real.rpow_pos_of_pos hk _
        have : (0 : ℝ) < (1 + δ / L₀) ^ s := Real.rpow_pos_of_pos h2 _
        field_simp

/-- For `δ ≤ L₀`: `1 ≤ 2^s F_{L₀}(δ)`. -/
theorem one_le_two_rpow_mul_decayF {s L₀ δ : ℝ} (hs : 0 ≤ s) (hL : 0 < L₀) (hδ : 0 ≤ δ)
    (h : δ ≤ L₀) : 1 ≤ 2 ^ s * decayF s L₀ δ := by
  unfold decayF
  have h1 := one_le_base hL hδ
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
  apply Real.rpow_le_rpow (by linarith) _ hs
  have : δ / L₀ ≤ 1 := by rw [div_le_one hL]; exact h
  linarith

/-- Product bound: for `l ≤ L₀`, `F_l(u) F_{L₀}(v) ≤ F_{L₀}(u + v)`. -/
theorem decayF_mul_le {s l L₀ u v : ℝ} (hs : 0 ≤ s) (hl : 0 < l) (hlL : l ≤ L₀) (hu : 0 ≤ u)
    (hv : 0 ≤ v) : decayF s l u * decayF s L₀ v ≤ decayF s L₀ (u + v) := by
  have hL₀ : 0 < L₀ := hl.trans_le hlL
  unfold decayF
  have h1 := one_le_base hl hu
  have h2 := one_le_base hL₀ hv
  have h3 := one_le_base hL₀ (add_nonneg hu hv)
  rw [← mul_inv, ← Real.mul_rpow (by linarith) (by linarith)]
  apply inv_anti₀ (by positivity)
  apply Real.rpow_le_rpow (by linarith) _ hs
  have : u / L₀ ≤ u / l := div_le_div_of_nonneg_left hu hl hlL
  have : 0 ≤ u / l * (v / L₀) := by positivity
  have e : (u + v) / L₀ = u / L₀ + v / L₀ := add_div _ _ _
  nlinarith

/-- Clause (i) comparison: `e^{-a r} ≤ (1 + D/a)^D (1 + r)^{-D}` for `a, D > 0`, `r ≥ 0`. -/
theorem exp_neg_le_decay {a D r : ℝ} (ha : 0 < a) (hD : 0 < D) (hr : 0 ≤ r) :
    Real.exp (-(a * r)) ≤ (1 + D / a) ^ D * ((1 + r) ^ D)⁻¹ := by
  have hK : 0 < 1 + D / a := by positivity
  have hbase : 1 + r ≤ (1 + D / a) * Real.exp (a * r / D) := by
    have he := Real.add_one_le_exp (a * r / D)
    have h1 : 1 ≤ Real.exp (a * r / D) := Real.one_le_exp (by positivity)
    have : (1 + D / a) * (a * r / D + 1) = 1 + r + a * r / D + D / a := by
      field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left he hK.le,
      (by positivity : (0 : ℝ) ≤ a * r / D), (by positivity : (0 : ℝ) ≤ D / a)]
  have hpow : (1 + r) ^ D ≤ (1 + D / a) ^ D * Real.exp (a * r) := by
    calc (1 + r) ^ D ≤ ((1 + D / a) * Real.exp (a * r / D)) ^ D :=
          Real.rpow_le_rpow (by linarith) hbase hD.le
      _ = (1 + D / a) ^ D * Real.exp (a * r) := by
          rw [Real.mul_rpow hK.le (Real.exp_pos _).le, ← Real.exp_mul]
          congr 2
          field_simp
  have hr1 : 0 < (1 + r) ^ D := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hr1]
  calc (Real.exp (a * r))⁻¹ * (1 + r) ^ D ≤
        (Real.exp (a * r))⁻¹ * ((1 + D / a) ^ D * Real.exp (a * r)) := by gcongr
    _ = (1 + D / a) ^ D := by field_simp

end BlockBand.Adapters.ErdosRiabov
