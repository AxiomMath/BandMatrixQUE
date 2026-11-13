module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Pointwise arithmetic for the past integrals

Deterministic. With `w = W⁻¹`, `u = W^{-1/2}`,
`m₀ = Cm(d + w)`, `s₀ = Cf(u + d)`, `t = m₀ + s₀`, `N = f_i + f_k`, and AM–GM
`ay ≤ (W/2)a² + (w/2)y²` (which replaces Hölder and needs no square roots):

* `drift_pointwise`: `μK(m₀ + t²)N²H ≤ MKA₁[(3/2)(Wd² + Wd⁴ + w) + 64w(f_i⁸ + f_k⁸) + (w/4)H⁴]`,
  `A₁ = Cm + 2(Cm + Cf)²`;
* `var_pointwise`: `(μK(s₀ + t²)N²H)² ≤ 3M²K²A₂²[(3/2)(w + Wd⁴ + Wd⁸) +
  2^14 w(f_i^16 + f_k^16) + (w/4)H⁸]`, `A₂ = Cf + 2(Cm + Cf)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

theorem add_pow_le_two_pow' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  have hm : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hmk : max a b ^ k ≤ a ^ k + b ^ k := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ha k]
    · rw [max_eq_left h]; linarith [pow_nonneg hb k]
  calc (a + b) ^ k ≤ (2 * max a b) ^ k := pow_le_pow_left₀ (by positivity) hm k
    _ = 2 ^ k * max a b ^ k := by rw [mul_pow]
    _ ≤ 2 ^ k * (a ^ k + b ^ k) := by gcongr

theorem mul_le_half_sq (x y : ℝ) : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
  nlinarith [sq_nonneg (x - y)]

theorem sq_add3_le (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

/-- AM–GM with weight `W`: `ay ≤ (W/2)a² + (W⁻¹/2)y²`. -/
theorem amgm_W {W a y : ℝ} (hW : 0 < W) : a * y ≤ W / 2 * a ^ 2 + W⁻¹ / 2 * y ^ 2 := by
  have h : 0 ≤ W⁻¹ * (W * a - y) ^ 2 := by positivity
  have e : W⁻¹ * (W * a - y) ^ 2 = W * a ^ 2 - 2 * (a * y) + W⁻¹ * y ^ 2 := by
    field_simp; ring
  nlinarith

/-- The scalar facts about `w = W⁻¹`, `u = W^{-1/2}`. -/
theorem w_facts {W : ℝ} (hW : 1 ≤ W) :
    0 < (Real.sqrt W)⁻¹ ∧ (Real.sqrt W)⁻¹ ^ 2 = W⁻¹ ∧ W⁻¹ ≤ (Real.sqrt W)⁻¹ ∧ 0 < W⁻¹ ∧
      W * W⁻¹ = 1 := by
  have hW0 : 0 < W := by linarith
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
  have hs1 : 1 ≤ Real.sqrt W := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hW
  have hsq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0.le
  refine ⟨inv_pos.mpr hs, by rw [inv_pow, hsq], ?_, inv_pos.mpr hW0, mul_inv_cancel₀ hW0.ne'⟩
  exact inv_anti₀ hs (by nlinarith)

/-- `t = m₀ + s₀ ≤ (Cm + Cf)(d + u)`. -/
theorem t_le {W d Cm Cf : ℝ} (hW : 1 ≤ W) (hCm : 0 ≤ Cm) :
    Cm * (d + W⁻¹) + Cf * ((Real.sqrt W)⁻¹ + d) ≤ (Cm + Cf) * (d + (Real.sqrt W)⁻¹) := by
  obtain ⟨-, -, hwu, -, -⟩ := w_facts hW
  have := mul_le_mul_of_nonneg_left hwu hCm
  linarith

theorem t_sq_le {W d Cm Cf : ℝ} (hW : 1 ≤ W) (hd : 0 ≤ d) (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf) :
    (Cm * (d + W⁻¹) + Cf * ((Real.sqrt W)⁻¹ + d)) ^ 2 ≤ 2 * (Cm + Cf) ^ 2 * (d ^ 2 + W⁻¹) := by
  obtain ⟨hu, hu2, hwu, hw, -⟩ := w_facts hW
  have h1 := t_le (d := d) (Cf := Cf) hW hCm
  have h0 : 0 ≤ Cm * (d + W⁻¹) + Cf * ((Real.sqrt W)⁻¹ + d) := by positivity
  calc (Cm * (d + W⁻¹) + Cf * ((Real.sqrt W)⁻¹ + d)) ^ 2
      ≤ ((Cm + Cf) * (d + (Real.sqrt W)⁻¹)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (Cm + Cf) ^ 2 * (d + (Real.sqrt W)⁻¹) ^ 2 := by ring
    _ ≤ (Cm + Cf) ^ 2 * (2 * (d ^ 2 + (Real.sqrt W)⁻¹ ^ 2)) := by
        gcongr; nlinarith [sq_nonneg (d - (Real.sqrt W)⁻¹)]
    _ = 2 * (Cm + Cf) ^ 2 * (d ^ 2 + W⁻¹) := by rw [hu2]; ring

/-- **The drift integrand, pointwise.** -/
theorem drift_pointwise {W d fi fk H Cm Cf K M μn : ℝ} (hW : 1 ≤ W) (hd : 0 ≤ d)
    (hfi : 0 ≤ fi) (hfk : 0 ≤ fk) (hH : 0 ≤ H) (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf) (hK : 0 ≤ K)
    (hμ : 0 ≤ μn) (hμM : μn ≤ M) :
    μn * (K * (Cm * (d + W⁻¹) + (Cm * (d + W⁻¹) + Cf * ((Real.sqrt W)⁻¹ + d)) ^ 2) *
        (fi + fk) ^ 2 * H) ≤
      M * K * (Cm + 2 * (Cm + Cf) ^ 2) * (3 / 2 * (W * d ^ 2) + 3 / 2 * (W * d ^ 4) +
        3 / 2 * W⁻¹ + 64 * (W⁻¹ * fi ^ 8) + 64 * (W⁻¹ * fk ^ 8) + 1 / 4 * (W⁻¹ * H ^ 4)) := by
  obtain ⟨_, _, _, hw, hWw⟩ := w_facts hW
  have hW0 : 0 < W := by linarith
  have hM0 : 0 ≤ M := hμ.trans hμM
  set A₁ := Cm + 2 * (Cm + Cf) ^ 2
  set a := d + d ^ 2 + W⁻¹
  set y := (fi + fk) ^ 2 * H
  have ha : 0 ≤ a := by positivity
  have hy : 0 ≤ y := by positivity
  have h1 : Cm * (d + W⁻¹) + (Cm * (d + W⁻¹) + Cf * ((Real.sqrt W)⁻¹ + d)) ^ 2 ≤ A₁ * a := by
    have ht := t_sq_le hW hd hCm hCf
    have e : A₁ * a = Cm * (d + W⁻¹) + 2 * (Cm + Cf) ^ 2 * (d ^ 2 + W⁻¹) +
        (Cm * d ^ 2 + 2 * (Cm + Cf) ^ 2 * d) := by simp only [A₁, a]; ring
    have h0 : 0 ≤ Cm * d ^ 2 + 2 * (Cm + Cf) ^ 2 * d := by positivity
    rw [e]; linarith
  have h2 := amgm_W (a := a) (y := y) hW0
  have h3 : W / 2 * a ^ 2 ≤ 3 / 2 * (W * d ^ 2) + 3 / 2 * (W * d ^ 4) + 3 / 2 * W⁻¹ := by
    have h := mul_le_mul_of_nonneg_left (sq_add3_le d (d ^ 2) W⁻¹) (by positivity : 0 ≤ W / 2)
    have e : W * (W⁻¹) ^ 2 = W⁻¹ := by rw [sq, ← mul_assoc, hWw, one_mul]
    calc W / 2 * a ^ 2 ≤ W / 2 * (3 * (d ^ 2 + (d ^ 2) ^ 2 + W⁻¹ ^ 2)) := h
      _ = 3 / 2 * (W * d ^ 2) + 3 / 2 * (W * d ^ 4) + 3 / 2 * (W * W⁻¹ ^ 2) := by ring
      _ = _ := by rw [e]
  have h4 : y ^ 2 ≤ ((fi + fk) ^ 8 + H ^ 4) / 2 := by
    have : y ^ 2 = (fi + fk) ^ 4 * (H ^ 2) := by simp only [y]; ring
    rw [this]
    have h := mul_le_half_sq ((fi + fk) ^ 4) (H ^ 2)
    calc (fi + fk) ^ 4 * H ^ 2 ≤ (((fi + fk) ^ 4) ^ 2 + (H ^ 2) ^ 2) / 2 := h
      _ = ((fi + fk) ^ 8 + H ^ 4) / 2 := by ring
  have h5 := add_pow_le_two_pow' hfi hfk 8
  have h6 : W⁻¹ / 2 * y ^ 2 ≤ 64 * (W⁻¹ * fi ^ 8) + 64 * (W⁻¹ * fk ^ 8) +
      1 / 4 * (W⁻¹ * H ^ 4) := by
    have h := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ W⁻¹ / 2)
    have h' := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ W⁻¹ / 4)
    have e : W⁻¹ / 2 * (((fi + fk) ^ 8 + H ^ 4) / 2) =
        W⁻¹ / 4 * (fi + fk) ^ 8 + 1 / 4 * (W⁻¹ * H ^ 4) := by ring
    have e' : W⁻¹ / 4 * (2 ^ 8 * (fi ^ 8 + fk ^ 8)) =
        64 * (W⁻¹ * fi ^ 8) + 64 * (W⁻¹ * fk ^ 8) := by ring
    linarith
  have hcore : a * y ≤ 3 / 2 * (W * d ^ 2) + 3 / 2 * (W * d ^ 4) + 3 / 2 * W⁻¹ +
      64 * (W⁻¹ * fi ^ 8) + 64 * (W⁻¹ * fk ^ 8) + 1 / 4 * (W⁻¹ * H ^ 4) := by linarith
  have hA₁ : 0 ≤ A₁ := by positivity
  calc μn * (K * (Cm * (d + W⁻¹) + (Cm * (d + W⁻¹) + Cf * ((Real.sqrt W)⁻¹ + d)) ^ 2) *
        (fi + fk) ^ 2 * H)
      = μn * K * (Cm * (d + W⁻¹) + (Cm * (d + W⁻¹) + Cf * ((Real.sqrt W)⁻¹ + d)) ^ 2) * y := by
        simp only [y]; ring
    _ ≤ M * K * (A₁ * a) * y := by gcongr
    _ = M * K * A₁ * (a * y) := by ring
    _ ≤ _ := by gcongr

/-- **The variance integrand, pointwise.** -/
theorem var_pointwise {W d fi fk H Cm Cf K M μn : ℝ} (hW : 1 ≤ W) (hd : 0 ≤ d)
    (hfi : 0 ≤ fi) (hfk : 0 ≤ fk) (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf)
    (hμ : 0 ≤ μn) (hμM : μn ≤ M) :
    (μn * (K * (Cf * ((Real.sqrt W)⁻¹ + d) +
        (Cm * (d + W⁻¹) + Cf * ((Real.sqrt W)⁻¹ + d)) ^ 2) * (fi + fk) ^ 2 * H)) ^ 2 ≤
      3 * M ^ 2 * K ^ 2 * (Cf + 2 * (Cm + Cf) ^ 2) ^ 2 * (3 / 2 * W⁻¹ + 3 / 2 * (W * d ^ 4) +
        3 / 2 * (W * d ^ 8) + 2 ^ 14 * (W⁻¹ * fi ^ 16) + 2 ^ 14 * (W⁻¹ * fk ^ 16) +
        1 / 4 * (W⁻¹ * H ^ 8)) := by
  obtain ⟨hu, hu2, hwu, hw, hWw⟩ := w_facts hW
  have hW0 : 0 < W := by linarith
  have hM0 : 0 ≤ M := hμ.trans hμM
  set A₂ := Cf + 2 * (Cm + Cf) ^ 2
  set u := (Real.sqrt W)⁻¹
  set S := Cf * (u + d) + (Cm * (d + W⁻¹) + Cf * (u + d)) ^ 2
  have hS0 : 0 ≤ S := by positivity
  have h1 : S ≤ A₂ * (u + d + d ^ 2) := by
    have ht := t_sq_le hW hd hCm hCf
    have e : A₂ * (u + d + d ^ 2) = Cf * (u + d) + 2 * (Cm + Cf) ^ 2 * (d ^ 2 + W⁻¹) +
        (Cf * d ^ 2 + 2 * (Cm + Cf) ^ 2 * d + 2 * (Cm + Cf) ^ 2 * (u - W⁻¹)) := by
      simp only [A₂]; ring
    have h0 : 0 ≤ Cf * d ^ 2 + 2 * (Cm + Cf) ^ 2 * d + 2 * (Cm + Cf) ^ 2 * (u - W⁻¹) := by
      have : 0 ≤ u - W⁻¹ := sub_nonneg.mpr hwu
      positivity
    simp only [S]; rw [e]; linarith
  set a := W⁻¹ + d ^ 2 + d ^ 4
  have h2 : S ^ 2 ≤ 3 * A₂ ^ 2 * a := by
    have hA₂ : 0 ≤ A₂ := by positivity
    calc S ^ 2 ≤ (A₂ * (u + d + d ^ 2)) ^ 2 := pow_le_pow_left₀ hS0 h1 2
      _ = A₂ ^ 2 * (u + d + d ^ 2) ^ 2 := by ring
      _ ≤ A₂ ^ 2 * (3 * (u ^ 2 + d ^ 2 + (d ^ 2) ^ 2)) := by gcongr; exact sq_add3_le _ _ _
      _ = 3 * A₂ ^ 2 * a := by simp only [a]; rw [hu2]; ring
  set y := (fi + fk) ^ 4 * H ^ 2
  have hy : 0 ≤ y := by positivity
  have ha : 0 ≤ a := by positivity
  have h3 := amgm_W (a := a) (y := y) hW0
  have h4 : W / 2 * a ^ 2 ≤ 3 / 2 * W⁻¹ + 3 / 2 * (W * d ^ 4) + 3 / 2 * (W * d ^ 8) := by
    have h := mul_le_mul_of_nonneg_left (sq_add3_le W⁻¹ (d ^ 2) (d ^ 4))
      (by positivity : 0 ≤ W / 2)
    have e : W * (W⁻¹) ^ 2 = W⁻¹ := by rw [sq, ← mul_assoc, hWw, one_mul]
    calc W / 2 * a ^ 2 ≤ W / 2 * (3 * (W⁻¹ ^ 2 + (d ^ 2) ^ 2 + (d ^ 4) ^ 2)) := h
      _ = 3 / 2 * (W * W⁻¹ ^ 2) + 3 / 2 * (W * d ^ 4) + 3 / 2 * (W * d ^ 8) := by ring
      _ = _ := by rw [e]
  have h5 : y ^ 2 ≤ ((fi + fk) ^ 16 + H ^ 8) / 2 := by
    have : y ^ 2 = (fi + fk) ^ 8 * (H ^ 4) := by simp only [y]; ring
    rw [this]
    have h := mul_le_half_sq ((fi + fk) ^ 8) (H ^ 4)
    calc (fi + fk) ^ 8 * H ^ 4 ≤ (((fi + fk) ^ 8) ^ 2 + (H ^ 4) ^ 2) / 2 := h
      _ = ((fi + fk) ^ 16 + H ^ 8) / 2 := by ring
  have h6 := add_pow_le_two_pow' hfi hfk 16
  have h7 : W⁻¹ / 2 * y ^ 2 ≤ 2 ^ 14 * (W⁻¹ * fi ^ 16) + 2 ^ 14 * (W⁻¹ * fk ^ 16) +
      1 / 4 * (W⁻¹ * H ^ 8) := by
    have h := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ W⁻¹ / 2)
    have h' := mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ W⁻¹ / 4)
    have e : W⁻¹ / 2 * (((fi + fk) ^ 16 + H ^ 8) / 2) =
        W⁻¹ / 4 * (fi + fk) ^ 16 + 1 / 4 * (W⁻¹ * H ^ 8) := by ring
    have e' : W⁻¹ / 4 * (2 ^ 16 * (fi ^ 16 + fk ^ 16)) =
        2 ^ 14 * (W⁻¹ * fi ^ 16) + 2 ^ 14 * (W⁻¹ * fk ^ 16) := by ring
    linarith
  have hcore : a * y ≤ 3 / 2 * W⁻¹ + 3 / 2 * (W * d ^ 4) + 3 / 2 * (W * d ^ 8) +
      2 ^ 14 * (W⁻¹ * fi ^ 16) + 2 ^ 14 * (W⁻¹ * fk ^ 16) + 1 / 4 * (W⁻¹ * H ^ 8) := by linarith
  calc (μn * (K * S * (fi + fk) ^ 2 * H)) ^ 2 = μn ^ 2 * K ^ 2 * S ^ 2 * y := by
        simp only [y]; ring
    _ ≤ M ^ 2 * K ^ 2 * (3 * A₂ ^ 2 * a) * y := by gcongr
    _ = 3 * M ^ 2 * K ^ 2 * A₂ ^ 2 * (a * y) := by ring
    _ ≤ _ := by gcongr

end BlockBand.SourceProcess.LengthCont.OneLayer
