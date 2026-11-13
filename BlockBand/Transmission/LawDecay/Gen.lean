module

public import BlockBand.Transmission.LawDecay.Lyap
public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The generator inequality `𝒢Φ_ε ≤ -(5D₀/512)(Φ_ε - 2√ε)`

`lyapGen ε D P` is the generator of the transmission generator theorem (`A_k`, `B_{kl}`)
applied to `Φ_ε` at the power vector `P`:
`coefX·A₁ + coefY·A₂ + coefXX·B₁₁ + coefXY·B₁₂` (`∂_y²Φ = 0`), with
`A₁ = -(D/2)P₁²`, `A₂ = D(P₁² - 2P₁P₂)`, `B₁₁ = D(P₂ - P₃)`, `B₁₂ = 2D(P₃ - P₄)`.

**`lyapGen_le`**: if `g = P₁ ≥ 0`, `0 ≤ P₂ ≤ g²`, `P₃ ≤ √P₂·P₂`, `P₄ ≥ 0`, `D ≥ 0`,
`0 < ε ≤ 1`, then `lyapGen ε D P ≤ -(5/512)D(Φ_ε(g, P₂) - 2√ε)`.

With `a = √(g+ε)`, `x = √P₂` the proof multiplies by `a⁷` (`lyapGen_eq`) and splits the
polynomial into its degree-10 part (the coefficient of `g`, `≤ -33/512` here) and its degree-8
part (the constant part, `≤ -5/512`; cases `x ≤ g/2` and `x ≥ g/2`, the second using
`15(x - 4a²/5)² ≥ 0`, i.e. `1 + 15x⁴/8 - 3x³ ≥ -1/8`). The `ε = 0` bound `𝒢F ≤ -D₀F/128`
becomes `-(5/512)D₀(Φ_ε - 2√ε)`, by `g²/a³ ≥ a - 2√ε`. The constraints on `P` are the
eigenvalue facts `ℓ² ≤ ℓ¹`, `ℓ³ ≤ ℓ²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

open BlockBand.Internal.Contracts.TransmissionStatements

/-- **The generator applied to `Φ_ε`.** -/
def lyapGen (ε D : ℝ) (P : ℕ → ℝ) : ℝ :=
  coefX ε (P 1) (P 2) * transmissionDrift D 1 P + coefY ε (P 1) * transmissionDrift D 2 P +
    coefXX ε (P 1) (P 2) * transmissionBracket D 1 1 P +
    coefXY ε (P 1) * transmissionBracket D 1 2 P

theorem drift_one (D : ℝ) (P : ℕ → ℝ) : transmissionDrift D 1 P = -(D / 2) * P 1 ^ 2 := by
  simp [transmissionDrift]; ring

theorem drift_two (D : ℝ) (P : ℕ → ℝ) :
    transmissionDrift D 2 P = D * (P 1 ^ 2 - 2 * P 1 * P 2) := by
  simp [transmissionDrift]; ring

theorem bracket_one_one (D : ℝ) (P : ℕ → ℝ) :
    transmissionBracket D 1 1 P = D * (P 2 - P 3) := by
  simp [transmissionBracket]

theorem bracket_one_two (D : ℝ) (P : ℕ → ℝ) :
    transmissionBracket D 1 2 P = 2 * D * (P 3 - P 4) := by
  simp only [transmissionBracket]; push_cast; ring

/-- `s^{-m/2} = (√s^m)⁻¹`. -/
theorem rpow_neg_half {s : ℝ} (hs : 0 < s) (m : ℕ) :
    s ^ (-(m : ℝ) / 2) = (Real.sqrt s ^ m)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_neg hs.le]
  congr 1; ring

theorem rpow_n1 {s : ℝ} (hs : 0 < s) : s ^ (-1 / 2 : ℝ) = (Real.sqrt s ^ 1)⁻¹ := by
  rw [← rpow_neg_half hs]; norm_num

theorem rpow_n3 {s : ℝ} (hs : 0 < s) : s ^ (-3 / 2 : ℝ) = (Real.sqrt s ^ 3)⁻¹ := by
  rw [← rpow_neg_half hs]; norm_num

theorem rpow_n5 {s : ℝ} (hs : 0 < s) : s ^ (-5 / 2 : ℝ) = (Real.sqrt s ^ 5)⁻¹ := by
  rw [← rpow_neg_half hs]; norm_num

theorem rpow_n7 {s : ℝ} (hs : 0 < s) : s ^ (-7 / 2 : ℝ) = (Real.sqrt s ^ 7)⁻¹ := by
  rw [← rpow_neg_half hs]; norm_num

theorem rpow_p1 {s : ℝ} : s ^ (1 / 2 : ℝ) = Real.sqrt s := (Real.sqrt_eq_rpow s).symm

/-- `Φ_ε` in terms of `a = √(g+ε)`. -/
theorem lyap_eq {ε g y : ℝ} (hs : 0 < g + ε) :
    lyap ε g y = Real.sqrt (g + ε) - y / (64 * Real.sqrt (g + ε) ^ 3) := by
  rw [lyap, rpow_p1, rpow_n3 hs]; field_simp

/-- **The polynomial form of the generator**: `a⁷·lyapGen = D·Q`. -/
theorem lyapGen_eq {ε D : ℝ} {P : ℕ → ℝ} (hs : 0 < P 1 + ε) :
    lyapGen ε D P * Real.sqrt (P 1 + ε) ^ 7 = D * (
      -(P 1 ^ 2 / 2) * (Real.sqrt (P 1 + ε) ^ 6 / 2 + 3 * P 2 * Real.sqrt (P 1 + ε) ^ 2 / 128) -
      Real.sqrt (P 1 + ε) ^ 4 / 64 * (P 1 ^ 2 - 2 * P 1 * P 2) +
      (P 2 - P 3) * (-(Real.sqrt (P 1 + ε) ^ 4 / 8) - 15 * P 2 / 512) +
      3 / 64 * Real.sqrt (P 1 + ε) ^ 2 * (P 3 - P 4)) := by
  have ha : 0 < Real.sqrt (P 1 + ε) := Real.sqrt_pos.2 hs
  rw [lyapGen, drift_one, drift_two, bracket_one_one, bracket_one_two, coefX, coefY, coefXX,
    coefXY, rpow_n1 hs, rpow_n3 hs, rpow_n5 hs, rpow_n7 hs]
  field_simp
  ring

/-- The degree-10 part. -/
theorem deg10_le {a g x : ℝ} (hg : 0 ≤ g) (hx : 0 ≤ x) (hxg : x ≤ g) (hxa : x ≤ a ^ 2) :
    -(g ^ 2 * a ^ 6 / 4) + a ^ 4 * g * x ^ 2 / 32 + a ^ 4 * x ^ 3 / 8 + 15 / 512 * x ^ 5 ≤
      -(33 / 512) * g ^ 2 * a ^ 6 := by
  have ha4 : 0 ≤ a ^ 4 := by positivity
  have hx2 : x ^ 2 ≤ g * a ^ 2 := by nlinarith
  have hx2g : x ^ 2 ≤ g ^ 2 := by nlinarith
  have hx3 : x ^ 3 ≤ g ^ 2 * a ^ 2 := by
    have : x ^ 3 = x ^ 2 * x := by ring
    rw [this]; exact mul_le_mul hx2g hxa hx (sq_nonneg g)
  have hx3a : x ^ 3 ≤ a ^ 6 := by
    have : a ^ 6 = (a ^ 2) ^ 3 := by ring
    rw [this]; exact pow_le_pow_left₀ hx hxa 3
  have h1 : a ^ 4 * g * x ^ 2 ≤ g ^ 2 * a ^ 6 := by
    have := mul_le_mul_of_nonneg_left hx2 (mul_nonneg ha4 hg); nlinarith
  have h2 : a ^ 4 * x ^ 3 ≤ g ^ 2 * a ^ 6 := by
    have := mul_le_mul_of_nonneg_left hx3 ha4; nlinarith
  have h3 : x ^ 5 ≤ g ^ 2 * a ^ 6 := by
    have : x ^ 5 = x ^ 2 * x ^ 3 := by ring
    rw [this]; exact mul_le_mul hx2g hx3a (by positivity) (sq_nonneg g)
  nlinarith

/-- The degree-8 part. -/
theorem deg8_le {a g x : ℝ} (hg : 0 ≤ g) (hx : 0 ≤ x) (hxg : x ≤ g) (hga : g ≤ a ^ 2) :
    -(g ^ 2 * a ^ 4 / 64) - a ^ 4 / 8 * x ^ 2 - 15 / 512 * x ^ 4 + 3 / 64 * a ^ 2 * x ^ 3 ≤
      -(5 / 512) * g ^ 2 * a ^ 4 := by
  have ha2 : 0 ≤ a ^ 2 := by positivity
  have ha4 : 0 ≤ a ^ 4 := by positivity
  rcases le_total x (g / 2) with h | h
  · have hx3 : x ^ 3 ≤ g ^ 2 * a ^ 2 / 8 := by
      have : x ^ 3 ≤ (g / 2) ^ 3 := pow_le_pow_left₀ hx h 3
      have : g ^ 3 ≤ g ^ 2 * a ^ 2 := by
        have : g ^ 3 = g ^ 2 * g := by ring
        rw [this]; exact mul_le_mul_of_nonneg_left hga (sq_nonneg g)
      nlinarith
    have : a ^ 2 * x ^ 3 ≤ g ^ 2 * a ^ 4 / 8 := by
      have := mul_le_mul_of_nonneg_left hx3 ha2; nlinarith
    nlinarith [sq_nonneg x, pow_nonneg hx 4, mul_nonneg ha4 (sq_nonneg x)]
  · have hx2 : g ^ 2 / 4 ≤ x ^ 2 := by nlinarith
    have hx2g : x ^ 2 ≤ g ^ 2 := by nlinarith
    have hsq : 0 ≤ 15 * (x - 4 / 5 * a ^ 2) ^ 2 := by positivity
    have key : -(a ^ 4 * x ^ 2 / 64) - 15 / 512 * x ^ 4 + 3 / 64 * a ^ 2 * x ^ 3 ≤
        8 / 5 / 512 * x ^ 2 * a ^ 4 := by
      have : 0 ≤ x ^ 2 * (15 * (x - 4 / 5 * a ^ 2) ^ 2) := mul_nonneg (sq_nonneg x) hsq
      nlinarith
    have e1 : -(g ^ 2 * a ^ 4 / 64) ≤ -(a ^ 4 * x ^ 2 / 64) := by
      have := mul_le_mul_of_nonneg_left hx2g ha4; nlinarith
    have e2 : -(a ^ 4 / 8 * x ^ 2) ≤ -(a ^ 4 * g ^ 2 / 32) := by
      have := mul_le_mul_of_nonneg_left hx2 ha4; nlinarith
    have e3 : x ^ 2 * a ^ 4 ≤ g ^ 2 * a ^ 4 := mul_le_mul_of_nonneg_right hx2g ha4
    nlinarith

/-- **The polynomial inequality** `Q ≤ -(5/512)g²a⁴`. -/
theorem poly_le {a g x P3 P4 : ℝ} (hg : 0 ≤ g) (hx : 0 ≤ x) (hxg : x ≤ g) (hga : g ≤ a ^ 2)
    (hP3x : P3 ≤ x ^ 3) (hP4 : 0 ≤ P4) :
    -(g ^ 2 / 2) * (a ^ 6 / 2 + 3 * x ^ 2 * a ^ 2 / 128) - a ^ 4 / 64 * (g ^ 2 - 2 * g * x ^ 2) +
      (x ^ 2 - P3) * (-(a ^ 4 / 8) - 15 * x ^ 2 / 512) + 3 / 64 * a ^ 2 * (P3 - P4) ≤
      -(5 / 512) * g ^ 2 * a ^ 4 := by
  have hxa : x ≤ a ^ 2 := hxg.trans hga
  have h10 := deg10_le hg hx hxg hxa
  have h8 := deg8_le hg hx hxg hga
  have ha2 : 0 ≤ a ^ 2 := by positivity
  have hcoef : 0 ≤ a ^ 4 / 8 + 15 * x ^ 2 / 512 + 3 / 64 * a ^ 2 := by positivity
  have hP3' := mul_le_mul_of_nonneg_left hP3x hcoef
  have : 0 ≤ g ^ 2 * a ^ 6 := by positivity
  have : 0 ≤ g ^ 2 * x ^ 2 * a ^ 2 := by positivity
  have : 0 ≤ a ^ 2 * P4 := mul_nonneg ha2 hP4
  nlinarith

/-- `g²/a³ ≥ a - 2√ε` for `a = √(g+ε)`. -/
theorem sq_div_cube_ge {ε g : ℝ} (hε : 0 < ε) (hg : 0 ≤ g) :
    Real.sqrt (g + ε) - 2 * Real.sqrt ε ≤ g ^ 2 / Real.sqrt (g + ε) ^ 3 := by
  set a := Real.sqrt (g + ε)
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have ha2 : a ^ 2 = g + ε := Real.sq_sqrt (by linarith)
  have hse : Real.sqrt ε ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hse2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hs0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  rw [le_div_iff₀ (by positivity)]
  have h1 : ε ≤ Real.sqrt ε * a := by nlinarith
  have h2 : a ^ 4 - g ^ 2 = ε * (a ^ 2 + g) := by rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ha2]; ring
  have h3 : ε * (a ^ 2 + g) ≤ 2 * ε * a ^ 2 := by nlinarith
  have h4 : 2 * ε * a ^ 2 ≤ 2 * Real.sqrt ε * a ^ 3 := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * a ^ 2); nlinarith
  nlinarith

/-- **The generator inequality.** -/
theorem lyapGen_le {ε D : ℝ} {P : ℕ → ℝ} (hε : 0 < ε) (hD : 0 ≤ D) (hg : 0 ≤ P 1)
    (h2 : 0 ≤ P 2) (h2g : P 2 ≤ P 1 ^ 2) (h3x : P 3 ≤ Real.sqrt (P 2) * P 2)
    (h4 : 0 ≤ P 4) :
    lyapGen ε D P ≤ -(5 / 512) * D * (lyap ε (P 1) (P 2) - 2 * Real.sqrt ε) := by
  have hs : 0 < P 1 + ε := by linarith
  set a := Real.sqrt (P 1 + ε)
  have ha : 0 < a := Real.sqrt_pos.2 hs
  have ha2 : a ^ 2 = P 1 + ε := Real.sq_sqrt hs.le
  set x := Real.sqrt (P 2)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = P 2 := Real.sq_sqrt h2
  have hxg : x ≤ P 1 := by
    rw [show P 1 = Real.sqrt (P 1 ^ 2) from (Real.sqrt_sq hg).symm]
    exact Real.sqrt_le_sqrt h2g
  have hQ := poly_le (a := a) (P3 := P 3) (P4 := P 4) hg hx hxg (by rw [ha2]; linarith)
    (le_of_le_of_eq h3x (by rw [← hx2]; ring)) h4
  rw [hx2] at hQ
  have hE := lyapGen_eq (ε := ε) (D := D) (P := P) hs
  have ha7 : 0 < a ^ 7 := by positivity
  have hG : lyapGen ε D P ≤ -(5 / 512) * D * (P 1 ^ 2 / a ^ 3) := by
    have : lyapGen ε D P * a ^ 7 ≤ D * (-(5 / 512) * P 1 ^ 2 * a ^ 4) :=
      hE.le.trans (mul_le_mul_of_nonneg_left hQ hD)
    have e : -(5 / 512) * D * (P 1 ^ 2 / a ^ 3) * a ^ 7 = D * (-(5 / 512) * P 1 ^ 2 * a ^ 4) := by
      field_simp
    exact le_of_mul_le_mul_right (this.trans e.ge) ha7
  have hL : lyap ε (P 1) (P 2) ≤ a := by
    rw [lyap_eq hs]
    have : 0 ≤ P 2 / (64 * a ^ 3) := by positivity
    linarith
  have hsq := sq_div_cube_ge hε hg
  have h5 : 0 ≤ 5 / 512 * D := by positivity
  nlinarith

/-- `(63/64)√(g+ε) ≤ Φ_ε(g, P₂) ≤ √(g+ε)` for `0 ≤ P₂ ≤ g²`. -/
theorem lyap_bounds {ε g y : ℝ} (hε : 0 < ε) (hg : 0 ≤ g) (hy : 0 ≤ y) (hyg : y ≤ g ^ 2) :
    63 / 64 * Real.sqrt (g + ε) ≤ lyap ε g y ∧ lyap ε g y ≤ Real.sqrt (g + ε) := by
  have hs : 0 < g + ε := by linarith
  rw [lyap_eq hs]
  set a := Real.sqrt (g + ε)
  have ha : 0 < a := Real.sqrt_pos.2 hs
  have ha2 : a ^ 2 = g + ε := Real.sq_sqrt hs.le
  have h0 : 0 ≤ y / (64 * a ^ 3) := by positivity
  have h1 : y / (64 * a ^ 3) ≤ a / 64 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : y ≤ a ^ 4 := by
      have : g ^ 2 ≤ (a ^ 2) ^ 2 := pow_le_pow_left₀ hg (by rw [ha2]; linarith) 2
      nlinarith
    nlinarith
  constructor <;> linarith

end BlockBand.Transmission.LawDecay
