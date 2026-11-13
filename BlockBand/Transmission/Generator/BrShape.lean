module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr

/-!
# The one-layer bracket: bookkeeping of `br_law`'s right side

**`br_rhs_le`**: with `s ≥ 1`, `Y ≥ 1`, `0 ≤ g ≤ Y`, `hf ≤ 4Y/s`, `σn ≤ C_σ/s²`, `ε ≤ C_εY/s⁴`,
`|r| ≤ C_D/s²`, `H₄ ≤ C_bY⁴/s⁴`, `ν ≤ C_νY/s²`, the right side of `br_law` is
`≤ brK·Y⁶/s³`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

theorem br_mono {Y s : ℝ} (hY : 1 ≤ Y) (hs : 1 ≤ s) {j p : ℕ} (hj : j ≤ 6) (hp : 3 ≤ p) :
    Y ^ j / s ^ p ≤ Y ^ 6 / s ^ 3 := by
  have hs0 : 0 < s := by linarith
  calc Y ^ j / s ^ p ≤ Y ^ 6 / s ^ p :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ hY hj) (by positivity)
    _ ≤ Y ^ 6 / s ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hs hp)

/-- The constant of `br_rhs_le`. -/
def brK (K L ck cl Cσ Cε CD Cb Cν : ℝ) : ℝ :=
  K * L * (16 * Cσ + Cε) + 2 * cl * K ^ 2 * (2 * CD + (16 * Cσ + Cε)) +
    2 * ck * L ^ 2 * (2 * CD + (16 * Cσ + Cε)) + (ck + cl + 8 * (ck ^ 2 + cl ^ 2)) * Cb +
    (ck + cl + 8 * (ck ^ 2 + cl ^ 2)) * Cν ^ 4 + K ^ 2 * Cν ^ 2 + L ^ 2 * Cν ^ 2

theorem br_Er_le {s Y g hf σn ε Cσ Cε : ℝ} (hs : 1 ≤ s) (hY : 1 ≤ Y) (hg0 : 0 ≤ g)
    (hgY : g ≤ Y) (hf0 : 0 ≤ hf) (hfY : hf ≤ 4 * Y / s) (hσ : σn ≤ Cσ / s ^ 2)
    (hε : ε ≤ Cε * Y / s ^ 4) (hCσ : 0 ≤ Cσ) (hCε : 0 ≤ Cε) :
    σn * hf ^ 2 + ε * g ^ 2 ≤ (16 * Cσ + Cε) * (Y ^ 3 / s ^ 4) := by
  have hs0 : 0 < s := by linarith
  have a : σn * hf ^ 2 ≤ Cσ / s ^ 2 * (4 * Y / s) ^ 2 :=
    mul_le_mul hσ (pow_le_pow_left₀ hf0 hfY 2) (sq_nonneg _) (by positivity)
  have b : ε * g ^ 2 ≤ Cε * Y / s ^ 4 * Y ^ 2 :=
    mul_le_mul hε (pow_le_pow_left₀ hg0 hgY 2) (sq_nonneg _) (by positivity)
  have e1 : Cσ / s ^ 2 * (4 * Y / s) ^ 2 = 16 * Cσ * (Y ^ 2 / s ^ 4) := by field_simp; ring
  have e2 : Cε * Y / s ^ 4 * Y ^ 2 = Cε * (Y ^ 3 / s ^ 4) := by field_simp
  have c : Y ^ 2 / s ^ 4 ≤ Y ^ 3 / s ^ 4 :=
    div_le_div_of_nonneg_right (pow_le_pow_right₀ hY (by norm_num)) (by positivity)
  have d := mul_le_mul_of_nonneg_left c (by positivity : (0 : ℝ) ≤ 16 * Cσ)
  rw [e1] at a; rw [e2] at b
  have e3 : (16 * Cσ + Cε) * (Y ^ 3 / s ^ 4) = 16 * Cσ * (Y ^ 3 / s ^ 4) + Cε * (Y ^ 3 / s ^ 4) := by
    ring
  rw [e3]; linarith

theorem br_M_le {s Y g Er r CD E0 : ℝ} (hs : 1 ≤ s) (hY : 1 ≤ Y) (hg0 : 0 ≤ g) (hgY : g ≤ Y)
    (hEr : Er ≤ E0 * (Y ^ 3 / s ^ 4)) (hE0 : 0 ≤ E0) (hr : |r| ≤ CD / s ^ 2) (hCD : 0 ≤ CD) :
    2 * |r| * g + Er ≤ (2 * CD + E0) * (Y ^ 3 / s ^ 2) := by
  have hs0 : 0 < s := by linarith
  have a : 2 * |r| * g ≤ 2 * (CD / s ^ 2) * Y :=
    mul_le_mul (by linarith) hgY hg0 (by positivity)
  have e : 2 * (CD / s ^ 2) * Y = 2 * CD * (Y / s ^ 2) := by ring
  have b : Y / s ^ 2 ≤ Y ^ 3 / s ^ 2 := by
    have := pow_le_pow_right₀ hY (show 1 ≤ 3 by norm_num)
    rw [pow_one] at this
    exact div_le_div_of_nonneg_right this (by positivity)
  have c : Y ^ 3 / s ^ 4 ≤ Y ^ 3 / s ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hs (by norm_num))
  have d1 := mul_le_mul_of_nonneg_left b (by positivity : (0 : ℝ) ≤ 2 * CD)
  have d2 := mul_le_mul_of_nonneg_left c hE0
  rw [e] at a
  have e3 : (2 * CD + E0) * (Y ^ 3 / s ^ 2) = 2 * CD * (Y ^ 3 / s ^ 2) + E0 * (Y ^ 3 / s ^ 2) := by
    ring
  rw [e3]; linarith

/-- **Bookkeeping of the bracket bound.** -/
theorem br_rhs_le {K L ck cl s Y g hf σn ε r H4 ν Cσ Cε CD Cb Cν : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hck : 0 ≤ ck) (hcl : 0 ≤ cl) (hs : 1 ≤ s) (hY : 1 ≤ Y) (hg0 : 0 ≤ g) (hgY : g ≤ Y)
    (hf0 : 0 ≤ hf) (hfY : hf ≤ 4 * Y / s) (hσ : σn ≤ Cσ / s ^ 2)
    (hε : ε ≤ Cε * Y / s ^ 4) (hr : |r| ≤ CD / s ^ 2) (hH : H4 ≤ Cb * Y ^ 4 / s ^ 4)
    (hν0 : 0 ≤ ν) (hν : ν ≤ Cν * Y / s ^ 2) (hCσ : 0 ≤ Cσ) (hCε : 0 ≤ Cε) (hCD : 0 ≤ CD)
    (hCb : 0 ≤ Cb) (hCν : 0 ≤ Cν) :
    K * L * (σn * hf ^ 2 + ε * g ^ 2) +
      2 * cl / s * (K ^ 2 * (2 * |r| * g + (σn * hf ^ 2 + ε * g ^ 2))) +
      2 * ck / s * (L ^ 2 * (2 * |r| * g + (σn * hf ^ 2 + ε * g ^ 2))) +
      (s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2)) * H4 +
      ((s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2)) * (ν ^ 2 * g) ^ 2 +
        ((K * (ν * g)) ^ 2 + (L * (ν * g)) ^ 2)) ≤
    brK K L ck cl Cσ Cε CD Cb Cν * (Y ^ 6 / s ^ 3) := by
  have hs0 : 0 < s := by linarith
  set X := Y ^ 6 / s ^ 3
  set E0 := 16 * Cσ + Cε
  set Ca := ck + cl + 8 * (ck ^ 2 + cl ^ 2)
  have hE0 : 0 ≤ E0 := by positivity
  have hCa : 0 ≤ Ca := by positivity
  set Er := σn * hf ^ 2 + ε * g ^ 2
  have hEr := br_Er_le hs hY hg0 hgY hf0 hfY hσ hε hCσ hCε
  have hM := br_M_le hs hY hg0 hgY hEr hE0 hr hCD
  have m34 := br_mono hY hs (j := 3) (p := 4) (by norm_num) (by norm_num)
  have m33 := br_mono hY hs (j := 3) (p := 3) (by norm_num) (by norm_num)
  have m44 := br_mono hY hs (j := 4) (p := 4) (by norm_num) (by norm_num)
  have m43 := br_mono hY hs (j := 4) (p := 3) (by norm_num) (by norm_num)
  have m67 := br_mono hY hs (j := 6) (p := 7) (by norm_num) (by norm_num)
  -- term 1
  have t1 : K * L * Er ≤ K * L * E0 * X := by
    calc K * L * Er ≤ K * L * (E0 * (Y ^ 3 / s ^ 4)) := mul_le_mul_of_nonneg_left hEr (by positivity)
      _ ≤ K * L * (E0 * X) := by gcongr
      _ = _ := by ring
  -- terms 2, 3
  have t2 : ∀ c Kx : ℝ, 0 ≤ c → 0 ≤ Kx → 2 * c / s * (Kx ^ 2 * (2 * |r| * g + Er)) ≤
      2 * c * Kx ^ 2 * (2 * CD + E0) * X := fun c Kx hc hKx => by
    calc 2 * c / s * (Kx ^ 2 * (2 * |r| * g + Er)) ≤
        2 * c / s * (Kx ^ 2 * ((2 * CD + E0) * (Y ^ 3 / s ^ 2))) := by gcongr
      _ = 2 * c * Kx ^ 2 * (2 * CD + E0) * (Y ^ 3 / s ^ 3) := by field_simp
      _ ≤ _ := by gcongr
  -- A3 ≤ s·Ca
  have hA3 : s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2) ≤ s * Ca := by
    have : 8 * (ck ^ 2 + cl ^ 2) ≤ s * (8 * (ck ^ 2 + cl ^ 2)) :=
      le_mul_of_one_le_left (by positivity) hs
    simp only [Ca]; nlinarith
  have hA30 : 0 ≤ s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2) := by positivity
  -- term 4
  have hH0 : H4 ≤ Cb * (Y ^ 4 / s ^ 4) := by rw [mul_div_assoc] at hH; exact hH
  have t4 : (s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2)) * H4 ≤ Ca * Cb * X := by
    rcases le_or_gt 0 H4 with h0 | h0
    · calc (s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2)) * H4 ≤ s * Ca * (Cb * (Y ^ 4 / s ^ 4)) :=
            mul_le_mul hA3 hH0 h0 (by positivity)
        _ = Ca * Cb * (Y ^ 4 / s ^ 3) := by field_simp
        _ ≤ _ := by gcongr
    · have : (s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2)) * H4 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hA30 h0.le
      have : 0 ≤ Ca * Cb * X := by positivity
      linarith
  -- ν²g and νg
  have hνg : ν * g ≤ Cν * (Y ^ 2 / s ^ 2) := by
    calc ν * g ≤ Cν * Y / s ^ 2 * Y := mul_le_mul hν hgY hg0 (by positivity)
      _ = _ := by ring
  have hνg0 : 0 ≤ ν * g := mul_nonneg hν0 hg0
  have hν2g : ν ^ 2 * g ≤ Cν ^ 2 * (Y ^ 3 / s ^ 4) := by
    calc ν ^ 2 * g ≤ (Cν * Y / s ^ 2) ^ 2 * Y :=
          mul_le_mul (pow_le_pow_left₀ hν0 hν 2) hgY hg0 (by positivity)
      _ = _ := by field_simp
  have t5 : (s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2)) * (ν ^ 2 * g) ^ 2 ≤ Ca * Cν ^ 4 * X := by
    calc (s * (ck + cl) + 8 * (ck ^ 2 + cl ^ 2)) * (ν ^ 2 * g) ^ 2 ≤
        s * Ca * (Cν ^ 2 * (Y ^ 3 / s ^ 4)) ^ 2 :=
          mul_le_mul hA3 (pow_le_pow_left₀ (by positivity) hν2g 2) (sq_nonneg _) (by positivity)
      _ = Ca * Cν ^ 4 * (Y ^ 6 / s ^ 7) := by field_simp
      _ ≤ _ := by gcongr
  have t6 : ∀ Kx : ℝ, 0 ≤ Kx → (Kx * (ν * g)) ^ 2 ≤ Kx ^ 2 * Cν ^ 2 * X := fun Kx hKx => by
    calc (Kx * (ν * g)) ^ 2 ≤ (Kx * (Cν * (Y ^ 2 / s ^ 2))) ^ 2 := by gcongr
      _ = Kx ^ 2 * Cν ^ 2 * (Y ^ 4 / s ^ 4) := by field_simp
      _ ≤ _ := by gcongr
  have := t2 cl K hcl hK
  have := t2 ck L hck hL
  have := t6 K hK
  have := t6 L hL
  have eK : brK K L ck cl Cσ Cε CD Cb Cν * X = K * L * E0 * X + 2 * cl * K ^ 2 * (2 * CD + E0) * X +
      2 * ck * L ^ 2 * (2 * CD + E0) * X + Ca * Cb * X + Ca * Cν ^ 4 * X + K ^ 2 * Cν ^ 2 * X +
      L ^ 2 * Cν ^ 2 * X := by simp only [brK, E0, Ca]; ring
  rw [eK]
  linarith

end BlockBand.Transmission.Generator
