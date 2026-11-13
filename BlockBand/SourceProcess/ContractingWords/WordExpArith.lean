module

public import BlockBand.SourceProcess.ContractingWords.SlotMean

/-!
# Arithmetic for the word-level expansions

With `x = W^{-1/2} ≤ 1`, `e ≥ 0`,
`R = x³ + e² + e^{2d+4} = layerRem W d e`:

* `pow_rem_le`: `(C(x+e))^m ≤ max(1,C)^{d+3} 2^{d+3} R` for `3 ≤ m ≤ d+3`;
* `rem_parts`: `x³ + e² ≤ R`, `e² ≤ R`, `0 ≤ R`; `cube_eq`: `x³ = W⁻¹/√W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

theorem cube_eq {W : ℝ} (hW : 0 < W) : (1 / Real.sqrt W) ^ 3 = W⁻¹ / Real.sqrt W := by
  have h := Real.mul_self_sqrt hW.le
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  set r := Real.sqrt W
  rw [← h]; field_simp

theorem pow_rem_le {x e C : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (he : 0 ≤ e) (hC : 0 ≤ C) {d m : ℕ}
    (hm : 3 ≤ m) (hmd : m ≤ d + 3) :
    (C * (x + e)) ^ m ≤ max 1 C ^ (d + 3) * 2 ^ (d + 3) * (x ^ 3 + e ^ 2 + e ^ (2 * d + 4)) := by
  have h1 : C ^ m ≤ max 1 C ^ (d + 3) :=
    (pow_le_pow_left₀ hC (le_max_right 1 C) m).trans (pow_le_pow_right₀ (le_max_left 1 C) hmd)
  have h2 : (x + e) ^ m ≤ 2 ^ m * (x ^ m + e ^ m) := add_pow_le_two_pow hx he m
  have h3 : x ^ m ≤ x ^ 3 := pow_le_pow_of_le_one hx hx1 hm
  have h4 : e ^ m ≤ e ^ 2 + e ^ (2 * d + 4) := pow_le_two_ends he (by omega) (by omega)
  have h5 : (2 : ℝ) ^ m ≤ 2 ^ (d + 3) := pow_le_pow_right₀ (by norm_num) hmd
  have hR : 0 ≤ x ^ 3 + e ^ 2 + e ^ (2 * d + 4) := by positivity
  rw [mul_pow]
  calc C ^ m * (x + e) ^ m ≤ max 1 C ^ (d + 3) * (2 ^ m * (x ^ m + e ^ m)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ max 1 C ^ (d + 3) * (2 ^ (d + 3) * (x ^ 3 + e ^ 2 + e ^ (2 * d + 4))) := by
        have hM : 0 ≤ max 1 C ^ (d + 3) := pow_nonneg (le_trans zero_le_one (le_max_left 1 C)) _
        refine mul_le_mul_of_nonneg_left (mul_le_mul h5 (by linarith) (by positivity)
          (by positivity)) hM
    _ = _ := by ring

theorem pow_rem_le' {x e C : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (he : 0 ≤ e) (hC : 0 ≤ C) {d m D : ℕ}
    (hm : 3 ≤ m) (hmD : m ≤ D) (hD : D ≤ 2 * d + 4) :
    (C * (x + e)) ^ m ≤ max 1 C ^ D * 2 ^ D * (x ^ 3 + e ^ 2 + e ^ (2 * d + 4)) := by
  have h1 : C ^ m ≤ max 1 C ^ D :=
    (pow_le_pow_left₀ hC (le_max_right 1 C) m).trans (pow_le_pow_right₀ (le_max_left 1 C) hmD)
  have h2 : (x + e) ^ m ≤ 2 ^ m * (x ^ m + e ^ m) := add_pow_le_two_pow hx he m
  have h3 : x ^ m ≤ x ^ 3 := pow_le_pow_of_le_one hx hx1 hm
  have h4 : e ^ m ≤ e ^ 2 + e ^ (2 * d + 4) := pow_le_two_ends he (by omega) (by omega)
  have h5 : (2 : ℝ) ^ m ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) hmD
  rw [mul_pow]
  have hM : 0 ≤ max 1 C ^ D := pow_nonneg (le_trans zero_le_one (le_max_left 1 C)) _
  calc C ^ m * (x + e) ^ m ≤ max 1 C ^ D * (2 ^ m * (x ^ m + e ^ m)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ max 1 C ^ D * (2 ^ D * (x ^ 3 + e ^ 2 + e ^ (2 * d + 4))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h5 (by linarith) (by positivity) (by positivity)) hM
    _ = _ := by ring

theorem rem_parts {x e : ℝ} (hx : 0 ≤ x) (he : 0 ≤ e) (d : ℕ) :
    x ^ 3 + e ^ 2 ≤ x ^ 3 + e ^ 2 + e ^ (2 * d + 4) ∧ e ^ 2 ≤ x ^ 3 + e ^ 2 + e ^ (2 * d + 4) ∧
      0 ≤ x ^ 3 + e ^ 2 + e ^ (2 * d + 4) := by
  have := pow_nonneg he (2 * d + 4); have := pow_nonneg hx 3
  refine ⟨by linarith, by linarith, by positivity⟩

end BlockBand.SourceProcess.ContractingWords
