module

public import BlockBand.Critical.RelativeVectors.GoodTime

/-!
# The polynomially bounded terms of the error

With `P = N^{3 + 2max(A,1)}` (`rmvP`): `Z² ≤ K_Z P`, `Z ≤ (1+K_Z)P`, `c̄ ≤ P/c₁²`, `b_f ≤ b₀P`,
`X_ext ≤ (rK_Z + 1)P³/c₁²`, hence (`tbQ0_poly_le`, `tbQ1_poly_le`) the `ε`-terms of `tbQ0` are
`≤ K_poly P⁴ ε` and `tbQ1 ≤ K_poly P⁴/ε` for `0 < ε ≤ 1`; `rpow_neg_le_rmvP` converts `N^{-D}` into
`P^{-j}` once `D ≥ (3 + 2max(A,1)) j`; `exp_neg_le_factorial`: `e^{-y} ≤ m!/y^m`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.CoarseRelative

variable {N : ℕ}

/-- The polynomial scale `P = N^{3 + 2max(A,1)}`. -/
def rmvP (N : ℕ) (A : ℝ) : ℝ := (N : ℝ) ^ (3 + 2 * max A 1)

theorem one_le_rmvP (hN : 1 ≤ N) (A : ℝ) : 1 ≤ rmvP N A :=
  Real.one_le_rpow (by exact_mod_cast hN) (by positivity)

theorem natCast_le_rmvP (hN : 1 ≤ N) (A : ℝ) : (N : ℝ) ≤ rmvP N A := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold rmvP
  calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by have := le_max_right A 1; linarith)

/-- `N^{-D} ≤ P^{-j}` once `(3 + 2max(A,1)) j ≤ D`. -/
theorem rpow_neg_le_rmvP (hN : 1 ≤ N) (A : ℝ) (j : ℕ) {D : ℝ}
    (hD : (3 + 2 * max A 1) * j ≤ D) : (N : ℝ) ^ (-D) ≤ (rmvP N A ^ j)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold rmvP
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_neg hN0.le]
  exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- `K_Z = 1/(v₀ c_low)`. -/
def rmvKZ (c s₀ v₀ : ℝ) : ℝ := 1 / (v₀ * lowConst c s₀ v₀)

theorem rmvKZ_nonneg {c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) : 0 ≤ rmvKZ c s₀ v₀ := by
  have hv := hK.2.2.2.2.2
  have hl : 0 < lowConst c s₀ v₀ := by
    unfold lowConst
    have : 0 < c - s₀ := by linarith [hK.2.2.2.2.1, hK.1]
    positivity
  unfold rmvKZ; positivity

theorem frameZsq_le_rmvP (hN : 1 ≤ N) {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) :
    frameZsq N A c s₀ v₀ ≤ rmvKZ c s₀ v₀ * rmvP N A := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hKZ := rmvKZ_nonneg hK
  have e : frameZsq N A c s₀ v₀ = rmvKZ c s₀ v₀ * (N : ℝ) ^ (1 + 2 * max A 1) := by
    unfold frameZsq rmvKZ
    rw [Real.rpow_add hN0, Real.rpow_one]
    ring
  rw [e]
  unfold rmvP
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hKZ

theorem sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  have := sqrt_le_amgm hx one_pos
  rw [div_one] at this
  linarith

/-- The constant of the polynomial terms. -/
def rmvKpoly (r k : ℕ) (Zb cb bb Xb : ℝ) : ℝ :=
  2 * (r : ℝ) ^ 2 * Xb + 1 / 2 * r * bb + Zb ^ 2 * cb * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 + bb * Zb / 4

theorem tbQ0_poly_le {r k : ℕ} {XJ B Z cbar bf ε P Zb cb bb Xb : ℝ} (hP : 1 ≤ P)
    (hNP : (N : ℝ) ≤ P) (hZ0 : 0 ≤ Z) (hZ : Z ≤ Zb * P) (hc0 : 0 ≤ cbar) (hc : cbar ≤ cb * P)
    (hbf : bf ≤ bb * P) (hε : 0 ≤ ε) (hZb : 0 ≤ Zb) (hcb : 0 ≤ cb)
    (hbb : 0 ≤ bb) (hXb : 0 ≤ Xb) :
    tbQ0 N r k XJ B Z cbar bf ε ≤
      (2 * (r : ℝ) ^ 2 * k * XJ + ((k : ℝ) * r) ^ 2 * (B * (Real.sqrt 2 * cbar))) +
        rmvKpoly r k Zb cb bb Xb * P ^ 4 * ε := by
  have hP0 : 0 ≤ P := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold tbQ0 rmvKpoly
  have h3 : Z * Z * (cbar * N) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * ε ≤
      (Zb * P) * (Zb * P) * ((cb * P) * P) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * ε := by gcongr
  have h4 : bf * (1 / 2 * Z) * ((N : ℝ) * ε / 2) ≤
      (bb * P) * (1 / 2 * (Zb * P)) * (P * ε / 2) := by gcongr
  have hP34 : P ^ 3 ≤ P ^ 4 := pow_le_pow_right₀ hP (by norm_num)
  have h4' : (bb * P) * (1 / 2 * (Zb * P)) * (P * ε / 2) ≤ bb * Zb / 4 * P ^ 4 * ε := by
    have e : (bb * P) * (1 / 2 * (Zb * P)) * (P * ε / 2) = bb * Zb / 4 * P ^ 3 * ε := by ring
    rw [e]
    gcongr
  have e3 : (Zb * P) * (Zb * P) * ((cb * P) * P) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * ε =
      Zb ^ 2 * cb * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * P ^ 4 * ε := by ring
  have hrest : 0 ≤ (2 * (r : ℝ) ^ 2 * Xb + 1 / 2 * r * bb) * P ^ 4 * ε := by positivity
  calc _ ≤ (2 * (r : ℝ) ^ 2 * k * XJ + ((k : ℝ) * r) ^ 2 * (B * (Real.sqrt 2 * cbar))) +
        Zb ^ 2 * cb * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * P ^ 4 * ε + bb * Zb / 4 * P ^ 4 * ε := by
        rw [← e3]; linarith
    _ ≤ _ := by nlinarith

theorem tbQ1_poly_le {r k : ℕ} {Xext Z cbar bf ε P Zb cb bb Xb : ℝ} (hP : 1 ≤ P)
    (hNP : (N : ℝ) ≤ P) (hX : Xext ≤ Xb * P ^ 3) (hZ0 : 0 ≤ Z)
    (hZ : Z ≤ Zb * P) (hc0 : 0 ≤ cbar) (hc : cbar ≤ cb * P) (hbf : bf ≤ bb * P)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hZb : 0 ≤ Zb) (hcb : 0 ≤ cb) (hbb : 0 ≤ bb) (hXb : 0 ≤ Xb) :
    tbQ1 N r k Xext Z cbar bf ε ≤ rmvKpoly r k Zb cb bb Xb * P ^ 4 / ε := by
  have hP0 : 0 ≤ P := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hPj : ∀ j : ℕ, j ≤ 4 → P ^ j ≤ P ^ 4 / ε := by
    intro j hj
    rw [le_div_iff₀ hε]
    calc P ^ j * ε ≤ P ^ j * 1 := by gcongr
      _ = P ^ j := mul_one _
      _ ≤ P ^ 4 := pow_le_pow_right₀ hP hj
  unfold tbQ1 rmvKpoly
  have h1 : 2 * (r : ℝ) ^ 2 * Xext ≤ 2 * (r : ℝ) ^ 2 * Xb * (P ^ 4 / ε) := by
    calc 2 * (r : ℝ) ^ 2 * Xext ≤ 2 * (r : ℝ) ^ 2 * (Xb * P ^ 3) := by gcongr
      _ ≤ 2 * (r : ℝ) ^ 2 * (Xb * (P ^ 4 / ε)) := by gcongr; exact hPj 3 (by norm_num)
      _ = _ := by ring
  have h2 : bf * (1 / 2 * r) ≤ 1 / 2 * r * bb * (P ^ 4 / ε) := by
    calc bf * (1 / 2 * r) ≤ (bb * P) * (1 / 2 * r) := by gcongr
      _ = 1 / 2 * r * bb * P ^ 1 := by ring
      _ ≤ 1 / 2 * r * bb * (P ^ 4 / ε) := by gcongr; exact hPj 1 (by norm_num)
  have h3 : Z * Z * (cbar * N) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 / ε ≤
      Zb ^ 2 * cb * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * (P ^ 4 / ε) := by
    calc Z * Z * (cbar * N) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 / ε ≤
        (Zb * P) * (Zb * P) * ((cb * P) * P) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 / ε := by gcongr
      _ = _ := by ring
  have h4 : bf * (1 / 2 * Z) / (2 * ε) ≤ bb * Zb / 4 * (P ^ 4 / ε) := by
    calc bf * (1 / 2 * Z) / (2 * ε) ≤ (bb * P) * (1 / 2 * (Zb * P)) / (2 * ε) :=
          div_le_div_of_nonneg_right (mul_le_mul hbf (by linarith) (by positivity)
            (by positivity)) (by positivity)
      _ = bb * Zb / 4 * (P ^ 2 / ε) := by field_simp; ring
      _ ≤ bb * Zb / 4 * (P ^ 4 / ε) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (pow_le_pow_right₀ hP (by norm_num)) hε.le) (by positivity)
  calc _ ≤ 2 * (r : ℝ) ^ 2 * Xb * (P ^ 4 / ε) + 1 / 2 * r * bb * (P ^ 4 / ε) +
        Zb ^ 2 * cb * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * (P ^ 4 / ε) + bb * Zb / 4 * (P ^ 4 / ε) := by
        linarith
    _ = _ := by ring

/-- `e^{-y} ≤ m!/y^m` for `y > 0`. -/
theorem exp_neg_le_factorial {y : ℝ} (hy : 0 < y) (m : ℕ) :
    Real.exp (-y) ≤ (m.factorial : ℝ) / y ^ m := by
  have h := Real.pow_div_factorial_le_exp y hy.le m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos y)]
  rw [div_le_iff₀ hf] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hy m)]
  nlinarith [Real.exp_pos y]

end BlockBand.Critical.RelativeVectors
