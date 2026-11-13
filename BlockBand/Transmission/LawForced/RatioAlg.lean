module

public import BlockBand.Transmission.LawForced.RatioBrL

/-!
# The `κ ≡ 0` one-layer bound against a normalised product

Generic reals: `P ≥ 1` (the normalised product), `0 ≤ v ≤ 1` (`v = W^{-1/2}`). If the inputs
of `ratio_layer_point` satisfy `g ≤ P`, `hs, τ ≤ 4Pv`, `y ≤ κ_yPv²`, `U_a ≤ κ_UPv²`,
`L_w ≤ κ_LP³v³`, `ε ≤ κ_εPv⁴`, `S ≤ κ_Sv²` and `E(M³+M⁹) ≤ σ³ + σ⁹` with `σ ≤ κ_MP³v`, then
**`ratio_rhs_le`**: `A·E(M³+M⁹) + ratioBrBd ≤ ratioK·P²⁷v³`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open BlockBand.Internal.Contracts.TransmissionPath

variable {p : ℕ}

theorem pv_le {P v : ℝ} (hP : 1 ≤ P) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) {k m : ℕ} (hk : k ≤ 27)
    (hm : 3 ≤ m) : P ^ k * v ^ m ≤ P ^ 27 * v ^ 3 :=
  mul_le_mul (pow_le_pow_right₀ hP hk) (pow_le_pow_of_le_one hv0 hv1 hm) (by positivity)
    (by positivity)

/-- The constant of `ratio_rhs_le`. -/
def ratioK (A qK Λ κM κy κU κL κε κS : ℝ) : ℝ :=
  A * (κM ^ 3 + κM ^ 9) + κL + κy ^ 2 * Λ + qK * (κU + κy) ^ 2 + (κL + κy * Λ) ^ 2 / 2 +
    qK * (κε + 16 * κS * (1 + Λ) ^ 2) + (16 * κS * Λ ^ 2 + κε * Λ ^ 2) / 2

theorem ratio_rhs_le (z : DualCoord p) {A κM κy κU κL κε κS P v g hs τ y Ua Lw ε S σ I : ℝ}
    (hA : 0 ≤ A) (hκM : 0 ≤ κM) (hκy : 0 ≤ κy) (hκL : 0 ≤ κL) (hκε : 0 ≤ κε)
    (hκS : 0 ≤ κS) (hΛ : 0 ≤ lamHat z) (hP : 1 ≤ P) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hg0 : 0 ≤ g) (hg : g ≤ P) (hs0 : 0 ≤ hs) (hhs : hs ≤ 4 * P * v) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 4 * P * v) (hy0 : 0 ≤ y) (hy : y ≤ κy * P * v ^ 2) (hU0 : 0 ≤ Ua)
    (hU : Ua ≤ κU * P * v ^ 2) (hL0 : 0 ≤ Lw) (hL : Lw ≤ κL * P ^ 3 * v ^ 3)
    (hε : ε ≤ κε * P * v ^ 4) (hS : S ≤ κS * v ^ 2) (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ κM * P ^ 3 * v) (hI : I ≤ σ ^ 3 + σ ^ 9) :
    A * I + ratioBrBd z g y Lw Ua ε S τ hs ≤
      ratioK A (quadK z) (lamHat z) κM κy κU κL κε κS * (P ^ 27 * v ^ 3) := by
  have hq := quadK_nonneg z
  set Λ := lamHat z
  have hP0 : 0 ≤ P := by linarith
  have pv := fun (k m : ℕ) (hk : k ≤ 27) (hm : 3 ≤ m) => pv_le hP hv0 hv1 hk hm
  have hv2 : v ^ 3 ≤ v ^ 2 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have hP23 : P ^ 2 ≤ P ^ 3 := pow_le_pow_right₀ hP (by norm_num)
  have h27 : 0 ≤ P ^ 27 * v ^ 3 := by positivity
  have t7 : A * I ≤ A * (κM ^ 3 + κM ^ 9) * (P ^ 27 * v ^ 3) := by
    have h3 : σ ^ 3 ≤ κM ^ 3 * (P ^ 9 * v ^ 3) := by
      calc σ ^ 3 ≤ (κM * P ^ 3 * v) ^ 3 := pow_le_pow_left₀ hσ0 hσ 3
        _ = _ := by ring
    have h9 : σ ^ 9 ≤ κM ^ 9 * (P ^ 27 * v ^ 9) := by
      calc σ ^ 9 ≤ (κM * P ^ 3 * v) ^ 9 := pow_le_pow_left₀ hσ0 hσ 9
        _ = _ := by ring
    have a3 := mul_le_mul_of_nonneg_left (pv 9 3 (by norm_num) le_rfl) (pow_nonneg hκM 3)
    have a9 := mul_le_mul_of_nonneg_left (pv 27 9 le_rfl (by norm_num)) (pow_nonneg hκM 9)
    have : I ≤ (κM ^ 3 + κM ^ 9) * (P ^ 27 * v ^ 3) := by linarith
    calc A * I ≤ A * ((κM ^ 3 + κM ^ 9) * (P ^ 27 * v ^ 3)) := mul_le_mul_of_nonneg_left this hA
      _ = _ := by ring
  have t1 : Lw ≤ κL * (P ^ 27 * v ^ 3) := by
    have := mul_le_mul_of_nonneg_left (pv 3 3 (by norm_num) le_rfl) hκL
    linarith
  have t2 : y ^ 2 * (Λ * g) ≤ κy ^ 2 * Λ * (P ^ 27 * v ^ 3) := by
    have : y ^ 2 * (Λ * g) ≤ (κy * P * v ^ 2) ^ 2 * (Λ * P) := by gcongr
    have e : (κy * P * v ^ 2) ^ 2 * (Λ * P) = κy ^ 2 * Λ * (P ^ 3 * v ^ 4) := by ring
    have := mul_le_mul_of_nonneg_left (pv 3 4 (by norm_num) (by norm_num))
      (show 0 ≤ κy ^ 2 * Λ by positivity)
    linarith
  have t3 : quadK z * ((Ua + y) ^ 2 * g) ≤ quadK z * (κU + κy) ^ 2 * (P ^ 27 * v ^ 3) := by
    have : quadK z * ((Ua + y) ^ 2 * g) ≤ quadK z * ((κU * P * v ^ 2 + κy * P * v ^ 2) ^ 2 * P) := by
      gcongr
    have e : quadK z * ((κU * P * v ^ 2 + κy * P * v ^ 2) ^ 2 * P) =
        quadK z * (κU + κy) ^ 2 * (P ^ 3 * v ^ 4) := by ring
    have := mul_le_mul_of_nonneg_left (pv 3 4 (by norm_num) (by norm_num))
      (show 0 ≤ quadK z * (κU + κy) ^ 2 by positivity)
    linarith
  have t4 : (Lw + y * (Λ * g)) ^ 2 / 2 ≤ (κL + κy * Λ) ^ 2 / 2 * (P ^ 27 * v ^ 3) := by
    have hb : Lw + y * (Λ * g) ≤ (κL + κy * Λ) * (P ^ 3 * v ^ 2) := by
      have a1 : Lw ≤ κL * (P ^ 3 * v ^ 2) := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv2 (pow_nonneg hP0 3)) hκL
        linarith
      have a2 : y * (Λ * g) ≤ κy * Λ * (P ^ 3 * v ^ 2) := by
        have : y * (Λ * g) ≤ (κy * P * v ^ 2) * (Λ * P) := by gcongr
        have e : (κy * P * v ^ 2) * (Λ * P) = κy * Λ * (P ^ 2 * v ^ 2) := by ring
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP23 (sq_nonneg v))
          (show 0 ≤ κy * Λ by positivity)
        linarith
      linarith
    have hsq : (Lw + y * (Λ * g)) ^ 2 ≤ ((κL + κy * Λ) * (P ^ 3 * v ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hb 2
    have e : ((κL + κy * Λ) * (P ^ 3 * v ^ 2)) ^ 2 = (κL + κy * Λ) ^ 2 * (P ^ 6 * v ^ 4) := by ring
    have := mul_le_mul_of_nonneg_left (pv 6 4 (by norm_num) (by norm_num))
      (show 0 ≤ (κL + κy * Λ) ^ 2 by positivity)
    rw [e] at hsq
    linarith
  have t5 : quadK z * (ε * g ^ 2 + S * ((1 + Λ) * τ) ^ 2) ≤
      quadK z * (κε + 16 * κS * (1 + Λ) ^ 2) * (P ^ 27 * v ^ 3) := by
    have hb : quadK z * (ε * g ^ 2 + S * ((1 + Λ) * τ) ^ 2) ≤
        quadK z * ((κε * P * v ^ 4) * P ^ 2 + (κS * v ^ 2) * ((1 + Λ) * (4 * P * v)) ^ 2) := by
      gcongr
    have e : quadK z * ((κε * P * v ^ 4) * P ^ 2 + (κS * v ^ 2) * ((1 + Λ) * (4 * P * v)) ^ 2) =
        quadK z * κε * (P ^ 3 * v ^ 4) + quadK z * (16 * κS * (1 + Λ) ^ 2) * (P ^ 2 * v ^ 4) := by
      ring
    have a1 := mul_le_mul_of_nonneg_left (pv 3 4 (by norm_num) (by norm_num))
      (show 0 ≤ quadK z * κε by positivity)
    have a2 := mul_le_mul_of_nonneg_left (pv 2 4 (by norm_num) (by norm_num))
      (show 0 ≤ quadK z * (16 * κS * (1 + Λ) ^ 2) by positivity)
    rw [e] at hb
    linarith
  have t6 : (S * Λ ^ 2 * hs ^ 2 + ε * Λ ^ 2 * g ^ 2) / 2 ≤
      (16 * κS * Λ ^ 2 + κε * Λ ^ 2) / 2 * (P ^ 27 * v ^ 3) := by
    have hb : S * Λ ^ 2 * hs ^ 2 + ε * Λ ^ 2 * g ^ 2 ≤
        (κS * v ^ 2) * Λ ^ 2 * (4 * P * v) ^ 2 + (κε * P * v ^ 4) * Λ ^ 2 * P ^ 2 := by gcongr
    have e : (κS * v ^ 2) * Λ ^ 2 * (4 * P * v) ^ 2 + (κε * P * v ^ 4) * Λ ^ 2 * P ^ 2 =
        16 * κS * Λ ^ 2 * (P ^ 2 * v ^ 4) + κε * Λ ^ 2 * (P ^ 3 * v ^ 4) := by ring
    have a1 := mul_le_mul_of_nonneg_left (pv 2 4 (by norm_num) (by norm_num))
      (show 0 ≤ 16 * κS * Λ ^ 2 by positivity)
    have a2 := mul_le_mul_of_nonneg_left (pv 3 4 (by norm_num) (by norm_num))
      (show 0 ≤ κε * Λ ^ 2 by positivity)
    rw [e] at hb
    linarith
  unfold ratioBrBd ratioK
  linarith

end BlockBand.Transmission.LawForced
