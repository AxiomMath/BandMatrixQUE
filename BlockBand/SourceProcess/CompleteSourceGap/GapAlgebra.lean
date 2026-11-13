module

public import BlockBand.Prelude

/-!
# The algebra of the complete-source gap identity

The Wirtinger identity `2iη ∂_w[N(w)N(w)*]_{w=z} = N P𝕊₊ N*` (the source-gap derivative) has the
closed form `N P𝕊₊ N* = ι (L𝒢₂₁K) ι* 𝕊` (`L𝒢₂₁K = K𝒢₁₂𝒢₂₁K = -∂_wΔ`). It is proved here
column block by column block of `ι*𝕊₊N*`, without derivatives:
* `ward21`: the `(2,1)` block of `𝒢 - 𝒢* = 𝒢(𝕄* - 𝕄)𝒢*`,
  `𝒢₂₁ - 𝒢₁₂* = -2i(𝒢₂₁Y𝒢₁₁* + η𝒢₂₂𝒢₁₂*)`, from `Im 𝒢₁₁` and the block identities;
* `gap_col0`: the near column `(1 - c𝒢₂₂)L* - c(𝒢₂₁𝕏₀₁D⁻¹)(Δℝ₁₂)* = 𝒢₂₁K(1 - cR)`, `c = 2iη`;
* `near_row_col0`, `near_row_col1`: the near row of `(z - 𝕏₊)⁻¹` is `[𝒢₂₂, 𝒢₂₁𝕏₀₁D⁻¹]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open Matrix
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`(2,1)` Ward block.** From `Im 𝒢₁₁` (`hG`), `𝒢₁₁B = -z𝒢₁₂` (`hJ2`), `B*𝒢₁₁ + z𝒢₂₁ = 0`
(`hL3`) and `B*𝒢₁₂ + z𝒢₂₂ = 1` (`hL4`), with `z - z̄ = 2iη`:
`𝒢₂₁ - 𝒢₁₂* = -2i(𝒢₂₁Y𝒢₁₁* + η𝒢₂₂𝒢₁₂*)`. -/
theorem ward21 (G Gb Gc Gd B Y : Matrix n n ℂ) (z : ℂ) (η : ℝ) (hz : z ≠ 0)
    (hzη : z - star z = 2 * Complex.I * (η : ℂ))
    (hG : G - Gᴴ = -((2 * Complex.I) • (G * Y * Gᴴ + (η : ℂ) • (Gb * Gbᴴ))))
    (hJ2 : G * B = -(z • Gb)) (hL3 : Bᴴ * G + z • Gc = 0) (hL4 : Bᴴ * Gb + z • Gd = 1) :
    Gc - Gbᴴ = -((2 * Complex.I) • (Gc * Y * Gᴴ + (η : ℂ) • (Gd * Gbᴴ))) := by
  have hc : z • Gc = -(Bᴴ * G) := eq_neg_of_add_eq_zero_right hL3
  have hd : z • Gd = 1 - Bᴴ * Gb := eq_sub_of_add_eq' hL4
  have hs : star z = z - 2 * Complex.I * (η : ℂ) := by rw [← hzη]; ring
  have hb : Bᴴ * Gᴴ = -((z - 2 * Complex.I * (η : ℂ)) • Gbᴴ) := by
    have := congrArg conjTranspose hJ2
    rwa [conjTranspose_mul, conjTranspose_neg, conjTranspose_smul, hs] at this
  have h1 := congrArg (Bᴴ * ·) hG
  simp only [Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_add, hb] at h1
  have key : z • Gc - z • Gbᴴ =
      -((2 * Complex.I) • ((z • Gc) * Y * Gᴴ + (η : ℂ) • ((z • Gd) * Gbᴴ))) := by
    rw [hc, hd]
    simp only [Matrix.neg_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc] at h1 ⊢
    linear_combination (norm := module) (-1 : ℂ) • h1
  apply smul_right_injective _ hz
  simp only [Matrix.smul_mul] at key
  change z • (Gc - Gbᴴ) = z • _
  linear_combination (norm := module) key

/-- **Near column of `ι*𝕊₊N*`** (`c = 2iη`, `L = K𝒢₁₂`, `Δ = K𝒢₁₁K - K`, `Q = ℝ₁₂`,
`P = 𝕏₀₁D⁻¹`, `PQ* = η⁻¹YR*`): `(1 - c𝒢₂₂)L* - c(𝒢₂₁P)(ΔQ)* = 𝒢₂₁K(1 - cR)`. -/
theorem gap_col0 (G Gb Gc Gd K R Y Q P : Matrix n n ℂ) {η : ℝ} (hη : η ≠ 0)
    (hW : Gc - Gbᴴ = -((2 * Complex.I) • (Gc * Y * Gᴴ + (η : ℂ) • (Gd * Gbᴴ))))
    (hK : K - Kᴴ = (2 * Complex.I) • ((η : ℂ) • 1 + Y))
    (hKR : K * R = 1) (hfar : P * Qᴴ = (η : ℂ)⁻¹ • (Y * Rᴴ)) :
    (1 - ((2 * Complex.I) * (η : ℂ)) • Gd) * (K * Gb)ᴴ +
        -(((2 * Complex.I) * (η : ℂ)) • (Gc * P)) * ((K * G * K - K) * Q)ᴴ =
      Gc * K * (1 - ((2 * Complex.I) * (η : ℂ)) • R) := by
  have he : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη
  have hRK : Rᴴ * Kᴴ = 1 := by rw [← conjTranspose_mul, hKR, conjTranspose_one]
  have hRK' : ∀ M : Matrix n n ℂ, Rᴴ * (Kᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hRK, Matrix.one_mul]
  have hKR' : ∀ M : Matrix n n ℂ, K * (R * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hKR, Matrix.one_mul]
  have hfar' : ∀ M : Matrix n n ℂ, P * (Qᴴ * M) = (η : ℂ)⁻¹ • (Y * (Rᴴ * M)) := fun M => by
    rw [← Matrix.mul_assoc, hfar, Matrix.smul_mul, Matrix.mul_assoc]
  have hc : 2 * Complex.I * (η : ℂ) * (η : ℂ)⁻¹ = 2 * Complex.I := by field_simp
  have e1 := congrArg (· * Kᴴ) hW
  simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.add_mul,
    Matrix.mul_assoc] at e1
  have e2 := congrArg (Gc * ·) hK
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one] at e2
  simp only [conjTranspose_mul, conjTranspose_sub, Matrix.sub_mul, Matrix.one_mul,
    Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
    Matrix.mul_assoc, hfar', hRK', hRK, hKR, smul_smul, hc]
  linear_combination (norm := module) (-1 : ℂ) • e1 + (-1 : ℂ) • e2

/-- `𝒢₂₁𝕏₀₁D⁻¹𝕏₁₀G₀ = 𝒢₂₁ + 𝒢₂₂B*G₀` (right-multiplied by `M`). -/
theorem near_row_key (S₀ G₀ X01 X10 Di B Gc Gd : Matrix n n ℂ) (hG0 : S₀ * G₀ = 1)
    (r1 : Gc * (S₀ - X01 * Di * X10) + Gd * Bᴴ = 0) (M : Matrix n n ℂ) :
    Gc * (X01 * (Di * (X10 * (G₀ * M)))) = Gc * M + Gd * (Bᴴ * (G₀ * M)) := by
  have hG0' : S₀ * (G₀ * M) = M := by rw [← Matrix.mul_assoc, hG0, Matrix.one_mul]
  have := congrArg (· * (G₀ * M)) r1
  simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.zero_mul,
    Matrix.mul_assoc, hG0'] at this
  linear_combination (norm := module) (-1 : ℂ) • this

/-- **Near row of `(z - 𝕏₊)⁻¹`, column `0`** (`S₀ = A - E - 𝕏₀₀`, `S₀G₀ = 1`, right fresh
identities `𝒢₂₁(A - E - X) + 𝒢₂₂B* = 0`, `𝒢₂₁B + 𝒢₂₂z = 1`, `X = 𝕏₀₀ + 𝕏₀₁D⁻¹𝕏₁₀`). -/
theorem near_row_col0 (S₀ G₀ X01 X10 Di B Gc Gd Z : Matrix n n ℂ) (hG0 : S₀ * G₀ = 1)
    (r1 : Gc * (S₀ - X01 * Di * X10) + Gd * Bᴴ = 0) (r2 : Gc * B + Gd * Z = 1) :
    Gd * (Z - Bᴴ * G₀ * B) + Gc * X01 * Di * (X10 * G₀ * B) = 1 := by
  simp only [Matrix.mul_sub, Matrix.mul_assoc, near_row_key S₀ G₀ X01 X10 Di B Gc Gd hG0 r1]
  linear_combination (norm := module) r2

/-- **Near row of `(z - 𝕏₊)⁻¹`, column `1`.** -/
theorem near_row_col1 (S₀ G₀ X01 X10 Di D B Gc Gd : Matrix n n ℂ) (hG0 : S₀ * G₀ = 1)
    (hD : Di * D = 1) (r1 : Gc * (S₀ - X01 * Di * X10) + Gd * Bᴴ = 0) :
    Gd * (Bᴴ * G₀ * X01) + Gc * X01 * Di * (D - X10 * G₀ * X01) = 0 := by
  have hD' : Di * D = 1 := hD
  simp only [Matrix.mul_sub, Matrix.mul_assoc, near_row_key S₀ G₀ X01 X10 Di B Gc Gd hG0 r1, hD',
    Matrix.mul_one]
  abel

end BlockBand.SourceProcess.CompleteSourceGap
