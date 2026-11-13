module

public import BlockBand.Prelude

/-!
# The algebra of the full Ward identity

Matrix identities giving the near diagonal block of the full Ward identity from the
left-inverse relations of the layer resolvent.

* `im_inv_block`: if `G M + Gb B* = 1` and `G B = -z Gb`, then
  `G - G* = G(M* - M)G* - (z - z̄) Gb Gb*` (the `(1,1)` block of `𝒢 - 𝒢* = 𝒢(𝕄* - 𝕄)𝒢*`).
* `ward_algebra`: from `G - G* = -2i(GYG* + η GbGb*)` (`Im 𝒢₁₁`), `K - K* = 2i(η + Y)`,
  `KR = 1` and `RYR* = η QQ*` (far absorption, `Q = ℝ₁₂`), with `Δ = KGK - K`,
  `f = R - (2iη)⁻¹`:
  `(KGb)(KGb)* + (ΔQ)(ΔQ)* - 1 = Δf + f*Δ*`,
  the near diagonal block of `𝓔 = NN* - I = ιΔF + F*Δ*ι*`, whose near diagonal entry reads
  `LL* + Δℝ₁₂ℝ₁₂*Δ* = I + Δf + f*Δ*`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open Matrix
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `(1,1)` block of `𝒢 - 𝒢* = 𝒢(𝕄* - 𝕄)𝒢*` from the left-inverse identities. -/
theorem im_inv_block (G Gb M B : Matrix n n ℂ) (z : ℂ) (hJ1 : G * M + Gb * Bᴴ = 1)
    (hJ2 : G * B = -(z • Gb)) :
    G - Gᴴ = G * (Mᴴ - M) * Gᴴ - (z - star z) • (Gb * Gbᴴ) := by
  have hGM : G * M = 1 - Gb * Bᴴ := eq_sub_of_add_eq hJ1
  have e1 : G * M * Gᴴ = Gᴴ + star z • (Gb * Gbᴴ) := by
    rw [hGM, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, ← conjTranspose_mul, hJ2,
      conjTranspose_neg, conjTranspose_smul, Matrix.mul_neg, Matrix.mul_smul]
    abel
  have e2 : G * Mᴴ * Gᴴ = G + z • (Gb * Gbᴴ) := by
    rw [Matrix.mul_assoc, ← conjTranspose_mul, hGM, conjTranspose_sub, conjTranspose_one,
      conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc, hJ2, Matrix.neg_mul, Matrix.smul_mul]
    abel
  rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2, sub_smul]
  abel

theorem star_cZero_inv (η : ℝ) :
    star ((2 * Complex.I * (η : ℂ))⁻¹) = -(2 * Complex.I * (η : ℂ))⁻¹ := by
  rw [star_inv₀, ← inv_neg]
  congr 1
  simp [Complex.conj_ofReal]

/-- **The Ward algebra** (near diagonal block of the full Ward identity). -/
theorem ward_algebra (G Gb K Y R Q : Matrix n n ℂ) {η : ℝ} (hη : η ≠ 0)
    (hG : G - Gᴴ = -((2 * Complex.I) • (G * Y * Gᴴ + (η : ℂ) • (Gb * Gbᴴ))))
    (hK : K - Kᴴ = (2 * Complex.I) • ((η : ℂ) • 1 + Y))
    (hKR : K * R = 1) (hR : R * Y * Rᴴ = (η : ℂ) • (Q * Qᴴ)) :
    K * Gb * (K * Gb)ᴴ + (K * G * K - K) * Q * ((K * G * K - K) * Q)ᴴ - 1 =
      (K * G * K - K) * (R - (2 * Complex.I * (η : ℂ))⁻¹ • 1) +
        (R - (2 * Complex.I * (η : ℂ))⁻¹ • 1)ᴴ * (K * G * K - K)ᴴ := by
  have he : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη
  set c₀ : ℂ := (2 * Complex.I * (η : ℂ))⁻¹ with hc₀
  have hc0 : star c₀ = -c₀ := star_cZero_inv η
  have hc2 : c₀ * (2 * Complex.I) = (η : ℂ)⁻¹ := by
    rw [hc₀]; field_simp
  set Δ := K * G * K - K with hΔ
  have hΔR : Δ * R = K * G - 1 := by
    rw [hΔ, Matrix.sub_mul, Matrix.mul_assoc (K * G) K R, hKR, Matrix.mul_one]
  have hP : Δ * Q * (Δ * Q)ᴴ = (η : ℂ)⁻¹ • ((K * G - 1) * Y * (K * G - 1)ᴴ) := by
    rw [← hΔR]
    have e : Δ * R * Y * (Δ * R)ᴴ = Δ * (R * Y * Rᴴ) * Δᴴ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [e, hR, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ he, one_smul]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have hdiff : Δ - Δᴴ = K * G * (K - Kᴴ) + K * (G - Gᴴ) * Kᴴ + (K - Kᴴ) * Gᴴ * Kᴴ -
      (K - Kᴴ) := by
    rw [hΔ]; simp only [conjTranspose_sub, conjTranspose_mul]; noncomm_ring
  set S : Matrix n n ℂ := K * G * ((η : ℂ) • 1 + Y) -
      K * (G * Y * Gᴴ + (η : ℂ) • (Gb * Gbᴴ)) * Kᴴ + ((η : ℂ) • 1 + Y) * Gᴴ * Kᴴ -
      ((η : ℂ) • 1 + Y) with hSdef
  have hS : Δ - Δᴴ = (2 * Complex.I) • S := by
    rw [hdiff, hK, hG, hSdef]
    simp only [mul_smul_comm, smul_mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add,
      Matrix.add_mul]
    module
  have hf : Δ * (R - c₀ • 1) + (R - c₀ • 1)ᴴ * Δᴴ = (K * G - 1) + (K * G - 1)ᴴ -
      c₀ • (Δ - Δᴴ) := by
    rw [← hΔR, conjTranspose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, conjTranspose_sub, conjTranspose_smul,
      conjTranspose_one, hc0, mul_smul_comm, smul_mul_assoc, Matrix.mul_one, Matrix.one_mul]
    module
  rw [hf, hS, smul_smul, hc2, hP, hSdef]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm,
    smul_mul_assoc, Matrix.mul_one, Matrix.one_mul, conjTranspose_sub, conjTranspose_mul,
    conjTranspose_one, Matrix.mul_assoc]
  linear_combination (norm := module) (inv_mul_cancel₀ he) • (K * G - K * (Gb * (Gbᴴ * Kᴴ)) +
    Gᴴ * Kᴴ - 1)

end BlockBand.SourceProcess.FullSource
