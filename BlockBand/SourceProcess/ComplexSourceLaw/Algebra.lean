module

public import BlockBand.SourceProcess.ComplexSourceLaw.Measurability
public import BlockBand.Transmission.Bridge.Passive

/-!
# The resolvent imaginary-part identity and unitarity of `𝕊`

For `G = 𝓜⁻¹`,
`G - Gᴴ = G(𝓜ᴴ - 𝓜)Gᴴ` (both sides vanish if `𝓜` is singular); for Hermitian path blocks
`𝓜ᴴ - 𝓜 = diag(0, (z̄ - z)I)`, so

* `G₁₁ - G₁₁ᴴ = (z̄ - z) 𝒰𝒰ᴴ` and `𝒦 - 𝒦ᴴ = (z̄ - z) M_pr` (`kc_sub_conjTranspose`);
* `ℝ - ℝᴴ = (z̄ - z) ℝℝᴴ`, hence `𝕊𝕊ᴴ = 1 = 𝕊ᴴ𝕊` (`scattering_mul_conjTranspose`,
  `conjTranspose_mul_scattering`).
No invertibility of the interior pencil is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Bridge
open scoped ComplexConjugate

/-- `G - Gᴴ = G(Mᴴ - M)Gᴴ` for `G = M⁻¹`. -/
theorem inv_sub_conjTranspose_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    M⁻¹ - (M⁻¹)ᴴ = M⁻¹ * (Mᴴ - M) * (M⁻¹)ᴴ := by
  by_cases h : IsUnit M.det
  · have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M h
    have h2 : Mᴴ * (M⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, conjTranspose_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, h1, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit M h]
    simp

variable {W : ℕ}

/-- `𝓜ᴴ - 𝓜 = diag(0, (z̄ - z)I)` for Hermitian path blocks. -/
theorem fullPathMatrix_conjTranspose_sub (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    (fullPathMatrix b E W n ω)ᴴ - fullPathMatrix b E W n ω =
      fromBlocks 0 0 0 ((conj (boundaryZ b E) - boundaryZ b E) • 1) := by
  have hH := pathMatrix_pathAt_isHermitian n ω hA
  rw [fullPathMatrix, fromBlocks_conjTranspose, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  congr 1
  · rw [conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
    abel
  · simp
  · simp
  · rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, sub_smul, sub_eq_add_neg]

/-- The block form of `G(diag(0, cI))Gᴴ`. -/
theorem mul_portDiag_mul {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]
    (G : Matrix (m ⊕ p) (m ⊕ p) ℂ) (c : ℂ) :
    G * fromBlocks 0 0 0 (c • 1) * Gᴴ =
      fromBlocks (c • (G.toBlocks₁₂ * G.toBlocks₁₂ᴴ)) (c • (G.toBlocks₁₂ * G.toBlocks₂₂ᴴ))
        (c • (G.toBlocks₂₂ * G.toBlocks₁₂ᴴ)) (c • (G.toBlocks₂₂ * G.toBlocks₂₂ᴴ)) := by
  conv_lhs => rw [← fromBlocks_toBlocks G]
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [Matrix.mul_smul, Matrix.smul_mul]

/-- `G - Gᴴ` in block form, for Hermitian path blocks. -/
theorem fullInverse_sub_conjTranspose (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    fullInverse b E W n ω - (fullInverse b E W n ω)ᴴ =
      fromBlocks ((conj (boundaryZ b E) - boundaryZ b E) •
          (boundaryToInterior b E W n ω * (boundaryToInterior b E W n ω)ᴴ))
        ((conj (boundaryZ b E) - boundaryZ b E) •
          (boundaryToInterior b E W n ω * (boundaryResolvent b E W n ω)ᴴ))
        ((conj (boundaryZ b E) - boundaryZ b E) •
          (boundaryResolvent b E W n ω * (boundaryToInterior b E W n ω)ᴴ))
        ((conj (boundaryZ b E) - boundaryZ b E) •
          (boundaryResolvent b E W n ω * (boundaryResolvent b E W n ω)ᴴ)) := by
  rw [fullInverse, inv_sub_conjTranspose_inv, fullPathMatrix_conjTranspose_sub b E n ω hA,
    mul_portDiag_mul]
  rfl

/-- `G₁₁ - G₁₁ᴴ = (z̄ - z)𝒰𝒰ᴴ`. -/
theorem interior_sub_conjTranspose (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    (fullInverse b E W n ω).toBlocks₁₁ - ((fullInverse b E W n ω).toBlocks₁₁)ᴴ =
      (conj (boundaryZ b E) - boundaryZ b E) •
        (boundaryToInterior b E W n ω * (boundaryToInterior b E W n ω)ᴴ) := by
  have h := congrArg Matrix.toBlocks₁₁ (fullInverse_sub_conjTranspose b E n ω hA)
  rw [toBlocks_fromBlocks₁₁] at h
  rw [← h]
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.conjTranspose_apply]

/-- `ℝ - ℝᴴ = (z̄ - z)ℝℝᴴ`. -/
theorem resolvent_sub_conjTranspose (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    boundaryResolvent b E W n ω - (boundaryResolvent b E W n ω)ᴴ =
      (conj (boundaryZ b E) - boundaryZ b E) •
        (boundaryResolvent b E W n ω * (boundaryResolvent b E W n ω)ᴴ) := by
  have h := congrArg Matrix.toBlocks₂₂ (fullInverse_sub_conjTranspose b E n ω hA)
  rw [toBlocks_fromBlocks₂₂] at h
  rw [← h]
  ext i j
  simp [boundaryResolvent, Matrix.toBlocks₂₂, Matrix.conjTranspose_apply]

theorem conj_boundaryZ_sub (b E : ℝ) :
    conj (boundaryZ b E) - boundaryZ b E = -(2 * (etaZ b E : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp
  · simp [etaZ]; ring

/-- `(1 - eR)(1 - eR)ᴴ = 1` when `ē = -e` and `R - Rᴴ = -e RRᴴ`. -/
theorem one_sub_smul_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (R : Matrix ι ι ℂ) (e : ℂ)
    (he : star e = -e) (h : R - Rᴴ = (-e) • (R * Rᴴ)) : (1 - e • R) * (1 - e • R)ᴴ = 1 := by
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, he, neg_smul, sub_neg_eq_add]
  have expand : (1 - e • R) * (1 + e • Rᴴ) = 1 - e • (R - Rᴴ) - (e * e) • (R * Rᴴ) := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, smul_sub]
    abel
  rw [expand, h, smul_smul, mul_neg, neg_smul, sub_neg_eq_add, add_sub_cancel_right]

/-- **`𝕊` is unitary** for Hermitian path blocks (`𝕊𝕊ᴴ = 1`). -/
theorem scattering_mul_conjTranspose (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1 := by
  have h := resolvent_sub_conjTranspose b E n ω hA
  rw [conj_boundaryZ_sub] at h
  have hS : scatteringMatrix b E W n ω =
      1 - (2 * (etaZ b E : ℂ) * Complex.I) • boundaryResolvent b E W n ω := by
    rw [scatteringMatrix]; congr 2; push_cast; ring
  rw [hS]
  exact one_sub_smul_unitary _ _ (by simp) h

theorem conjTranspose_mul_scattering (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    (scatteringMatrix b E W n ω)ᴴ * scatteringMatrix b E W n ω = 1 :=
  mul_eq_one_comm.mp (scattering_mul_conjTranspose b E n ω hA)

end BlockBand.SourceProcess.ComplexSourceLaw
