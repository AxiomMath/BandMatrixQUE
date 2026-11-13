module

public import BlockBand.SourceProcess.RawTag.UpdPathFacts
public import BlockBand.SourceProcess.TagBirth.FreshTrace

/-!
# The interior pencil of the path

`interior_pencil_mul`: the interior inverse `G₁₁` inverts the interior pencil,
`(H - E - z⁻¹CC*)G₁₁ = 1`; `coupling_sq_succ`: in `headEquiv` coordinates, `CC*` of the path of
length `l + 1` is block diagonal, with the new bond `BB*` and the far coupling of the path of length
`l`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open scoped Matrix ComplexOrder

variable {W : ℕ}

/-- `(H - E - z⁻¹CC*)G₁₁ = 1`. -/
theorem interior_pencil_mul (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hM : IsUnit (fullPathMatrix b E W n ω)) (hz : boundaryZ b E ≠ 0) :
    (pathMatrix (pathAt W n ω) - (E : ℂ) • 1 - (boundaryZ b E)⁻¹ •
        (pathPortCoupling (pathAt W n ω) * (pathPortCoupling (pathAt W n ω))ᴴ)) *
      (fullInverse b E W n ω).toBlocks₁₁ = 1 := by
  obtain ⟨h1, h2⟩ := interior_eqs b E n ω hM
  have h21 : (fullInverse b E W n ω).toBlocks₂₁ = -((boundaryZ b E)⁻¹ •
      ((pathPortCoupling (pathAt W n ω))ᴴ * (fullInverse b E W n ω).toBlocks₁₁)) := by
    rw [add_eq_zero_iff_eq_neg'] at h2
    rw [← smul_neg, ← h2, smul_smul, inv_mul_cancel₀ hz, one_smul]
  rw [h21, Matrix.mul_neg, Matrix.mul_smul, ← sub_eq_add_neg, ← Matrix.mul_assoc] at h1
  rw [Matrix.sub_mul, Matrix.smul_mul]; exact h1

theorem coupling_sq_succ {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W) :
    (pathPortCoupling (pathAt W (l + 1) ω) * (pathPortCoupling (pathAt W (l + 1) ω))ᴴ).submatrix
        (headEquiv l W) (headEquiv l W) =
      fromBlocks (ω.2 (l + 1) * (ω.2 (l + 1))ᴴ) 0 0 (farCoupling W l ω * (farCoupling W l ω)ᴴ) := by
  have e1 : (pathPortCoupling (pathAt W (l + 1) ω) *
      (pathPortCoupling (pathAt W (l + 1) ω))ᴴ).submatrix (headEquiv l W) (headEquiv l W) =
      (pathPortCoupling (pathAt W (l + 1) ω)).submatrix (headEquiv l W) id *
        ((pathPortCoupling (pathAt W (l + 1) ω)).submatrix (headEquiv l W) id)ᴴ := by
    rw [conjTranspose_submatrix, submatrix_mul _ _ _ _ _ Function.bijective_id]
  have hfn : farCoupling W l ω * (nearSel W)ᴴ = 0 := by
    have := congrArg conjTranspose (nearSel_mul_farCoupling (W := W) l ω)
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
  rw [e1, coupling_succ_submatrix hl, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromRows_mul_fromCols]
  congr 1
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (nearSel W),
      nearSel_mul_conjTranspose, Matrix.one_mul]
  · rw [Matrix.mul_assoc, nearSel_mul_farCoupling, Matrix.mul_zero]
  · rw [conjTranspose_mul, ← Matrix.mul_assoc, hfn, Matrix.zero_mul]

end BlockBand.SourceProcess.RawTag
