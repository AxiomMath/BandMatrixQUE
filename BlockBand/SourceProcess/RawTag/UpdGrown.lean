module

public import BlockBand.SourceProcess.RawTag.UpdPath

/-!
# The interior inverse of the grown path: `grown_G_eq`

`grown_G_eq`: for Hermitian blocks, invertible pencils at lengths `l` and `l + 1`, a passive near
Schur matrix and an invertible new bond, the interior inverse of the path of length `l + 1`, in
`headEquiv` coordinates, is given in block form by the interior inverse at length `l`, the fresh
layer and `R = (z - X_l)⁻¹`.
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

/-- **The grown interior inverse** in `headEquiv` coordinates. -/
theorem grown_G_eq (b E : ℝ) {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W l ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (l + 1) ω) - (E : ℂ) • 1))
    (hY : (passiveY (pathX b E W l ω)).PosSemidef) (hB : IsUnit (ω.2 (l + 1))) :
    (fullInverse b E W (l + 1) ω).toBlocks₁₁.submatrix (headEquiv l W) (headEquiv l W) =
      fromBlocks (g11 E (boundaryZ b E) (pathX b E W l ω) (freshSample W l ω))
        (g11 E (boundaryZ b E) (pathX b E W l ω) (freshSample W l ω) *
          (boundaryZ b E • 1 - pathX b E W l ω) *
          (nearSel W * (scatteringMatrix b E W l ω * (boundaryToInterior b E W l ω)ᴴ)))
        (boundaryToInterior b E W l ω * (nearSel W)ᴴ * ((boundaryZ b E • 1 - pathX b E W l ω) *
          g11 E (boundaryZ b E) (pathX b E W l ω) (freshSample W l ω)))
        ((fullInverse b E W l ω).toBlocks₁₁ + boundaryToInterior b E W l ω * (nearSel W)ᴴ *
          ((boundaryZ b E • 1 - pathX b E W l ω) *
            g11 E (boundaryZ b E) (pathX b E W l ω) (freshSample W l ω) *
            (boundaryZ b E • 1 - pathX b E W l ω) - (boundaryZ b E • 1 - pathX b E W l ω)) *
          (nearSel W * (scatteringMatrix b E W l ω * (boundaryToInterior b E W l ω)ᴴ))) := by
  set z := boundaryZ b E
  have hz : z ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  set X := pathX b E W l ω
  set 𝒢 := g11 E z X (freshSample W l ω)
  set U := boundaryToInterior b E W l ω
  set S := scatteringMatrix b E W l ω
  set nc := nearCol W l ω
  set f := farCoupling W l ω
  set ns := nearSel W
  set HO := pathMatrix (pathAt W l ω) - (E : ℂ) • 1
  have hC : pathPortCoupling (pathAt W l ω) = nc * ns + f := coupling_split l ω
  have hM := isUnit_fullPathMatrix b E l ω hA hη hF
  -- old path
  have hG := interior_pencil_mul b E l ω hM hz
  rw [hC] at hG
  have hV : (nc * ns + f)ᴴ * (fullInverse b E W l ω).toBlocks₁₁ = -(z • (S * Uᴴ)) := by
    obtain ⟨-, h2⟩ := interior_eqs b E l ω hM
    rw [hC, add_eq_zero_iff_eq_neg] at h2
    rw [h2, fullInverse_21_eq b E l ω hA]
  obtain ⟨hU, hd⟩ := boundary_eqs b E l ω hA hη hF
  rw [hC] at hU hd
  have hnsC : ns * (nc * ns + f)ᴴ = ncᴴ := by
    rw [conjTranspose_add, conjTranspose_mul, Matrix.mul_add, ← Matrix.mul_assoc,
      nearSel_mul_conjTranspose, Matrix.one_mul, nearSel_mul_farCoupling, add_zero]
  have hd' : ncᴴ * (U * nsᴴ) = 1 - z • passiveResolvent b E X := by
    rw [← hd, ← hnsC, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  obtain ⟨F1, F2, F3⟩ := old_facts z hz HO nc f ns (nearSel_mul_farCoupling l ω)
    nearSel_mul_conjTranspose _ U (S * Uᴴ) (passiveResolvent b E X) hG hV hU hd'
  -- fresh layer and `R`
  have hK := (isUnit_iff_isUnit_det _).mp
    (BlockBand.SourceProcess.TagBirth.isUnit_pencil (b := b) (E := E) hη hY)
  have hRK : passiveResolvent b E X * (z • 1 - X) = 1 := Matrix.nonsing_inv_mul _ hK
  have hf := fresh_eq (b := b) (E := E) hη hY (ω := freshSample W l ω) (hA l) hB
  set A'' := ω.1 l - (E : ℂ) • 1 - z⁻¹ • (ω.2 (l + 1) * (ω.2 (l + 1))ᴴ)
  have hF5 : A'' * 𝒢 = 1 + X * 𝒢 := by
    have : A'' = (ω.1 l - (E : ℂ) • 1 - X - z⁻¹ • (ω.2 (l + 1) * (ω.2 (l + 1))ᴴ)) + X := by
      simp only [A'']; abel
    rw [this, Matrix.add_mul]
    exact congrArg (· + X * 𝒢) hf
  have hR := grown_interior_mul z (HO - z⁻¹ • (f * fᴴ)) nc (fullInverse b E W l ω).toBlocks₁₁
    (U * nsᴴ) (ns * (S * Uᴴ)) X (passiveResolvent b E X) A'' 𝒢 F1 F2 F3 hd' hF5 hRK hz
  -- new path
  have hM' := isUnit_fullPathMatrix b E (l + 1) ω hA hη hF'
  have hG' := interior_pencil_mul b E (l + 1) ω hM' hz
  have hQ : (pathMatrix (pathAt W (l + 1) ω) - (E : ℂ) • 1 - z⁻¹ •
      (pathPortCoupling (pathAt W (l + 1) ω) * (pathPortCoupling (pathAt W (l + 1) ω))ᴴ)).submatrix
        (headEquiv l W) (headEquiv l W) = fromBlocks A'' ncᴴ nc (HO - z⁻¹ • (f * fᴴ)) := by
    have e1 : ∀ (P Q : Matrix (Fin (l + 1) × Fin W) (Fin (l + 1) × Fin W) ℂ),
        (P - z⁻¹ • Q).submatrix (headEquiv l W) (headEquiv l W) =
          P.submatrix (headEquiv l W) (headEquiv l W) -
            z⁻¹ • Q.submatrix (headEquiv l W) (headEquiv l W) := fun _ _ => rfl
    rw [e1, pathMatrix_succ_submatrix, coupling_sq_succ hl, fromBlocks_smul, sub_eq_add_neg,
      fromBlocks_neg, fromBlocks_add]
    congr 1 <;> simp [nc]
  have hG'e := congrArg (fun M => M.submatrix (headEquiv l W) (headEquiv l W)) hG'
  rw [← submatrix_mul_equiv _ _ (headEquiv l W) (headEquiv l W) (headEquiv l W), hQ,
    submatrix_one_equiv] at hG'e
  have h1 := Matrix.inv_eq_right_inv hR
  have h2 := Matrix.inv_eq_right_inv hG'e
  rw [← h2, h1]

end BlockBand.SourceProcess.RawTag
