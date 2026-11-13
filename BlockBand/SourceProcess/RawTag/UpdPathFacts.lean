module

public import BlockBand.SourceProcess.RawTag.UpdAlgebra
public import BlockBand.SourceProcess.RawTag.Defs
public import BlockBand.Transmission.Bridge.Complete
public import BlockBand.SourceProcess.ComplexSourceLaw.Algebra
public import BlockBand.SourceProcess.FullSource.RightLetter

/-!
# The path inputs of the Schur step

For a sample with Hermitian blocks, invertible `H_l - E` and `Im z > 0`:
* `interior_eqs`: `(H - E - z⁻¹CC*)G₁₁ = 1` and `C*G₁₁ = -zG₂₁` (first block column of `𝓜G = 1`);
* `fullInverse_21_eq`: `G₂₁ = 𝕊𝒰*` (the boundary identity, from `G - G* = (z̄ - z)G P G*`);
* `boundary_eqs`: `(H - E - z⁻¹CC*)𝒰 = -z⁻¹C`, and `ι*C*𝒰ι = 1 - zR` with `R = (z - X_l)⁻¹`;
* `fresh_eq`: `(A - E - X - z⁻¹BB*)𝒢₁₁ = 1` for the fresh layer (the layer Schur inverse).
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

/-- The first block column of `𝓜G = 1`. -/
theorem interior_eqs (b E : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hM : IsUnit (fullPathMatrix b E W n ω)) :
    (pathMatrix (pathAt W n ω) - (E : ℂ) • 1) * (fullInverse b E W n ω).toBlocks₁₁ +
        pathPortCoupling (pathAt W n ω) * (fullInverse b E W n ω).toBlocks₂₁ = 1 ∧
      (pathPortCoupling (pathAt W n ω))ᴴ * (fullInverse b E W n ω).toBlocks₁₁ +
        boundaryZ b E • (fullInverse b E W n ω).toBlocks₂₁ = 0 := by
  have h := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)
  rw [← Matrix.fromBlocks_toBlocks (fullPathMatrix b E W n ω)⁻¹, fullPathMatrix,
    Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h
  refine ⟨h.1, ?_⟩
  have h3 := h.2.2.1
  rwa [Matrix.smul_mul, Matrix.one_mul] at h3

/-- **The boundary identity** `G₂₁ = 𝕊𝒰*`. -/
theorem fullInverse_21_eq (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (hA : ∀ k, (ω.1 k).IsHermitian) :
    (fullInverse b E W n ω).toBlocks₂₁ =
      scatteringMatrix b E W n ω * (boundaryToInterior b E W n ω)ᴴ := by
  have h := congrArg Matrix.toBlocks₂₁
    (BlockBand.SourceProcess.ComplexSourceLaw.fullInverse_sub_conjTranspose b E n ω hA)
  rw [toBlocks_fromBlocks₂₁, BlockBand.SourceProcess.ComplexSourceLaw.conj_boundaryZ_sub] at h
  have e1 : ((fullInverse b E W n ω)ᴴ).toBlocks₂₁ = (boundaryToInterior b E W n ω)ᴴ := by
    ext i j; simp [Matrix.toBlocks₂₁, boundaryToInterior, Matrix.toBlocks₁₂,
      Matrix.conjTranspose_apply]
  have e2 : (fullInverse b E W n ω - (fullInverse b E W n ω)ᴴ).toBlocks₂₁ =
      (fullInverse b E W n ω).toBlocks₂₁ - ((fullInverse b E W n ω)ᴴ).toBlocks₂₁ := by
    ext i j; simp [Matrix.toBlocks₂₁]
  rw [e2, e1, sub_eq_iff_eq_add] at h
  rw [h, scatteringMatrix, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  have : ((2 * etaZ b E : ℝ) : ℂ) * Complex.I = 2 * (etaZ b E : ℂ) * Complex.I := by push_cast; ring
  rw [this, neg_smul, sub_eq_add_neg, add_comm]

theorem nearSel_mul_mul_conjTranspose (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    nearSel W * M * (nearSel W)ᴴ = portBlock M 0 0 := by
  ext x y
  simp [nearSel, portBlock, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The boundary-map equations of the old path. -/
theorem boundary_eqs (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (hA : ∀ k, (ω.1 k).IsHermitian)
    (hη : 0 < (boundaryZ b E).im) (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)) :
    (pathMatrix (pathAt W n ω) - (E : ℂ) • 1 - (boundaryZ b E)⁻¹ •
        (pathPortCoupling (pathAt W n ω) * (pathPortCoupling (pathAt W n ω))ᴴ)) *
        boundaryToInterior b E W n ω =
      -((boundaryZ b E)⁻¹ • pathPortCoupling (pathAt W n ω)) ∧
    nearSel W * ((pathPortCoupling (pathAt W n ω))ᴴ * boundaryToInterior b E W n ω) *
        (nearSel W)ᴴ = 1 - boundaryZ b E • passiveResolvent b E (pathX b E W n ω) := by
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  obtain ⟨h1, h2⟩ := full_solution b E n ω (isUnit_fullPathMatrix b E n ω hA hη hF)
  set C := pathPortCoupling (pathAt W n ω)
  set U := boundaryToInterior b E W n ω
  set ℝ' := boundaryResolvent b E W n ω
  have hR : ℝ' = (boundaryZ b E)⁻¹ • (1 - Cᴴ * U) := by
    rw [← h2, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hz, one_smul]
  refine ⟨?_, ?_⟩
  · rw [hR] at h1
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
    have h1' := h1
    rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, smul_sub] at h1'
    rw [← sub_eq_zero]
    rw [← h1']; abel
  · have hX : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) -
        portBlock (pathSchur E (pathAt W n ω)) 1 1) := by
      have hXX := pathSchur_isHermitian E n ω hA
      exact BlockBand.Transmission.portPencil_isUnit _ (by
        ext x y; simpa [portBlock, Matrix.conjTranspose_apply] using
          congrFun (congrFun hXX (1, x)) (1, y)) hη
    have hRe : portBlock ℝ' 0 0 = passiveResolvent b E (pathX b E W n ω) := by
      simp only [ℝ']
      rw [boundaryResolvent_eq b E n ω hF, portBlock_twoPortResolvent_zero_zero b E _ hX,
        pathX_eq]
    have hCU : Cᴴ * U = 1 - boundaryZ b E • ℝ' := by rw [← h2]; abel
    rw [hCU, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, nearSel_mul_conjTranspose,
      Matrix.mul_smul, Matrix.smul_mul, nearSel_mul_mul_conjTranspose, hRe]

/-- **The fresh-layer equation** `(A - E - X - z⁻¹BB*)𝒢₁₁ = 1`. -/
theorem fresh_eq {b E : ℝ} (hη : 0 < (boundaryZ b E).im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    (ω.1 0 - (E : ℂ) • 1 - X - (boundaryZ b E)⁻¹ • (ω.2 0 0 * (ω.2 0 0)ᴴ)) *
      g11 E (boundaryZ b E) X ω = 1 := by
  obtain ⟨-, hres, -, -⟩ := layer_schur E hη hY hA hB
  have hg := g11_eq (E := E) (w := boundaryZ b E) (X := X) (ω := ω) hres
  have hS := isUnit_schurS E hη hY hA hB
  have hSS := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hS)
  have hsub : (schurS E (boundaryZ b E) X ω).submatrix embed0 embed0 =
      ω.1 0 - (E : ℂ) • 1 - X - (boundaryZ b E)⁻¹ • (ω.2 0 0 * (ω.2 0 0)ᴴ) := by
    ext x y
    simp [schurS, BlockBand.Internal.Contracts.Layers.blockDiag, liftX, bondL, bondMatrix,
      LayerShape.incident, embed0, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
  have hmul : ∀ N N' : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ,
      N.submatrix embed0 embed0 * N'.submatrix embed0 embed0 =
        (N * N').submatrix embed0 embed0 := by
    intro N N'
    ext x y
    simp [Matrix.mul_apply, embed0, Fintype.sum_prod_type, Subsingleton.elim _ (0 : Fin 1)]
  rw [hg, ← hsub, hmul, hSS]
  ext x y; simp [embed0, Matrix.one_apply]

end BlockBand.SourceProcess.RawTag
