module

public import BlockBand.Transmission.PassiveCovariance.ResolventBound
public import BlockBand.Transmission.SchurDerivative

/-!
# Smoothness of the fresh layer at strictly passive inputs (gap 4, first part)

* `posDef_fromBlocks_diag`, `matrixImaginaryPart_fromBlocks_adj`, `posDef_liftX`: block
  positivity.
* `isUnit_layerMatrix_strict`: if `Y = -Im X ≻ 0` and `η > 0`, the layer matrix
  `[[A - E - X, B], [B*, z]]` is invertible at **every** sample with Hermitian `A`, because its
  imaginary part is `diag(Y, η) ≻ 0`. This is the support of `layerLaw`, and the reason for the
  regularization `PassiveCovariance.regX`.
* `layerMatrix_add_smul`, `hasDerivAt_layerResolvent`: the layer matrix is affine in the
  sample (`layerLin`), and at an invertible point `d/ds 𝒢(ω + sΔ)|₀ = -𝒢 (layerLin Δ) 𝒢`
  (from `affineInverse_hasDerivAt`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open BlockBand.Transmission BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
theorem posDef_fromBlocks_diag {P : Matrix m m ℂ} {Q : Matrix n n ℂ} (hP : P.PosDef)
    (hQ : Q.PosDef) : (fromBlocks P 0 0 Q).PosDef := by
  have hP0 := hP.posSemidef.dotProduct_mulVec_nonneg
  have hQ0 := hQ.posSemidef.dotProduct_mulVec_nonneg
  rw [posDef_iff_dotProduct_mulVec] at hP hQ ⊢
  refine ⟨IsHermitian.fromBlocks hP.1 (by simp) hQ.1, fun x hx => ?_⟩
  have key : star x ⬝ᵥ (fromBlocks P 0 0 Q *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (P *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (Q *ᵥ (x ∘ Sum.inr)) := by
    conv_lhs => rw [← Sum.elim_comp_inl_inr x]
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, zero_add]
    rw [show star (Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr)) =
      Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) by ext i; cases i <;> rfl]
    exact sumElim_dotProduct_sumElim _ _ _ _
  rw [key]
  by_cases h1 : x ∘ Sum.inl = 0
  · have h2 : x ∘ Sum.inr ≠ 0 := by
      intro h2; apply hx; rw [← Sum.elim_comp_inl_inr x, h1, h2]; ext i; cases i <;> rfl
    exact add_pos_of_nonneg_of_pos (hP0 _) (hQ.2 h2)
  · exact add_pos_of_pos_of_nonneg (hP.2 h1) (hQ0 _)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem matrixImaginaryPart_fromBlocks_adj (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ) :
    matrixImaginaryPart (fromBlocks A B Bᴴ D) =
      fromBlocks (matrixImaginaryPart A) 0 0 (matrixImaginaryPart D) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [matrixImaginaryPart, fromBlocks_conjTranspose]

theorem posDef_liftX {W : ℕ} {Y : Matrix (Fin W) (Fin W) ℂ} (hY : Y.PosDef) :
    (Matrix.of fun (u v : Fin 1 × Fin W) => Y u.2 v.2).PosDef := by
  have e : (Matrix.of fun (u v : Fin 1 × Fin W) => Y u.2 v.2) =
      Y.submatrix (Equiv.uniqueProd (Fin W) (Fin 1)) (Equiv.uniqueProd (Fin W) (Fin 1)) := by
    ext u v; rfl
  rw [e]
  exact hY.submatrix (Equiv.injective _)

/-- **Strictly passive inputs give an everywhere-invertible layer** (at Hermitian `A`). -/
theorem isUnit_layerMatrix_strict {W : ℕ} {b E : ℝ} (hη : 0 < etaZ b E)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosDef) (ω : LayerSample W .oneBlockOnePort)
    (hA : (ω.1 0).IsHermitian) :
    IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  rw [layerMatrix, matrixImaginaryPart_fromBlocks_adj]
  refine posDef_fromBlocks_diag ?_ ?_
  · have hBD : (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)).IsHermitian := by
      refine IsHermitian.sub ?_ ?_
      · ext u v
        simp only [conjTranspose_apply, BlockBand.Internal.Contracts.Layers.blockDiag]
        have hu : u.1 = 0 := Subsingleton.elim _ _
        have hv : v.1 = 0 := Subsingleton.elim _ _
        simp only [hu, hv, ite_true]
        have h := congrFun (congrFun hA u.2) v.2
        simpa [conjTranspose_apply] using h
      · exact isHermitian_one.smul (Complex.conj_ofReal E)
    have h0 : matrixImaginaryPart (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 -
        (E : ℂ) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)) = 0 := by
      rw [matrixImaginaryPart, hBD.eq, sub_self, smul_zero]
    rw [matrixImaginaryPart_sub, h0, zero_sub]
    have hl : -matrixImaginaryPart (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) =
        Matrix.of fun (u v : Fin 1 × Fin W) => passiveY X u.2 v.2 := by
      ext u v; simp [matrixImaginaryPart, passiveY]
    rw [hl]
    exact posDef_liftX hY
  · have h := matrixImaginaryPart_portPencil (0 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)
      isHermitian_zero (boundaryZ b E)
    simp only [portPencil, sub_zero] at h
    rw [h]
    exact Matrix.PosDef.one.smul hη

/-- The linear part of the layer matrix in the Gaussian sample. -/
def layerLin {W : ℕ} (Δ : LayerSample W .oneBlockOnePort) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks (BlockBand.Internal.Contracts.Layers.blockDiag Δ.1) (bondMatrix .oneBlockOnePort Δ.2)
    (bondMatrix .oneBlockOnePort Δ.2)ᴴ 0

theorem layerMatrix_add_smul {W : ℕ} (E : ℝ) (z : ℂ)
    (X' : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) (ω Δ : LayerSample W .oneBlockOnePort) (s : ℝ) :
    layerMatrix .oneBlockOnePort E z X' (ω + (s : ℂ) • Δ) =
      layerMatrix .oneBlockOnePort E z X' ω + (s : ℂ) • layerLin Δ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp only [layerMatrix, layerLin, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix, conjTranspose_apply,
      Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.zero_apply]
  all_goals (try split_ifs)
  all_goals (try simp [star_add, star_mul', Complex.conj_ofReal])
  all_goals (try ring)

/-- **Directional derivative of the layer resolvent** at an invertible point:
`d/ds 𝒢(ω + sΔ)|₀ = -𝒢 (layerLin Δ) 𝒢`. -/
theorem hasDerivAt_layerResolvent {W : ℕ} (E : ℝ) (z : ℂ)
    (X' : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) (ω Δ : LayerSample W .oneBlockOnePort)
    (hω : IsUnit (layerMatrix .oneBlockOnePort E z X' ω)) :
    HasDerivAt (fun s : ℝ => layerResolvent .oneBlockOnePort E z X' (ω + (s : ℂ) • Δ))
      (-(layerResolvent .oneBlockOnePort E z X' ω * layerLin Δ *
        layerResolvent .oneBlockOnePort E z X' ω)) 0 := by
  have hc := affineInverse_hasDerivAt (layerMatrix .oneBlockOnePort E z X' ω) (layerLin Δ)
    ((0 : ℝ) : ℂ) (by simpa using hω)
  have hr := hc.scomp (0 : ℝ) (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_zero, zero_smul, add_zero,
    Complex.ofReal_one, one_smul] at hr
  refine hr.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [layerResolvent, Function.comp_apply]
  exact congrArg _ (layerMatrix_add_smul E z X' ω Δ s)

end BlockBand.Transmission.PassiveCovariance
