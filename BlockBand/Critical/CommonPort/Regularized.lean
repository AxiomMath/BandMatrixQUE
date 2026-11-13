module

public import BlockBand.Critical.CommonPort.Algebra
public import BlockBand.Layers.TraceFluctuation

/-!
# Common-port mean: weighted bounds for the regularized common port

Deterministic; no measure. Domain: every sample `ω`, deterministic `X`, real `e`, `b`, and
`κ ∈ ℝ` with `IsUnit (tflReg κ M).det`, `M = layerMatrix .common e z₀ X ω`, and
`z₀ + iκ ≠ 0`. Norms: `ℓ²` operator norms. Notation: `κ` in this file is the regularization
height, not the bulk-energy margin of `bulkInterval κ`.

* `norm_schur_weighted_G11_le`, `norm_schur_weighted_G12_le`: generic weighted Schur bounds
  `‖(S + D)𝒢₁₁‖ ≤ 1 + (‖S‖ + |z|⁻¹‖Bm‖²)‖𝒢‖`,
  `‖(S + D)𝒢₁₂‖ ≤ |z|⁻¹ (1 + (‖S‖ + |z|⁻¹‖Bm‖²)‖𝒢‖)‖Bm‖`.
* `tflReg_layerMatrix_common`: `tflReg κ M = [[D + iκ, Bm], [Bmᴴ, (z₀ + iκ) I]]`.
* `norm_K_regG11_le`, `norm_K_regG12_le`: the same bounds for `𝒢_κ = (tflReg κ M)⁻¹`, with
  `S = (z_b + e - iκ) I - blockDiag A`, `K = z_b I - X = S + D + iκ`.
* `topRows`, `topRows_eq`, `norm_mul_topRows_le`: `‖K · topRows 𝒢‖ ≤ ‖K 𝒢₁₁‖ + ‖K 𝒢₁₂‖`
  (any square block matrix `𝒢`, any `K`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open Matrix BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped Matrix.Norms.L2Operator

section Generic

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `‖S + z⁻¹ Bm Bmᴴ‖ ≤ ‖S‖ + |z|⁻¹ ‖Bm‖²`. -/
theorem norm_weight_le (S : Matrix n n ℂ) (Bm : Matrix n m ℂ) (z : ℂ) :
    ‖S + z⁻¹ • (Bm * Bmᴴ)‖ ≤ ‖S‖ + ‖z‖⁻¹ * ‖Bm‖ ^ 2 := by
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, norm_inv, sq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (l2_opNorm_mul _ _).trans (le_of_eq (by rw [l2_opNorm_conjTranspose]))

/-- **Weighted Schur bound, top block.** -/
theorem norm_schur_weighted_G11_le (S D : Matrix n n ℂ) (Bm : Matrix n m ℂ) {z : ℂ}
    (hz : z ≠ 0) (hM : IsUnit (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ))).det) :
    ‖(S + D) * (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₁₁‖ ≤
      1 + (‖S‖ + ‖z‖⁻¹ * ‖Bm‖ ^ 2) * ‖(fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹‖ := by
  rw [schur_weighted_G11 S D Bm hz hM]
  set G := (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹
  refine (norm_add_le _ _).trans (add_le_add BlockBand.Layers.lct_norm_one_le ?_)
  exact (l2_opNorm_mul _ _).trans (mul_le_mul (norm_weight_le S Bm z) (norm_toBlocks11_le G)
    (norm_nonneg _) (by positivity))

/-- **Weighted Schur bound, off-diagonal block.** -/
theorem norm_schur_weighted_G12_le (S D : Matrix n n ℂ) (Bm : Matrix n m ℂ) {z : ℂ}
    (hz : z ≠ 0) (hM : IsUnit (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ))).det) :
    ‖(S + D) * (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₁₂‖ ≤
      ‖z‖⁻¹ * (1 + (‖S‖ + ‖z‖⁻¹ * ‖Bm‖ ^ 2) *
        ‖(fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹‖) * ‖Bm‖ := by
  rw [schur_weighted_G12 S D Bm hz hM, norm_smul, norm_neg, norm_inv, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((l2_opNorm_mul _ _).trans ?_) (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [← schur_weighted_G11 S D Bm hz hM]
  exact norm_schur_weighted_G11_le S D Bm hz hM

omit [Fintype n] [Fintype m] in
/-- Shift of a block matrix by a scalar: `[[D, B], [Bᴴ, z]] + c = [[D + c, B], [Bᴴ, z + c]]`. -/
theorem fromBlocks_add_smul_one (D : Matrix n n ℂ) (Bm : Matrix n m ℂ) (z c : ℂ) :
    fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)) + c • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) =
      fromBlocks (D + c • 1) Bm Bmᴴ ((z + c) • (1 : Matrix m m ℂ)) := by
  rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  simp only [smul_zero, add_zero, add_smul]

end Generic

section CommonPort

variable {W : ℕ}

/-- **The regularized common-port matrix** `tflReg κ M = M + iκ` in block form. -/
theorem tflReg_layerMatrix_common (e : ℝ) (z : ℂ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) (κ : ℝ) :
    BlockBand.Layers.tflReg κ (layerMatrix .common e z X ω) =
      fromBlocks (Internal.Contracts.Layers.blockDiag ω.1 - (e : ℂ) • 1 - X +
          ((κ : ℂ) * Complex.I) • 1) (bondMatrix .common ω.2) (bondMatrix .common ω.2)ᴴ
        ((z + (κ : ℂ) * Complex.I) • 1) := by
  unfold BlockBand.Layers.tflReg layerMatrix
  exact fromBlocks_add_smul_one _ _ _ _

/-- The regularized weight `S_κ = (z_b + e - iκ) I - blockDiag A`, so `K = S_κ + D + iκ`. -/
def regShift (b e κ : ℝ) (ω : LayerSample W .common) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (boundaryZ b e + (e : ℂ) - (κ : ℂ) * Complex.I) •
    (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Internal.Contracts.Layers.blockDiag ω.1

theorem matchedLeadK_eq_reg (b e κ : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) :
    matchedLeadK b e X = regShift b e κ ω +
      (Internal.Contracts.Layers.blockDiag ω.1 - (e : ℂ) • 1 - X + ((κ : ℂ) * Complex.I) • 1) := by
  unfold matchedLeadK regShift
  rw [sub_smul, add_smul]
  abel

/-- `‖S_κ‖ ≤ |z_b + e| + |κ| + ‖blockDiag A‖`. -/
theorem norm_regShift_le (b e κ : ℝ) (ω : LayerSample W .common) :
    ‖regShift b e κ ω‖ ≤ ‖boundaryZ b e + (e : ℂ)‖ + |κ| +
      ‖Internal.Contracts.Layers.blockDiag ω.1‖ := by
  unfold regShift
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  rw [norm_smul]
  refine (mul_le_mul_of_nonneg_left BlockBand.Layers.lct_norm_one_le (norm_nonneg _)).trans ?_
  rw [mul_one]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The regularized resolvent `𝒢_κ = (𝒢⁻¹ + iκ)⁻¹`. -/
def regResolvent (e : ℝ) (z : ℂ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ)
    (ω : LayerSample W .common) : Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
  (BlockBand.Layers.tflReg κ (layerMatrix .common e z X ω))⁻¹

/-- **`‖K 𝒢_κ,₁₁‖`**: on `IsUnit (tflReg κ M).det` and `z₀ + iκ ≠ 0`,
`‖K 𝒢_κ,₁₁‖ ≤ 1 + (‖S_κ‖ + |z₀ + iκ|⁻¹ ‖Bm‖²) ‖𝒢_κ‖`. -/
theorem norm_K_regG11_le (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ)
    (ω : LayerSample W .common) (hz : commonZ b e + (κ : ℂ) * Complex.I ≠ 0)
    (hM : IsUnit (BlockBand.Layers.tflReg κ (layerMatrix .common e (commonZ b e) X ω)).det) :
    ‖matchedLeadK b e X * (regResolvent e (commonZ b e) X κ ω).toBlocks₁₁‖ ≤
      1 + (‖regShift b e κ ω‖ + ‖commonZ b e + (κ : ℂ) * Complex.I‖⁻¹ *
        ‖bondMatrix .common ω.2‖ ^ 2) * ‖regResolvent e (commonZ b e) X κ ω‖ := by
  unfold regResolvent
  rw [tflReg_layerMatrix_common] at hM ⊢
  rw [matchedLeadK_eq_reg b e κ X ω]
  exact norm_schur_weighted_G11_le _ _ _ hz hM

/-- **`‖K 𝒢_κ,₁₂‖`**: same domain,
`‖K 𝒢_κ,₁₂‖ ≤ |z₀ + iκ|⁻¹ (1 + (‖S_κ‖ + |z₀ + iκ|⁻¹ ‖Bm‖²) ‖𝒢_κ‖) ‖Bm‖`. -/
theorem norm_K_regG12_le (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ)
    (ω : LayerSample W .common) (hz : commonZ b e + (κ : ℂ) * Complex.I ≠ 0)
    (hM : IsUnit (BlockBand.Layers.tflReg κ (layerMatrix .common e (commonZ b e) X ω)).det) :
    ‖matchedLeadK b e X * (regResolvent e (commonZ b e) X κ ω).toBlocks₁₂‖ ≤
      ‖commonZ b e + (κ : ℂ) * Complex.I‖⁻¹ *
        (1 + (‖regShift b e κ ω‖ + ‖commonZ b e + (κ : ℂ) * Complex.I‖⁻¹ *
          ‖bondMatrix .common ω.2‖ ^ 2) * ‖regResolvent e (commonZ b e) X κ ω‖) *
        ‖bondMatrix .common ω.2‖ := by
  unfold regResolvent
  rw [tflReg_layerMatrix_common] at hM ⊢
  rw [matchedLeadK_eq_reg b e κ X ω]
  exact norm_schur_weighted_G12_le _ _ _ hz hM

end CommonPort

section TopRows

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The physical rows of a square block matrix (`n × (n ⊕ m)`). -/
def topRows (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) : Matrix n (n ⊕ m) ℂ := G.submatrix Sum.inl id

theorem topRows_eq (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    topRows G = G.toBlocks₁₁ * selectMatrix (Sum.inl : n → n ⊕ m) +
      G.toBlocks₁₂ * selectMatrix (Sum.inr : m → n ⊕ m) := by
  ext x y
  rcases y with y | y <;>
    simp [topRows, Matrix.mul_apply, selectMatrix, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

/-- `‖K · topRows 𝒢‖ ≤ ‖K 𝒢₁₁‖ + ‖K 𝒢₁₂‖`. -/
theorem norm_mul_topRows_le (K : Matrix n n ℂ) (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    ‖K * topRows G‖ ≤ ‖K * G.toBlocks₁₁‖ + ‖K * G.toBlocks₁₂‖ := by
  rw [topRows_eq, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have h1 := norm_le_one_of_mul_conjTranspose _
    (selectMatrix_mul_conjTranspose (Sum.inl_injective : Function.Injective (Sum.inl : n → n ⊕ m)))
  have h2 := norm_le_one_of_mul_conjTranspose _
    (selectMatrix_mul_conjTranspose (Sum.inr_injective : Function.Injective (Sum.inr : m → n ⊕ m)))
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (l2_opNorm_mul _ _).trans
      ((mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (le_of_eq (mul_one _)))
  · exact (l2_opNorm_mul _ _).trans
      ((mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans (le_of_eq (mul_one _)))

end TopRows

end BlockBand.Critical.CommonPort
