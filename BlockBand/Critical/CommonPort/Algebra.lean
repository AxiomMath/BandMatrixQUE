module

public import BlockBand.Internal.Contracts.Critical
public import BlockBand.Layers.LayerMeanBounds

/-!
# Common-port mean: deterministic Schur algebra of the common port

Deterministic; no measure. *Domain:* an invertible block matrix
`M = [[D, Bm], [Bmᴴ, z I]]` (`IsUnit M.det`), `z ≠ 0`, `𝒢 = M⁻¹` (Lean's `⁻¹`); for the
common-port layer `D = blockDiag A - e I - X`, `Bm = bondMatrix .common B`, `z = z₀`.
Norms: the Euclidean operator norm (`Matrix.Norms.L2Operator`) on rectangular matrices.

* `schur_G12_eq`, `schur_G21_eq`, `schur_D_G11`: the block equations
  `𝒢₁₂ = -z⁻¹ 𝒢₁₁ Bm`, `𝒢₂₁ = -z⁻¹ Bmᴴ 𝒢₁₁`, `D 𝒢₁₁ + Bm 𝒢₂₁ = 1`.
* `schur_weighted_G11`: for every `S`, `(S + D) 𝒢₁₁ = 1 + (S + z⁻¹ Bm Bmᴴ) 𝒢₁₁`.
* `schur_weighted_G12`, `norm_schur_weighted_G12_le`:
  `(S + D) 𝒢₁₂ = -z⁻¹ (1 + (S + z⁻¹ Bm Bmᴴ) 𝒢₁₁) Bm` and
  `‖(S + D) 𝒢₁₂‖ ≤ |z|⁻¹ (1 + (‖S‖ + |z|⁻¹ ‖Bm‖²) ‖𝒢‖) ‖Bm‖`.
* `norm_submatrix_le`, `norm_toBlocks11_le`, `norm_toBlocks12_le`, `norm_toBlocks22_le`,
  `norm_blockDiag_le`: compressions do not increase the operator norm;
  `‖blockDiag A‖ ≤ Σₐ ‖Aₐ‖`.
* `commonPortL_eq`, `norm_commonPortL_le`: for `commonPortL`
  (`L = K𝒢₁₂`, `K = z_b I - X`), on `IsUnit (layerMatrix .common e z₀ X ω).det` and `z₀ ≠ 0`:
  `‖L‖ ≤ |z₀|⁻¹ (1 + (|z_b + e| + ‖blockDiag A‖ + |z₀|⁻¹ ‖Bm‖²) ‖𝒢‖) ‖Bm‖`.
  The deformation `X` enters only through `𝒢` (uniform in `X`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open Matrix BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped Matrix.Norms.L2Operator

section Schur

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `𝒢 M = 1` and `M 𝒢 = 1` for an invertible `M`. -/
theorem schur_inv_mul (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) (hM : IsUnit M.det) : M⁻¹ * M = 1 :=
  Matrix.nonsing_inv_mul M hM

theorem schur_mul_inv (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) (hM : IsUnit M.det) : M * M⁻¹ = 1 :=
  Matrix.mul_nonsing_inv M hM

/-- Block (1,2) of `𝒢 M = 1`: `𝒢₁₁ Bm + z 𝒢₁₂ = 0`, i.e. `𝒢₁₂ = -z⁻¹ 𝒢₁₁ Bm`
(so `L = -K𝒢₁₁B z₀⁻¹`). -/
theorem schur_G12_eq (D : Matrix n n ℂ) (Bm : Matrix n m ℂ) {z : ℂ} (hz : z ≠ 0)
    (hM : IsUnit (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ))).det) :
    (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₁₂ =
      -z⁻¹ • ((fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₁₁ * Bm) := by
  have h := schur_inv_mul _ hM
  generalize (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹ = G at h ⊢
  rw [← fromBlocks_toBlocks G, fromBlocks_multiply, ← fromBlocks_one] at h
  have h12 := congrArg Matrix.toBlocks₁₂ h
  simp only [toBlocks_fromBlocks₁₂] at h12
  -- `G₁₁ Bm + G₁₂ (z • 1) = 0`
  have h12' : G.toBlocks₁₂ = -z⁻¹ • (G.toBlocks₁₁ * Bm) := by
    have : z • G.toBlocks₁₂ = -(G.toBlocks₁₁ * Bm) := by
      rw [Matrix.mul_smul, Matrix.mul_one] at h12
      exact eq_neg_of_add_eq_zero_right h12
    calc G.toBlocks₁₂ = z⁻¹ • (z • G.toBlocks₁₂) := by rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = -z⁻¹ • (G.toBlocks₁₁ * Bm) := by rw [this, smul_neg, neg_smul]
  exact h12'

/-- Block (2,1) of `M 𝒢 = 1`: `Bmᴴ 𝒢₁₁ + z 𝒢₂₁ = 0`. -/
theorem schur_G21_eq (D : Matrix n n ℂ) (Bm : Matrix n m ℂ) {z : ℂ} (hz : z ≠ 0)
    (hM : IsUnit (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ))).det) :
    (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₂₁ =
      -z⁻¹ • (Bmᴴ * (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₁₁) := by
  have h := schur_mul_inv _ hM
  generalize (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹ = G at h ⊢
  rw [← fromBlocks_toBlocks G, fromBlocks_multiply, ← fromBlocks_one] at h
  have h21 := congrArg Matrix.toBlocks₂₁ h
  simp only [toBlocks_fromBlocks₂₁] at h21
  have : z • G.toBlocks₂₁ = -(Bmᴴ * G.toBlocks₁₁) := by
    rw [Matrix.smul_mul, Matrix.one_mul] at h21
    exact eq_neg_of_add_eq_zero_right h21
  calc G.toBlocks₂₁ = z⁻¹ • (z • G.toBlocks₂₁) := by rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
    _ = -z⁻¹ • (Bmᴴ * G.toBlocks₁₁) := by rw [this, smul_neg, neg_smul]

/-- Block (1,1) of `M 𝒢 = 1`: `D 𝒢₁₁ + Bm 𝒢₂₁ = 1`. -/
theorem schur_D_G11 (D : Matrix n n ℂ) (Bm : Matrix n m ℂ) (z : ℂ)
    (hM : IsUnit (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ))).det) :
    D * (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₁₁ +
        Bm * (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₂₁ = 1 := by
  have h := schur_mul_inv _ hM
  generalize (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹ = G at h ⊢
  rw [← fromBlocks_toBlocks G, fromBlocks_multiply, ← fromBlocks_one] at h
  have h11 := congrArg Matrix.toBlocks₁₁ h
  simpa only [toBlocks_fromBlocks₁₁] using h11

/-- **Weighted top block**: for every `S`,
`(S + D) 𝒢₁₁ = 1 + (S + z⁻¹ Bm Bmᴴ) 𝒢₁₁`. -/
theorem schur_weighted_G11 (S D : Matrix n n ℂ) (Bm : Matrix n m ℂ) {z : ℂ} (hz : z ≠ 0)
    (hM : IsUnit (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ))).det) :
    (S + D) * (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₁₁ =
      1 + (S + z⁻¹ • (Bm * Bmᴴ)) *
        (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₁₁ := by
  have h1 := schur_D_G11 D Bm z hM
  have h2 := schur_G21_eq D Bm hz hM
  set G := (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹
  rw [h2, Matrix.mul_smul, ← Matrix.mul_assoc] at h1
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul]
  have : D * G.toBlocks₁₁ = 1 + z⁻¹ • (Bm * Bmᴴ * G.toBlocks₁₁) := by
    rw [neg_smul] at h1
    rw [← h1]; abel
  rw [this]; abel

/-- **Weighted off-diagonal block**:
`(S + D) 𝒢₁₂ = -z⁻¹ (1 + (S + z⁻¹ Bm Bmᴴ) 𝒢₁₁) Bm`. -/
theorem schur_weighted_G12 (S D : Matrix n n ℂ) (Bm : Matrix n m ℂ) {z : ℂ} (hz : z ≠ 0)
    (hM : IsUnit (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ))).det) :
    (S + D) * (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₁₂ =
      -z⁻¹ • ((1 + (S + z⁻¹ • (Bm * Bmᴴ)) *
        (fromBlocks D Bm Bmᴴ (z • (1 : Matrix m m ℂ)))⁻¹.toBlocks₁₁) * Bm) := by
  rw [schur_G12_eq D Bm hz hM, Matrix.mul_smul, ← Matrix.mul_assoc,
    schur_weighted_G11 S D Bm hz hM]

end Schur

section Norms

/-- `‖J‖ ≤ 1` when `J Jᴴ = 1`. -/
theorem norm_le_one_of_mul_conjTranspose {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (J : Matrix m n ℂ) (hJ : J * Jᴴ = 1) : ‖J‖ ≤ 1 := by
  have h1 : ‖Jᴴ‖ * ‖Jᴴ‖ = ‖(Jᴴ)ᴴ * Jᴴ‖ := (l2_opNorm_conjTranspose_mul_self Jᴴ).symm
  rw [conjTranspose_conjTranspose, hJ, l2_opNorm_conjTranspose] at h1
  have h2 := BlockBand.Layers.lct_norm_one_le (n := m)
  have h0 := norm_nonneg J
  nlinarith

/-- Coordinate selection matrix of a map `f : m → n`. -/
def selectMatrix {m n : Type*} [DecidableEq n] (f : m → n) : Matrix m n ℂ :=
  Matrix.of fun x y => if y = f x then 1 else 0

theorem selectMatrix_mul_conjTranspose {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {f : m → n} (hf : Function.Injective f) :
    selectMatrix f * (selectMatrix f)ᴴ = 1 := by
  ext x y
  simp only [Matrix.mul_apply, conjTranspose_apply, selectMatrix, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (f y)]
  · by_cases h : x = y
    · subst h; simp
    · have : f y ≠ f x := fun e => h (hf e).symm
      simp [this, h]
  · intro c _ hc; simp [hc]
  · simp

theorem submatrix_eq_select {l m n o : Type*} [Fintype n] [DecidableEq n] [Fintype o]
    [DecidableEq o] (M : Matrix n o ℂ) (f : l → n) (g : m → o) :
    M.submatrix f g = selectMatrix f * M * (selectMatrix g)ᴴ := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, conjTranspose_apply, selectMatrix,
    Matrix.of_apply]
  rw [Finset.sum_eq_single (g y)]
  · rw [Finset.sum_eq_single (f x)] <;> simp +contextual
  · intro c _ hc; simp [hc]
  · simp

/-- **Compressions do not increase the operator norm**: `‖M.submatrix f g‖ ≤ ‖M‖` for
injective `f, g`. -/
theorem norm_submatrix_le {l m n o : Type*} [Fintype l] [DecidableEq l] [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype o] [DecidableEq o]
    (M : Matrix n o ℂ) {f : l → n} {g : m → o} (hf : Function.Injective f)
    (hg : Function.Injective g) : ‖M.submatrix f g‖ ≤ ‖M‖ := by
  rw [submatrix_eq_select]
  have h1 := norm_le_one_of_mul_conjTranspose _ (selectMatrix_mul_conjTranspose hf)
  have h2 := norm_le_one_of_mul_conjTranspose _ (selectMatrix_mul_conjTranspose hg)
  calc ‖selectMatrix f * M * (selectMatrix g)ᴴ‖
      ≤ ‖selectMatrix f‖ * ‖M‖ * ‖(selectMatrix g)ᴴ‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
          (norm_nonneg _))
    _ ≤ 1 * ‖M‖ * 1 := by
        rw [l2_opNorm_conjTranspose]
        exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2 (norm_nonneg _)
          (by positivity)
    _ = ‖M‖ := by ring

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `‖M₁₂‖ ≤ ‖M‖`. -/
theorem norm_toBlocks12_le (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : ‖M.toBlocks₁₂‖ ≤ ‖M‖ := by
  have : M.toBlocks₁₂ = M.submatrix Sum.inl Sum.inr := rfl
  rw [this]
  exact norm_submatrix_le M Sum.inl_injective Sum.inr_injective

/-- `‖M₂₂‖ ≤ ‖M‖`. -/
theorem norm_toBlocks22_le (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : ‖M.toBlocks₂₂‖ ≤ ‖M‖ := by
  have : M.toBlocks₂₂ = M.submatrix Sum.inr Sum.inr := rfl
  rw [this]
  exact norm_submatrix_le M Sum.inr_injective Sum.inr_injective

/-- `‖M₁₁‖ ≤ ‖M‖`. -/
theorem norm_toBlocks11_le (M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : ‖M.toBlocks₁₁‖ ≤ ‖M‖ := by
  have : M.toBlocks₁₁ = M.submatrix Sum.inl Sum.inl := rfl
  rw [this]
  exact norm_submatrix_le M Sum.inl_injective Sum.inl_injective

end Norms

section BlockDiag

/-- One diagonal block of `blockDiag`, embedded. -/
def blockEmbed {k W : ℕ} (A : Fin k → Matrix (Fin W) (Fin W) ℂ) (a : Fin k) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  (selectMatrix (fun i : Fin W => (a, i)))ᴴ * A a * selectMatrix (fun i : Fin W => (a, i))

theorem blockEmbed_apply {k W : ℕ} (A : Fin k → Matrix (Fin W) (Fin W) ℂ) (a : Fin k)
    (x y : Fin k × Fin W) :
    blockEmbed A a x y = if x.1 = a ∧ y.1 = a then A a x.2 y.2 else 0 := by
  obtain ⟨c, i⟩ := x
  obtain ⟨d, j⟩ := y
  simp only [blockEmbed, Matrix.mul_apply, conjTranspose_apply, selectMatrix, Matrix.of_apply,
    Prod.mk.injEq]
  by_cases hc : c = a <;> by_cases hd : d = a
  · subst hc; subst hd
    simp [Finset.sum_ite_eq]
  · simp [hd]
  · simp [hc]
  · simp [hc]

theorem blockDiag_eq_sum {k W : ℕ} (A : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    Internal.Contracts.Layers.blockDiag A = ∑ a, blockEmbed A a := by
  ext x y
  simp only [Internal.Contracts.Layers.blockDiag, Matrix.sum_apply, blockEmbed_apply]
  by_cases h : x.1 = y.1
  · rw [Finset.sum_eq_single x.1]
    · simp [h]
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  · simp only [h, ite_false]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    by_cases hc : x.1 = c
    · have : ¬ y.1 = c := fun e => h (hc.trans e.symm)
      simp [this]
    · simp [hc]

theorem norm_blockEmbed_le {k W : ℕ} (A : Fin k → Matrix (Fin W) (Fin W) ℂ) (a : Fin k) :
    ‖blockEmbed A a‖ ≤ ‖A a‖ := by
  have hinj : Function.Injective (fun i : Fin W => (a, i)) := fun i j h => (Prod.ext_iff.1 h).2
  have h1 := norm_le_one_of_mul_conjTranspose _ (selectMatrix_mul_conjTranspose hinj)
  unfold blockEmbed
  calc ‖(selectMatrix (fun i : Fin W => (a, i)))ᴴ * A a * selectMatrix (fun i : Fin W => (a, i))‖
      ≤ ‖(selectMatrix (fun i : Fin W => (a, i)))ᴴ‖ * ‖A a‖ *
          ‖selectMatrix (fun i : Fin W => (a, i))‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
          (norm_nonneg _))
    _ ≤ 1 * ‖A a‖ * 1 := by
        rw [l2_opNorm_conjTranspose]
        exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h1 (norm_nonneg _)
          (by positivity)
    _ = ‖A a‖ := by ring

/-- **`‖blockDiag A‖ ≤ Σₐ ‖Aₐ‖`** (operator norms). -/
theorem norm_blockDiag_le {k W : ℕ} (A : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    ‖Internal.Contracts.Layers.blockDiag A‖ ≤ ∑ a, ‖A a‖ := by
  rw [blockDiag_eq_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_blockEmbed_le A a)

end BlockDiag

section CommonPort

variable {W : ℕ}

/-- The random weight `T = (z_b + e) I - blockDiag A + z₀⁻¹ Bm Bmᴴ`. -/
def commonPortWeight (b e : ℝ) (ω : LayerSample W .common) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ((boundaryZ b e + (e : ℂ)) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - blockDiag ω.1) +
    (commonZ b e)⁻¹ • (bondMatrix .common ω.2 * (bondMatrix .common ω.2)ᴴ)

/-- **The weighted identity for the common-port matrix `L`.** Deterministic;
for every `W`, Hermitian or not `X`, real `e`, `b`, and every layer sample `ω` with
`IsUnit (layerMatrix .common e z₀ X ω).det` and `z₀ = commonZ b e ≠ 0`:
`L = K𝒢₁₂ = -z₀⁻¹ (1 + T 𝒢₁₁) Bm`, `T = commonPortWeight b e ω`. -/
theorem commonPortL_eq (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) (hz : commonZ b e ≠ 0)
    (hM : IsUnit (layerMatrix .common e (commonZ b e) X ω).det) :
    commonPortL b e X ω = -(commonZ b e)⁻¹ •
      ((1 + commonPortWeight b e ω * (commonPortResolvent b e X ω).toBlocks₁₁) *
        bondMatrix .common ω.2) := by
  have hK : matchedLeadK b e X =
      ((boundaryZ b e + (e : ℂ)) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        blockDiag ω.1) + (blockDiag ω.1 - (e : ℂ) • 1 - X) := by
    unfold matchedLeadK; rw [add_smul]; abel
  unfold commonPortL commonPortResolvent layerResolvent commonPortWeight
  rw [hK]
  exact schur_weighted_G12 _ _ _ hz hM

/-- **Deterministic bound on `L`**: on the same domain as
`commonPortL_eq`, with operator norms,
`‖L‖ ≤ |z₀|⁻¹ (1 + (|z_b + e| + ‖blockDiag A‖ + |z₀|⁻¹ ‖Bm‖²) ‖𝒢‖) ‖Bm‖`.
No norm of `X` enters. -/
theorem norm_commonPortL_le (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) (hz : commonZ b e ≠ 0)
    (hM : IsUnit (layerMatrix .common e (commonZ b e) X ω).det) :
    ‖commonPortL b e X ω‖ ≤ ‖commonZ b e‖⁻¹ *
      (1 + (‖boundaryZ b e + (e : ℂ)‖ + ‖blockDiag ω.1‖ +
          ‖commonZ b e‖⁻¹ * ‖bondMatrix .common ω.2‖ ^ 2) *
        ‖commonPortResolvent b e X ω‖) * ‖bondMatrix .common ω.2‖ := by
  rw [commonPortL_eq b e X ω hz hM, norm_smul, norm_neg, norm_inv]
  set Bm := bondMatrix .common ω.2
  set G := commonPortResolvent b e X ω
  have hT : ‖commonPortWeight b e ω‖ ≤ ‖boundaryZ b e + (e : ℂ)‖ + ‖blockDiag ω.1‖ +
      ‖commonZ b e‖⁻¹ * ‖Bm‖ ^ 2 := by
    unfold commonPortWeight
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ?_ le_rfl)) ?_)
    · rw [norm_smul]
      calc ‖boundaryZ b e + (e : ℂ)‖ * ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖
          ≤ ‖boundaryZ b e + (e : ℂ)‖ * 1 :=
            mul_le_mul_of_nonneg_left BlockBand.Layers.lct_norm_one_le (norm_nonneg _)
        _ = _ := mul_one _
    · rw [norm_smul, norm_inv, sq]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (l2_opNorm_mul _ _).trans (le_of_eq (by rw [l2_opNorm_conjTranspose]))
  have hG11 : ‖G.toBlocks₁₁‖ ≤ ‖G‖ := norm_toBlocks11_le G
  have h1 : ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      commonPortWeight b e ω * G.toBlocks₁₁‖ ≤
      1 + (‖boundaryZ b e + (e : ℂ)‖ + ‖blockDiag ω.1‖ + ‖commonZ b e‖⁻¹ * ‖Bm‖ ^ 2) * ‖G‖ := by
    refine (norm_add_le _ _).trans (add_le_add BlockBand.Layers.lct_norm_one_le ?_)
    exact (l2_opNorm_mul _ _).trans (mul_le_mul hT hG11 (norm_nonneg _)
      ((norm_nonneg _).trans hT))
  calc ‖commonZ b e‖⁻¹ * ‖((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
        commonPortWeight b e ω * G.toBlocks₁₁) * Bm‖
      ≤ ‖commonZ b e‖⁻¹ * (‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
          commonPortWeight b e ω * G.toBlocks₁₁‖ * ‖Bm‖) :=
        mul_le_mul_of_nonneg_left (l2_opNorm_mul _ _) (by positivity)
    _ ≤ ‖commonZ b e‖⁻¹ * ((1 + (‖boundaryZ b e + (e : ℂ)‖ + ‖blockDiag ω.1‖ +
          ‖commonZ b e‖⁻¹ * ‖Bm‖ ^ 2) * ‖G‖) * ‖Bm‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
          (by positivity)
    _ = _ := by ring

/-- `‖H‖ = ‖𝒢₂₂‖ ≤ ‖𝒢‖` (every sample). -/
theorem norm_commonPortH_le (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) :
    ‖commonPortH b e X ω‖ ≤ ‖commonPortResolvent b e X ω‖ :=
  norm_toBlocks22_le _

end CommonPort

end BlockBand.Critical.CommonPort
