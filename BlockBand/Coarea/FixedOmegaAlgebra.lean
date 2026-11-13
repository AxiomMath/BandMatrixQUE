module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalNormalizedManuscriptChartMeasure

/-!
# Fixed-`ω` coarea, linear algebra: frames, inertia, Gaussian norm splitting

*Setting.* Finite index types `ι` (the pair block, `|ι| = d`) and `κ` (a frame index,
`|κ| = d - 1`); a unit vector `v : ι → ℂ` and an orthonormal frame `U : Matrix ι κ ℂ` of
`v^⊥` (`Uᴴ U = 1`, `Uᴴ v = 0`). Everything is exact finite-dimensional algebra; there is no
measure, limit or uniformity statement.

## Main results

* `negativeCount_eq_of_charpoly_eq`, `negativeCount_unitary_conj`, `negativeCount_reindex`:
  `N_-` depends only on the characteristic polynomial.
* `frame_mul_conjTranspose`: `U Uᴴ = 1 - v vᴴ` (dimension count `|ι| = |κ| + 1`).
* `frameChange_mul`, `frameChange_unitary`: for two frames `U₁, U₂` of `v^⊥`,
  `W = U₁ᴴ U₂` is unitary and `U₂ = U₁ W`.
* `hilbertSchmidtNormSq_reconstructed` (the Gaussian norm splitting of the coarea regression formula): for Hermitian `F`,
  `‖E vvᴴ + U(UᴴFU + G')Uᴴ - F‖²_HS = (E - vᴴFv)² + 2‖Fv - (vᴴFv)v‖² + ‖G'‖²_HS`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FixedOmega

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-!
## The negative count depends only on the characteristic polynomial
-/

theorem negativeCount_of_isHermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    negativeCount M = (Finset.univ.filter fun k => hM.eigenvalues k < 0).card := by
  unfold negativeCount
  simp [hM]

theorem negativeCount_eq_card_roots {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    negativeCount M = (M.charpoly.roots.filter fun z : ℂ => z.re < 0).card := by
  rw [negativeCount_of_isHermitian hM, hM.roots_charpoly_eq_eigenvalues, Multiset.filter_map,
    Multiset.card_map, Finset.card_def, Finset.filter_val]
  congr 1

/-- `N_-` is a function of the characteristic polynomial (Hermitian matrices). -/
theorem negativeCount_eq_of_charpoly_eq {M : Matrix ι ι ℂ} {N : Matrix κ κ ℂ}
    (hM : M.IsHermitian) (hN : N.IsHermitian) (h : M.charpoly = N.charpoly) :
    negativeCount M = negativeCount N := by
  rw [negativeCount_eq_card_roots hM, negativeCount_eq_card_roots hN, h]

theorem charpoly_unitary_conj {W M : Matrix ι ι ℂ} (hW : Wᴴ * W = 1) :
    (Wᴴ * M * W).charpoly = M.charpoly := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hW', Matrix.mul_one]

/-- Unitary conjugation preserves `N_-`. -/
theorem negativeCount_unitary_conj {W M : Matrix ι ι ℂ} (hW : Wᴴ * W = 1)
    (hM : M.IsHermitian) : negativeCount (Wᴴ * M * W) = negativeCount M :=
  negativeCount_eq_of_charpoly_eq (isHermitian_conjTranspose_mul_mul W hM) hM
    (charpoly_unitary_conj hW)

/-- Unitary conjugation preserves the determinant. -/
theorem det_unitary_conj {W M : Matrix ι ι ℂ} (hW : Wᴴ * W = 1) :
    (Wᴴ * M * W).det = M.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Wᴴ.det), mul_assoc, ← Matrix.det_mul, hW,
    Matrix.det_one, mul_one]

/-- Reindexing preserves `N_-`. -/
theorem negativeCount_reindex (e : ι ≃ κ) {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    negativeCount (Matrix.reindex e e M) = negativeCount M :=
  negativeCount_eq_of_charpoly_eq (hM.submatrix e.symm) hM (Matrix.charpoly_reindex e M)

/-!
## Unit vectors and frames
-/

theorem l2Norm_sq {α : Type*} [Fintype α] (x : α → ℂ) : l2Norm x ^ 2 = ∑ k, ‖x k‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem star_dotProduct_self_eq {α : Type*} [Fintype α] (x : α → ℂ) :
    star x ⬝ᵥ x = ((l2Norm x ^ 2 : ℝ) : ℂ) := by
  rw [l2Norm_sq]
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]
  rfl

theorem l2Norm_sq_eq_re {α : Type*} [Fintype α] (x : α → ℂ) :
    l2Norm x ^ 2 = (star x ⬝ᵥ x).re := by
  rw [star_dotProduct_self_eq, Complex.ofReal_re]

theorem star_dotProduct_self_of_l2Norm {α : Type*} [Fintype α] {v : α → ℂ}
    (hv : l2Norm v = 1) : star v ⬝ᵥ v = 1 := by
  rw [star_dotProduct_self_eq, hv]
  simp

/-- `U` is an orthonormal frame of `v^⊥`. -/
def IsFrameOf (v : ι → ℂ) (U : Matrix ι κ ℂ) : Prop :=
  Uᴴ * U = 1 ∧ Uᴴ *ᵥ v = 0

/-- The square matrix `[v | U]` with columns indexed by `Unit ⊕ κ`. -/
def frameCompletion (v : ι → ℂ) (U : Matrix ι κ ℂ) : Matrix ι (Unit ⊕ κ) ℂ :=
  Matrix.fromCols (Matrix.replicateCol Unit v) U

theorem frame_star_mulVec {v : ι → ℂ} {U : Matrix ι κ ℂ} (hUv : Uᴴ *ᵥ v = 0) :
    star v ᵥ* U = 0 := by
  have h := congrArg star hUv
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, star_zero] at h
  exact h

theorem frameCompletion_conjTranspose_mul {v : ι → ℂ} {U : Matrix ι κ ℂ}
    (hv : star v ⬝ᵥ v = 1) (hU : IsFrameOf v U) :
    (frameCompletion v U)ᴴ * frameCompletion v U = 1 := by
  obtain ⟨hUU, hUv⟩ := hU
  have hvU := frame_star_mulVec hUv
  unfold frameCompletion
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]
  rw [← Matrix.fromBlocks_one]
  congr 1
  · ext a b
    simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.conjTranspose_apply, dotProduct] at hv ⊢
    simpa [mul_comm] using hv
  · ext a j
    have := congrFun hvU j
    simpa [Matrix.mul_apply, Matrix.replicateCol, Matrix.conjTranspose_apply, Matrix.vecMul,
      dotProduct] using this
  · ext j a
    have := congrFun hUv j
    simpa [Matrix.mul_apply, Matrix.replicateCol, Matrix.mulVec, dotProduct] using this

/-- **Projection identity**: for an orthonormal frame `U` of `v^⊥` (with `|ι| = |κ| + 1`),
`U Uᴴ = 1 - v vᴴ`. -/
theorem frame_mul_conjTranspose (hcard : Fintype.card ι = Fintype.card κ + 1)
    {v : ι → ℂ} {U : Matrix ι κ ℂ} (hv : star v ⬝ᵥ v = 1) (hU : IsFrameOf v U) :
    U * Uᴴ = 1 - vecMulVec v (star v) := by
  set W := frameCompletion v U
  have hW := frameCompletion_conjTranspose_mul hv hU
  have hc : Fintype.card (Unit ⊕ κ) = Fintype.card ι := by
    simp [hcard, add_comm]
  let e : Unit ⊕ κ ≃ ι := Fintype.equivOfCardEq hc
  set Ws : Matrix ι ι ℂ := W.submatrix id e.symm
  have hWs : Wsᴴ * Ws = 1 := by
    have h1 : Wsᴴ = Wᴴ.submatrix e.symm id := by
      ext a b; simp [Ws, Matrix.conjTranspose_apply]
    rw [h1]
    have h2 : (Wᴴ.submatrix e.symm id) * Ws = (Wᴴ * W).submatrix e.symm e.symm := by
      have := Matrix.submatrix_mul_equiv Wᴴ W e.symm (Equiv.refl ι) e.symm
      simpa [Ws] using this
    rw [h2, hW, Matrix.submatrix_one_equiv]
  have hWs' : Ws * Wsᴴ = 1 := mul_eq_one_comm.mp hWs
  have h3 : Ws * Wsᴴ = W * Wᴴ := by
    have h1 : Wsᴴ = Wᴴ.submatrix e.symm id := by
      ext a b; simp [Ws, Matrix.conjTranspose_apply]
    rw [h1]
    have := Matrix.submatrix_mul_equiv W Wᴴ id e.symm id
    simp [Ws]
  have h4 : W * Wᴴ = vecMulVec v (star v) + U * Uᴴ := by
    simp only [W, frameCompletion]
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
    congr 1
    ext a b
    simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.conjTranspose_apply, vecMulVec_apply]
  rw [← h3, hWs'] at h4
  rw [h4]
  abel

/-- For two frames of `v^⊥`, `W = U₁ᴴ U₂` satisfies `U₁ W = U₂`. -/
theorem frameChange_mul (hcard : Fintype.card ι = Fintype.card κ + 1)
    {v : ι → ℂ} {U₁ U₂ : Matrix ι κ ℂ} (hv : star v ⬝ᵥ v = 1)
    (h₁ : IsFrameOf v U₁) (h₂ : IsFrameOf v U₂) : U₁ * (U₁ᴴ * U₂) = U₂ := by
  rw [← Matrix.mul_assoc, frame_mul_conjTranspose hcard hv h₁, Matrix.sub_mul, Matrix.one_mul]
  have : vecMulVec v (star v) * U₂ = 0 := by
    rw [vecMulVec_mul, frame_star_mulVec h₂.2]
    ext a b; simp [vecMulVec_apply]
  rw [this, sub_zero]

/-- For two frames of `v^⊥`, `W = U₁ᴴ U₂` is unitary. -/
theorem frameChange_unitary (hcard : Fintype.card ι = Fintype.card κ + 1)
    {v : ι → ℂ} {U₁ U₂ : Matrix ι κ ℂ} (hv : star v ⬝ᵥ v = 1)
    (h₁ : IsFrameOf v U₁) (h₂ : IsFrameOf v U₂) : (U₁ᴴ * U₂)ᴴ * (U₁ᴴ * U₂) = 1 := by
  have h := frameChange_mul hcard hv h₁ h₂
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h, h₂.1]

/-!
## Gaussian norm splitting
-/

section NormSplitting

open CoareaNative.BlockBand

theorem mul_mul_eq_zero_of' {l m n k : Type*} [Fintype l] [Fintype m] {A : Matrix l m ℂ}
    {B : Matrix m n ℂ} (h : A * B = 0) (Y : Matrix k l ℂ) : Y * A * B = 0 := by
  rw [Matrix.mul_assoc, h, Matrix.mul_zero]

theorem mul_mul_eq_self_of' {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    {A : Matrix m n ℂ} {B : Matrix n m ℂ} (h : A * B = 1) (Y : Matrix k m ℂ) :
    Y * A * B = Y := by
  rw [Matrix.mul_assoc, h, Matrix.mul_one]

theorem hilbertSchmidtNormSq_unit (A : Matrix Unit Unit ℂ) :
    hilbertSchmidtNormSq A = Complex.normSq (A () ()) := by
  simp [hilbertSchmidtNormSq]

theorem hilbertSchmidtNormSq_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : hilbertSchmidtNormSq Aᴴ = hilbertSchmidtNormSq A := by
  unfold hilbertSchmidtNormSq
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

theorem hilbertSchmidtNormSq_neg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : hilbertSchmidtNormSq (-A) = hilbertSchmidtNormSq A := by
  simp [hilbertSchmidtNormSq]

theorem hilbertSchmidtNormSq_col {m : Type*} [Fintype m] (A : Matrix m Unit ℂ) :
    hilbertSchmidtNormSq A = ∑ j, Complex.normSq (A j ()) := by
  simp [hilbertSchmidtNormSq]

/-- Unitary invariance of the Hilbert–Schmidt norm under the square completion `[v | U]`. -/
theorem hilbertSchmidtNormSq_frameCompletion_conj
    (hcard : Fintype.card ι = Fintype.card κ + 1)
    {v : ι → ℂ} {U : Matrix ι κ ℂ} (hv : star v ⬝ᵥ v = 1) (hU : IsFrameOf v U)
    (X : Matrix ι ι ℂ) :
    hilbertSchmidtNormSq X =
      hilbertSchmidtNormSq ((frameCompletion v U)ᴴ * X * frameCompletion v U) := by
  set W := frameCompletion v U
  have hW := frameCompletion_conjTranspose_mul hv hU
  have hc : Fintype.card (Unit ⊕ κ) = Fintype.card ι := by
    simp [hcard, add_comm]
  let e : Unit ⊕ κ ≃ ι := Fintype.equivOfCardEq hc
  set Ws : Matrix ι ι ℂ := W.submatrix id e.symm
  have h1 : Wsᴴ = Wᴴ.submatrix e.symm id := by
    ext a b; simp [Ws, Matrix.conjTranspose_apply]
  have hWs : Wsᴴ * Ws = 1 := by
    rw [h1]
    have h2 : (Wᴴ.submatrix e.symm id) * Ws = (Wᴴ * W).submatrix e.symm e.symm := by
      have := Matrix.submatrix_mul_equiv Wᴴ W e.symm (Equiv.refl ι) e.symm
      simpa [Ws] using this
    rw [h2, hW, Matrix.submatrix_one_equiv]
  have hWs' : Ws * Wsᴴ = 1 := mul_eq_one_comm.mp hWs
  have hconj : hilbertSchmidtNormSq (Wsᴴ * X * Wsᴴᴴ) = hilbertSchmidtNormSq X :=
    hilbertSchmidtNormSq_unitary_conj Wsᴴ X (by rw [conjTranspose_conjTranspose]; exact hWs')
  rw [conjTranspose_conjTranspose] at hconj
  have hre : Wsᴴ * X * Ws = Matrix.reindex e e (Wᴴ * X * W) := by
    rw [h1]
    ext a b
    simp [Ws, Matrix.mul_apply, Matrix.reindex_apply]
  rw [← hconj, hre, hilbertSchmidtNormSq_reindex]

/-- `‖Uᴴ w‖² = ‖w - (vᴴw) v‖²` for an orthonormal frame `U` of `v^⊥`. -/
theorem sum_normSq_frame_mulVec (hcard : Fintype.card ι = Fintype.card κ + 1)
    {v : ι → ℂ} {U : Matrix ι κ ℂ} (hv : star v ⬝ᵥ v = 1) (hU : IsFrameOf v U)
    (w : ι → ℂ) :
    ∑ j, Complex.normSq ((Uᴴ *ᵥ w) j) = l2Norm (w - (star v ⬝ᵥ w) • v) ^ 2 := by
  have hP := frame_mul_conjTranspose hcard hv hU
  have hL : ∑ j, Complex.normSq ((Uᴴ *ᵥ w) j) = (star (Uᴴ *ᵥ w) ⬝ᵥ (Uᴴ *ᵥ w)).re := by
    rw [← l2Norm_sq_eq_re, l2Norm_sq]
    simp [Complex.normSq_eq_norm_sq]
  rw [hL, l2Norm_sq_eq_re]
  have h1 : star (Uᴴ *ᵥ w) ⬝ᵥ (Uᴴ *ᵥ w) = star w ⬝ᵥ (w - (star v ⬝ᵥ w) • v) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, hP, Matrix.sub_mulVec, Matrix.one_mulVec]
    congr 2
    funext a
    simp [Matrix.mulVec, vecMulVec_apply, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  have h2 : star (w - (star v ⬝ᵥ w) • v) ⬝ᵥ (w - (star v ⬝ᵥ w) • v) =
      star w ⬝ᵥ (w - (star v ⬝ᵥ w) • v) := by
    have h3 : star v ⬝ᵥ (w - (star v ⬝ᵥ w) • v) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, hv]; simp
    rw [star_sub, sub_dotProduct, star_smul, smul_dotProduct, h3, smul_zero, sub_zero]
  rw [h1, h2]

/-- **Gaussian norm splitting** (in the coarea regression formula): for a unit
vector `v`, an orthonormal frame `U` of `v^⊥`, Hermitian `F`, real `E` and any `G'`,
`‖E vvᴴ + U(UᴴFU + G')Uᴴ - F‖²_HS = (E - vᴴFv)² + 2‖Fv - (vᴴFv)v‖² + ‖G'‖²_HS`. -/
theorem hilbertSchmidtNormSq_reconstructed (hcard : Fintype.card ι = Fintype.card κ + 1)
    {v : ι → ℂ} {U : Matrix ι κ ℂ} (hv : star v ⬝ᵥ v = 1) (hU : IsFrameOf v U)
    {F : Matrix ι ι ℂ} (hF : F.IsHermitian) (E : ℝ) (G' : Matrix κ κ ℂ) :
    hilbertSchmidtNormSq ((E : ℂ) • vecMulVec v (star v) + U * (Uᴴ * F * U + G') * Uᴴ - F) =
      (E - (star v ⬝ᵥ (F *ᵥ v)).re) ^ 2 +
        2 * l2Norm (F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) ^ 2 + hilbertSchmidtNormSq G' := by
  set col : Matrix ι Unit ℂ := Matrix.replicateCol Unit v
  set row : Matrix Unit ι ℂ := Matrix.replicateRow Unit (star v)
  obtain ⟨hUU, hUv⟩ := hU
  have hUcol : Uᴴ * col = 0 := by
    ext j u
    simpa [col, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hUv j
  have hrowU : row * U = 0 := by
    ext u j
    simpa [row, Matrix.mul_apply, Matrix.vecMul, dotProduct] using
      congrFun (frame_star_mulVec hUv) j
  have hrowcol : row * col = 1 := by
    simp only [row, col, Matrix.replicateRow_mul_replicateCol, hv]
    ext a b; simp
  have hvv : vecMulVec v (star v) = col * row := Matrix.vecMulVec_eq Unit v (star v)
  set X := (E : ℂ) • vecMulVec v (star v) + U * (Uᴴ * F * U + G') * Uᴴ - F
  rw [hilbertSchmidtNormSq_frameCompletion_conj hcard hv ⟨hUU, hUv⟩ X]
  have hWh : (frameCompletion v U)ᴴ = Matrix.fromRows row Uᴴ := by
    simp only [frameCompletion, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_replicateCol, row, col]
  rw [hWh, Matrix.fromRows_mul, frameCompletion, fromRows_mul_fromCols,
    hilbertSchmidtNormSq_fromBlocks]
  have hD : Uᴴ * X * U = G' := by
    simp only [X, hvv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hUcol, hUU, Matrix.one_mul,
      Matrix.zero_mul, smul_zero, zero_add, mul_mul_eq_zero_of' hUcol, mul_mul_eq_self_of' hUU]
    abel
  have hC : Uᴴ * X * col = -(Uᴴ * F * col) := by
    simp only [X, hvv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hUcol, hUU, Matrix.one_mul,
      Matrix.zero_mul, Matrix.mul_zero, smul_zero, zero_add, add_zero, mul_mul_eq_zero_of' hUcol,
      mul_mul_eq_self_of' hUU]
    abel
  have hB : row * X * U = -(Uᴴ * F * col)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF.eq, conjTranspose_conjTranspose]
    simp only [X, hvv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hrowU, hrowcol, Matrix.one_mul,
      Matrix.mul_zero, Matrix.zero_mul, smul_zero, zero_add, add_zero, Matrix.conjTranspose_neg,
      mul_mul_eq_zero_of' hrowU, mul_mul_eq_self_of' hrowcol, mul_mul_eq_self_of' hUU]
    rw [show (col)ᴴ = row by simp [row, col, conjTranspose_replicateCol]]
    abel
  have hAm : row * X * col = (((E : ℂ) - star v ⬝ᵥ (F *ᵥ v)) • (1 : Matrix Unit Unit ℂ)) := by
    simp only [X, hvv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hrowU, hrowcol, Matrix.one_mul,
      Matrix.zero_mul, smul_zero, zero_add, add_zero, Matrix.mul_one, mul_mul_eq_zero_of' hrowU,
      mul_mul_eq_self_of' hrowcol, mul_mul_eq_zero_of' hUcol]
    ext a b
    simp only [row, col, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.replicateRow_apply, Matrix.replicateCol_apply,
      Pi.star_apply, Finset.univ_unique, Finset.sum_singleton, ite_true, smul_eq_mul, mul_one,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [hD, hC, hB, hAm, hilbertSchmidtNormSq_neg, hilbertSchmidtNormSq_conjTranspose,
    hilbertSchmidtNormSq_neg, hilbertSchmidtNormSq_unit, hilbertSchmidtNormSq_col]
  have hcolv : ∀ j, (Uᴴ * F * col) j () = (Uᴴ *ᵥ (F *ᵥ v)) j := by
    intro j
    simp only [col, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.replicateCol_apply,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  simp_rw [hcolv]
  rw [sum_normSq_frame_mulVec hcard hv ⟨hUU, hUv⟩]
  have him : (star v ⬝ᵥ (F *ᵥ v)).im = 0 := hF.im_star_dotProduct_mulVec_self v
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Complex.normSq_apply,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, him]
  ring

end NormSplitting

end BlockBand.Coarea.FixedOmega
