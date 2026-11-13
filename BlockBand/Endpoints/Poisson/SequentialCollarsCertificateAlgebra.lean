module

public import BlockBand.Endpoints.Poisson.SequentialCollarsInvertible
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# Item (ii): matrix algebra of the compressed old response

Item (ii) of the sequential collars lemma. Deterministic identities for Steps 3–4 of its proof:
* `inv_block_of_decoupled`: inverse of a block-diagonal matrix (decoupled components);
  `inv_fromBlocks_toBlocks₂₂`, `inv_fromBlocks_toBlocks₁₁`: Schur blocks of inverses.
* `one_sub_oldResponse_conj_mul`: `I - r*r = 4η R*(-Im X)R`; `oldResponse_unitary`: `r` is unitary
  for Hermitian `X` (`g₀ = 0` in case 1).
* `blockConductance_symm`: the two one-port conductances of a unitary two-port agree;
  `portBlock_inv_zero`, `blockConductance_zero_eq`: the near-port conductance is
  `conductanceOf (passiveTransmission b e (nearSchur z X))` (`nearConductance`).
* `case1_conclusions`, `case2_conclusions`: `d(X₀)` and `g₀` from the two shapes of the outer
  resolvent (Step 3).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix

section BlockInverse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse of a matrix that is block diagonal with respect to `K` versus its complement is
block diagonal, and its `K` block is the inverse of the `K` block. -/
theorem inv_block_of_decoupled (N : Matrix ι ι ℂ) (K : ι → Prop) [DecidablePred K]
    (hN : ∀ x y, K x → ¬ K y → N x y = 0 ∧ N y x = 0) (hdet : IsUnit N.det) :
    (N⁻¹).submatrix (Subtype.val : {x // K x} → ι) (Subtype.val : {x // K x} → ι) =
        (N.submatrix (Subtype.val : {x // K x} → ι) (Subtype.val : {x // K x} → ι))⁻¹ ∧
      ∀ x y, K x → ¬ K y → N⁻¹ x y = 0 ∧ N⁻¹ y x = 0 := by
  set e := Equiv.sumCompl K
  set N₁ := N.submatrix (Subtype.val : {x // K x} → ι) Subtype.val
  set N₂ := N.submatrix (Subtype.val : {x // ¬ K x} → ι) Subtype.val
  have hblk : N.submatrix e e = fromBlocks N₁ 0 0 N₂ := by
    ext (x | x) (y | y)
    · rfl
    · exact (hN x.1 y.1 x.2 y.2).1
    · exact (hN y.1 x.1 y.2 x.2).2
    · rfl
  have hdet' : IsUnit (fromBlocks N₁ 0 0 N₂).det := by
    rw [← hblk, det_submatrix_equiv_self]; exact hdet
  rw [det_fromBlocks_zero₂₁, IsUnit.mul_iff] at hdet'
  have hinv : (N.submatrix e e)⁻¹ = fromBlocks N₁⁻¹ 0 0 N₂⁻¹ := by
    rw [hblk, inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _
      (by rw [isUnit_iff_isUnit_det, isUnit_iff_isUnit_det]; exact iff_of_true hdet'.1 hdet'.2)]
    simp
  rw [inv_submatrix_equiv] at hinv
  refine ⟨?_, fun x y hx hy => ⟨?_, ?_⟩⟩
  · ext x y
    have := congrFun (congrFun hinv (Sum.inl x)) (Sum.inl y)
    simpa [e] using this
  · have := congrFun (congrFun hinv (Sum.inl ⟨x, hx⟩)) (Sum.inr ⟨y, hy⟩)
    simpa [e] using this
  · have := congrFun (congrFun hinv (Sum.inr ⟨y, hy⟩)) (Sum.inl ⟨x, hx⟩)
    simpa [e] using this

/-- Bottom-right block of the inverse of a `2 × 2` block matrix (Schur complement of `A`). -/
theorem inv_fromBlocks_toBlocks₂₂ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hA : IsUnit A.det) (hS : IsUnit (D - C * A⁻¹ * B).det) :
    ((fromBlocks A B C D)⁻¹).toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  let := invertibleOfIsUnitDet A hA
  have hS' : IsUnit (D - C * ⅟A * B).det := by rwa [invOf_eq_nonsing_inv]
  let := invertibleOfIsUnitDet _ hS'
  let := fromBlocks₁₁Invertible A B C D
  rw [← invOf_eq_nonsing_inv (fromBlocks A B C D), invOf_fromBlocks₁₁_eq, toBlocks_fromBlocks₂₂,
    invOf_eq_nonsing_inv, invOf_eq_nonsing_inv]

/-- Top-left block of the inverse of a `2 × 2` block matrix (Schur complement of `D`). -/
theorem inv_fromBlocks_toBlocks₁₁ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D.det) (hS : IsUnit (A - B * D⁻¹ * C).det) :
    ((fromBlocks A B C D)⁻¹).toBlocks₁₁ = (A - B * D⁻¹ * C)⁻¹ := by
  let := invertibleOfIsUnitDet D hD
  have hS' : IsUnit (A - B * ⅟D * C).det := by rwa [invOf_eq_nonsing_inv]
  let := invertibleOfIsUnitDet _ hS'
  let := fromBlocks₂₂Invertible A B C D
  rw [← invOf_eq_nonsing_inv (fromBlocks A B C D), invOf_fromBlocks₂₂_eq, toBlocks_fromBlocks₁₁,
    invOf_eq_nonsing_inv, invOf_eq_nonsing_inv]

end BlockInverse

section Scattering

open BlockBand.Transmission (matrixImaginaryPart)

variable {q : Type*} [Fintype q] [DecidableEq q]

/-- `I - r*r = 4η R*(-Im X)R` for `r = I - 2iη R`, `R = (z - X)⁻¹`, `η = Im z`. -/
theorem one_sub_oldResponse_conj_mul (z : ℂ) (X : Matrix q q ℂ) (hK : IsUnit (z • 1 - X).det) :
    1 - (oldResponse z X)ᴴ * oldResponse z X =
      ((4 * z.im : ℝ) : ℂ) • ((z • 1 - X)⁻¹ᴴ * (-matrixImaginaryPart X) * (z • 1 - X)⁻¹) := by
  set K := z • (1 : Matrix q q ℂ) - X with hKdef
  set R := K⁻¹
  have hKR : K * R = 1 := mul_nonsing_inv _ hK
  have hRK : R * K = 1 := nonsing_inv_mul _ hK
  have hRKR : Rᴴ * K * R = Rᴴ := by rw [Matrix.mul_assoc, hKR, Matrix.mul_one]
  have hRKhR : Rᴴ * Kᴴ * R = R := by
    rw [← conjTranspose_mul, hKR, conjTranspose_one, Matrix.one_mul]
  have hX : X = z • 1 - K := by rw [hKdef]; abel
  have hXh : Xᴴ = (starRingEnd ℂ z) • 1 - Kᴴ := by
    rw [hX, conjTranspose_sub, conjTranspose_smul, conjTranspose_one]; rfl
  unfold oldResponse matrixImaginaryPart
  rw [hXh]
  conv_rhs => rw [hX]
  simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_sub,
    neg_sub, smul_smul]
  rw [hRKR, hRKhR]
  change 1 - (1 - _ • Rᴴ - (_ • R - _ • (Rᴴ * R))) = _
  have hzc : starRingEnd ℂ z = z - 2 * (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp; ring
  rw [hzc]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  module

/-- For Hermitian `X` and `Im z > 0`, `z - X` is invertible. -/
theorem isUnit_det_sub_hermitian {X : Matrix q q ℂ} (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    IsUnit (z • 1 - X).det := by
  have h : z • (1 : Matrix q q ℂ) - X = ((z.re : ℂ) • 1 - X) + ((z.im : ℂ) * Complex.I) • 1 := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [add_smul]; abel
  rw [h]
  refine isUnit_det_hermitian_add _ ?_ hz
  refine IsHermitian.sub ?_ hX
  simp [IsHermitian, conjTranspose_smul]

/-- For Hermitian `X`, the response `r = I - 2iη(z - X)⁻¹` is unitary. -/
theorem oldResponse_unitary {X : Matrix q q ℂ} (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    (oldResponse z X)ᴴ * oldResponse z X = 1 ∧ oldResponse z X * (oldResponse z X)ᴴ = 1 := by
  have h := one_sub_oldResponse_conj_mul z X (isUnit_det_sub_hermitian hX hz)
  have hIm : matrixImaginaryPart X = 0 := by
    unfold matrixImaginaryPart; rw [hX.eq, sub_self, smul_zero]
  rw [hIm, neg_zero, Matrix.mul_zero, Matrix.zero_mul, smul_zero, sub_eq_zero] at h
  exact ⟨h.symm, mul_eq_one_comm.mp h.symm⟩

end Scattering

section Ports

open BlockBand.Transmission (matrixImaginaryPart)
open BlockBand.Internal.Contracts.TransmissionPath (portBlock nearSchur passiveTransmission
  passiveQ passiveY passiveResolvent conductanceOf etaZ)
open BlockBand.Internal.Contracts.Layers (boundaryZ)

variable {W : ℕ}

theorem portBlock_mul (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    portBlock (A * B) i j = ∑ k, portBlock A i k * portBlock B k j := by
  ext x y
  simp only [portBlock, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

theorem portBlock_conjTranspose (A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    portBlock Aᴴ i j = (portBlock A j i)ᴴ := by
  ext x y; simp [portBlock]

theorem portBlock_one (i j : Fin 2) :
    portBlock (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) i j = if i = j then 1 else 0 := by
  ext x y
  by_cases h : i = j
  · subst h; simp [portBlock, one_apply]
  · simp [portBlock, one_apply, h]

theorem portBlock_sub (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    portBlock (A - B) i j = portBlock A i j - portBlock B i j := by
  ext x y; simp [portBlock]

theorem portBlock_smul (c : ℂ) (A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    portBlock (c • A) i j = c • portBlock A i j := by
  ext x y; simp [portBlock]

theorem trace_eq_sum_portBlock (A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    A.trace = (portBlock A 0 0).trace + (portBlock A 1 1).trace := by
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, portBlock]

/-- One-port conductance `Re Tr(I - r_jj* r_jj)` of the diagonal port block `j`. -/
def blockConductance (r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) : ℝ :=
  (1 - (portBlock r j j)ᴴ * portBlock r j j).trace.re

/-- For a unitary two-port matrix the two one-port conductances agree. -/
theorem blockConductance_symm {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (h1 : Sᴴ * S = 1) (h2 : S * Sᴴ = 1) : blockConductance S 0 = blockConductance S 1 := by
  have e1 := congrArg (fun A => portBlock A 0 0) h1
  have e2 := congrArg (fun A => portBlock A 1 1) h2
  simp only [portBlock_mul, portBlock_conjTranspose, portBlock_one, Fin.sum_univ_two,
    ite_true] at e1 e2
  unfold blockConductance
  have hA : 1 - (portBlock S 0 0)ᴴ * portBlock S 0 0 = (portBlock S 1 0)ᴴ * portBlock S 1 0 := by
    rw [← e1]; abel
  have hB : (portBlock S 1 0) * (portBlock S 1 0)ᴴ = 1 - portBlock S 1 1 * (portBlock S 1 1)ᴴ := by
    rw [← e2]; abel
  rw [hA, trace_mul_comm, hB, trace_sub, trace_sub, trace_mul_comm (portBlock S 1 1)]

/-- The total conductance of a block-diagonal two-port response is the sum of the one-port
conductances. -/
theorem conductance_eq_add_of_blockDiag {r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (h01 : portBlock r 0 1 = 0) (h10 : portBlock r 1 0 = 0) :
    (1 - rᴴ * r).trace.re = blockConductance r 0 + blockConductance r 1 := by
  rw [trace_eq_sum_portBlock, Complex.add_re]
  simp only [portBlock_sub, portBlock_mul, portBlock_conjTranspose, portBlock_one,
    Fin.sum_univ_two, ite_true, h01, h10, conjTranspose_zero, Matrix.zero_mul, add_zero,
    zero_add]
  rfl

/-- The two ports as a sum of index types. -/
def portSumEquiv (W : ℕ) : Fin W ⊕ Fin W ≃ Fin 2 × Fin W where
  toFun x := match x with
    | Sum.inl a => (0, a)
    | Sum.inr a => (1, a)
  invFun y := if y.1 = 0 then Sum.inl y.2 else Sum.inr y.2
  left_inv x := by cases x <;> simp
  right_inv y := by
    obtain ⟨i, a⟩ := y
    fin_cases i <;> simp

theorem portBlock_hermitian {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (i : Fin 2) : (portBlock X i i).IsHermitian := by
  rw [IsHermitian, ← portBlock_conjTranspose, hX.eq]

/-- **Near block of the two-port resolvent**: for Hermitian `X` and `Im z > 0`,
`[(z - X)⁻¹]₀₀ = (z - X₀₀ - X₀₁(z - X₁₁)⁻¹X₁₀)⁻¹ = (z - nearSchur z X)⁻¹`, and the latter matrix is
invertible. -/
theorem portBlock_inv_zero {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    portBlock ((z • 1 - X)⁻¹) 0 0 = (z • 1 - nearSchur z X)⁻¹ ∧
      IsUnit (z • 1 - nearSchur z X).det := by
  set e := portSumEquiv W
  have hD : IsUnit (z • 1 - portBlock X 1 1).det :=
    isUnit_det_sub_hermitian (portBlock_hermitian hX 1) hz
  have hX10 : portBlock X 1 0 = (portBlock X 0 1)ᴴ := by
    rw [← portBlock_conjTranspose, hX.eq]
  have hS : IsUnit (z • 1 - nearSchur z X).det := by
    apply isUnit_det_of_im_pos
    intro v hv
    have hIm : ∀ u : Fin W → ℂ, 0 ≤ (star u ⬝ᵥ (z • 1 - portBlock X 1 1) *ᵥ u).im := by
      intro u
      rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
        star_dotProduct_self_eq, Complex.sub_im, smul_eq_mul]
      have h0 := (portBlock_hermitian hX 1).im_star_dotProduct_mulVec_self u
      rw [RCLike.im_to_complex] at h0
      rw [h0]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
        sub_zero]
      exact mul_nonneg hz.le (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
    have hQ := im_oldSchur_nonpos (z • 1 - portBlock X 1 1) (portBlock X 0 1)ᴴ hD hIm v
    simp only [oldSchur, conjTranspose_conjTranspose] at hQ
    have h00 := (portBlock_hermitian hX 0).im_star_dotProduct_mulVec_self v
    rw [RCLike.im_to_complex] at h00
    simp only [nearSchur, hX10]
    rw [sub_mulVec, smul_mulVec, one_mulVec, add_mulVec, dotProduct_sub, dotProduct_add,
      dotProduct_smul, star_dotProduct_self_eq, Complex.sub_im, Complex.add_im, smul_eq_mul, h00]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    have := sum_normSq_pos hv
    nlinarith
  refine ⟨?_, hS⟩
  have hblk : (z • 1 - X).submatrix e e = fromBlocks (z • 1 - portBlock X 0 0)
      (-portBlock X 0 1) (-portBlock X 1 0) (z • 1 - portBlock X 1 1) := by
    ext (a | a) (b | b) <;> simp [e, portSumEquiv, portBlock, one_apply]
  have h11 := inv_fromBlocks_toBlocks₁₁ (z • 1 - portBlock X 0 0) (-portBlock X 0 1)
    (-portBlock X 1 0) (z • 1 - portBlock X 1 1) hD (by
      have : z • 1 - portBlock X 0 0 - -portBlock X 0 1 * (z • 1 - portBlock X 1 1)⁻¹ *
          -portBlock X 1 0 = z • 1 - nearSchur z X := by
        simp only [nearSchur, neg_mul, mul_neg, neg_neg]; abel
      rw [this]; exact hS)
  rw [← hblk, inv_submatrix_equiv] at h11
  have : z • 1 - portBlock X 0 0 - -portBlock X 0 1 * (z • 1 - portBlock X 1 1)⁻¹ *
      -portBlock X 1 0 = z • 1 - nearSchur z X := by
    simp only [nearSchur, neg_mul, mul_neg, neg_neg]; abel
  rw [this] at h11
  rw [← h11]
  ext a b
  simp [e, portSumEquiv, portBlock, toBlocks₁₁]

/-- The one-port conductance of the near port of a Hermitian two-port `X` is the conductance
`Tr T` of the near passive coordinate `nearSchur z_∂ X`. -/
theorem blockConductance_zero_eq (b E : ℝ) (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    blockConductance (oldResponse (boundaryZ b E) X) 0 =
      conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) X)) := by
  obtain ⟨hblk, hS⟩ := portBlock_inv_zero hX hz
  have hr : portBlock (oldResponse (boundaryZ b E) X) 0 0 =
      oldResponse (boundaryZ b E) (nearSchur (boundaryZ b E) X) := by
    unfold oldResponse
    rw [portBlock_sub, portBlock_one, portBlock_smul, hblk]
    simp
  unfold blockConductance
  rw [hr, one_sub_oldResponse_conj_mul _ _ hS]
  rfl

open BlockBand.Internal.Contracts.Layers (matchedDistance blockTrace matchedA)
open BlockBand.Internal.Contracts.Critical (conductance)

/-- Near-port conductance of a Hermitian two-port self-energy. -/
def nearConductance (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  conductanceOf (passiveTransmission b e (nearSchur (boundaryZ b e) X))

/-- Port swap. -/
def portSwap (W : ℕ) : Fin 2 × Fin W ≃ Fin 2 × Fin W :=
  (Equiv.swap (0 : Fin 2) 1).prodCongr (Equiv.refl _)

/-- **Case 1 of Step 3**: if the old outer resolvent is the two-port resolvent of a Hermitian
`Xp` with the two ports exchanged, then `d(X₀) = d(Xp)` and `g₀ = 0` (unitary response). -/
theorem case1_conclusions (b e : ℝ) (hz : 0 < (boundaryZ b e).im)
    {X₀ Xp : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXp : Xp.IsHermitian)
    (h : (boundaryZ b e • 1 - X₀)⁻¹ =
      ((boundaryZ b e • 1 - Xp)⁻¹).submatrix (portSwap W) (portSwap W)) :
    matchedDistance b e X₀ = matchedDistance b e Xp ∧
      conductance (oldResponse (boundaryZ b e) X₀) = 0 := by
  constructor
  · have hbt : ∀ i : Fin 2, blockTrace ((boundaryZ b e • 1 - X₀)⁻¹) i =
        blockTrace ((boundaryZ b e • 1 - Xp)⁻¹) (Equiv.swap (0 : Fin 2) 1 i) := by
      intro i; rw [h]; rfl
    unfold matchedDistance
    rw [hbt, hbt]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact max_comm _ _
  · have hr : oldResponse (boundaryZ b e) X₀ =
        (oldResponse (boundaryZ b e) Xp).submatrix (portSwap W) (portSwap W) := by
      unfold oldResponse
      rw [h]
      ext x y
      simp [submatrix_apply, one_apply, (portSwap W).injective.eq_iff]
    obtain ⟨hu, -⟩ := oldResponse_unitary hXp hz
    unfold conductance
    rw [hr, conjTranspose_submatrix, submatrix_mul_equiv, hu, submatrix_one_equiv, sub_self,
      trace_zero, Complex.zero_re]

/-- **Case 2 of Step 3**: if the old outer resolvent is block diagonal with diagonal blocks the
near-port blocks of two Hermitian two-port resolvents (`XR` at its port `0`, `XL` at its port
`1`), then `d(X₀) ≤ max(d(XR), d(XL))` and `g₀` is the sum of the two near conductances. -/
theorem case2_conclusions (b e : ℝ) (hz : 0 < (boundaryZ b e).im)
    {X₀ XR XL : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hR : XR.IsHermitian)
    (hLh : XL.IsHermitian)
    (h11 : portBlock ((boundaryZ b e • 1 - X₀)⁻¹) 1 1 = portBlock ((boundaryZ b e • 1 - XR)⁻¹) 0 0)
    (h00 : portBlock ((boundaryZ b e • 1 - X₀)⁻¹) 0 0 = portBlock ((boundaryZ b e • 1 - XL)⁻¹) 1 1)
    (h01 : portBlock ((boundaryZ b e • 1 - X₀)⁻¹) 0 1 = 0)
    (h10 : portBlock ((boundaryZ b e • 1 - X₀)⁻¹) 1 0 = 0) :
    matchedDistance b e X₀ ≤ max (matchedDistance b e XR) (matchedDistance b e XL) ∧
      conductance (oldResponse (boundaryZ b e) X₀) =
        nearConductance b e XR + nearConductance b e XL := by
  have hbt : ∀ (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2),
      blockTrace M i = (W : ℂ)⁻¹ * (portBlock M i i).trace := by
    intro M i; simp [blockTrace, Matrix.trace, portBlock]
  constructor
  · unfold matchedDistance
    simp only [hbt]
    rw [h00, h11]
    exact max_le (le_max_of_le_right (le_max_right _ _)) (le_max_of_le_left (le_max_left _ _))
  · set r := oldResponse (boundaryZ b e) X₀
    have hpb : ∀ i j, portBlock r i j = (if i = j then 1 else 0) -
        ((2 * (boundaryZ b e).im : ℝ) * Complex.I) •
          portBlock ((boundaryZ b e • 1 - X₀)⁻¹) i j := by
      intro i j; simp only [r, oldResponse, portBlock_sub, portBlock_one, portBlock_smul]
    have hr01 : portBlock r 0 1 = 0 := by rw [hpb, h01]; simp
    have hr10 : portBlock r 1 0 = 0 := by rw [hpb, h10]; simp
    unfold conductance
    rw [conductance_eq_add_of_blockDiag hr01 hr10, add_comm]
    congr 1
    · have : portBlock r 1 1 = portBlock (oldResponse (boundaryZ b e) XR) 0 0 := by
        rw [hpb, h11]; simp [oldResponse, portBlock_sub, portBlock_one, portBlock_smul]
      unfold blockConductance
      rw [this]
      exact blockConductance_zero_eq b e hz hR
    · have : portBlock r 0 0 = portBlock (oldResponse (boundaryZ b e) XL) 1 1 := by
        rw [hpb, h00]; simp [oldResponse, portBlock_sub, portBlock_one, portBlock_smul]
      obtain ⟨hu1, hu2⟩ := oldResponse_unitary hLh hz
      have hs := blockConductance_symm hu1 hu2
      unfold blockConductance at hs ⊢
      rw [this, ← hs]
      exact blockConductance_zero_eq b e hz hLh

end Ports

end BlockBand.Endpoints
