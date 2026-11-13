module

public import BlockBand.Prelude

/-!
# Sequential collar removal: the Schur determinant algebra

Deterministic matrix identities behind the stage factorization in the proof of the
sequential-collars lemma. Index types: `o` (old interior), `q` (the two
selected outer coordinates, `q = Fin 2 × Fin W` in the application), `g` (the middle block).
Matrices are complex; `⁻¹` is Lean's totalized inverse, used only under explicit `IsUnit det`
hypotheses.

- `collarBefore M Cₒ Cₒ' Aₒ B B' Gm = [[M, (Cₒ 0)], [(Cₒ' ; 0), [[Aₒ, B], [B', Gm]]]]` is
  `H^before_κ` (with `Aₒ = A - e`, `Gm = G - e`), `collarAfter M Cₒ Cₒ' z = [[M, Cₒ], [Cₒ', zI]]`
  is `H^after_κ`; `oldSchur = X_κ = Cₒ' M⁻¹ Cₒ`; `collarK ξ = K_c = A - e - ξ - B(G-e)⁻¹B'`;
  `collarU η K = U = I - 2iη(K + iη)⁻¹`; `oldResponse z X = r_κ = I - 2i Im z (z - X)⁻¹`.
- `det_collarBefore`, `det_collarAfter`: the two Schur determinant formulas;
  `one_sub_collarU_mul_oldResponse`: `I - U r_κ = 2iη(K_c+iη)⁻¹(K_c+ξ-X_κ)(z-X_κ)⁻¹`;
  `collar_stage_factorization`: the stage factorization under the four invertibility
  hypotheses; `collar_stage_factorization_hermitian`: the same when only `M⁻¹` and `(G-e)⁻¹` are
  assumed (Hermitian `A, G`, `M` with numerical range in the closed upper half-plane, `Im z > 0`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix

variable {o q g : Type*} [Fintype o] [Fintype q] [Fintype g]
  [DecidableEq o] [DecidableEq q] [DecidableEq g]

/-- `H^before_κ`: old interior, two outer coordinates and the middle block. -/
def collarBefore (M : Matrix o o ℂ) (Co : Matrix o q ℂ) (Co' : Matrix q o ℂ)
    (Ao : Matrix q q ℂ) (Bo : Matrix q g ℂ) (Bo' : Matrix g q ℂ) (Gm : Matrix g g ℂ) :
    Matrix (o ⊕ (q ⊕ g)) (o ⊕ (q ⊕ g)) ℂ :=
  fromBlocks M (fromCols Co 0) (fromRows Co' 0) (fromBlocks Ao Bo Bo' Gm)

/-- `H^after_κ`: the outer diagonals replaced by `zI` and the middle block deleted. -/
def collarAfter (M : Matrix o o ℂ) (Co : Matrix o q ℂ) (Co' : Matrix q o ℂ) (z : ℂ) :
    Matrix (o ⊕ q) (o ⊕ q) ℂ :=
  fromBlocks M Co Co' (z • 1)

/-- `X_κ = Cₒ' M_κ⁻¹ Cₒ`, the Schur complement term of the old network. -/
def oldSchur (M : Matrix o o ℂ) (Co : Matrix o q ℂ) (Co' : Matrix q o ℂ) : Matrix q q ℂ :=
  Co' * M⁻¹ * Co

/-- `K_c = A - e - ξ - B(G-e)⁻¹B*`, with `Aₒ = A - e`, `Gm = G - e`. -/
def collarK (ξ : ℝ) (Ao : Matrix q q ℂ) (Bo : Matrix q g ℂ) (Bo' : Matrix g q ℂ)
    (Gm : Matrix g g ℂ) : Matrix q q ℂ :=
  Ao - (ξ : ℂ) • 1 - Bo * Gm⁻¹ * Bo'

/-- `U = I - 2iη(K_c + iη)⁻¹`. -/
def collarU (η : ℝ) (K : Matrix q q ℂ) : Matrix q q ℂ :=
  1 - ((2 * η : ℝ) * Complex.I) • (K + ((η : ℂ) * Complex.I) • 1)⁻¹

/-- `r_κ = I - 2iη(z - X_κ)⁻¹`, `η = Im z`. -/
def oldResponse (z : ℂ) (X : Matrix q q ℂ) : Matrix q q ℂ :=
  1 - ((2 * z.im : ℝ) * Complex.I) • (z • 1 - X)⁻¹

/-- Eliminating the old interior and then the middle block. -/
theorem det_collarBefore (M : Matrix o o ℂ) (Co : Matrix o q ℂ) (Co' : Matrix q o ℂ)
    (Ao : Matrix q q ℂ) (Bo : Matrix q g ℂ) (Bo' : Matrix g q ℂ) (Gm : Matrix g g ℂ)
    (hM : IsUnit M.det) (hG : IsUnit Gm.det) :
    (collarBefore M Co Co' Ao Bo Bo' Gm).det =
      M.det * Gm.det * (Ao - oldSchur M Co Co' - Bo * Gm⁻¹ * Bo').det := by
  let := invertibleOfIsUnitDet M hM
  let := invertibleOfIsUnitDet Gm hG
  unfold collarBefore
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have h1 : fromRows Co' (0 : Matrix g o ℂ) * M⁻¹ * fromCols Co (0 : Matrix o g ℂ) =
      fromBlocks (Co' * M⁻¹ * Co) 0 0 0 := by
    rw [fromRows_mul, fromRows_mul, mul_fromCols, mul_fromCols]
    ext (i | i) (j | j) <;> simp
  have h2 : fromBlocks Ao Bo Bo' Gm - fromBlocks (Co' * M⁻¹ * Co) 0 0 0 =
      fromBlocks (Ao - Co' * M⁻¹ * Co) Bo Bo' Gm := by
    ext (i | i) (j | j) <;> simp
  rw [h1, h2, det_fromBlocks₂₂, invOf_eq_nonsing_inv]
  unfold oldSchur
  ring

/-- `det H^after = det M det(z - X)`. -/
theorem det_collarAfter (M : Matrix o o ℂ) (Co : Matrix o q ℂ) (Co' : Matrix q o ℂ) (z : ℂ)
    (hM : IsUnit M.det) :
    (collarAfter M Co Co' z).det = M.det * (z • 1 - oldSchur M Co Co').det := by
  let := invertibleOfIsUnitDet M hM
  unfold collarAfter
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  rfl

/-- The exact identity `I - U r_κ = 2iη(K_c+iη)⁻¹(K_c+ξ-X_κ)(z-X_κ)⁻¹`, `z = ξ + iη`. -/
theorem one_sub_collarU_mul_oldResponse (z : ℂ) (X K : Matrix q q ℂ)
    (hK : IsUnit (K + ((z.im : ℂ) * Complex.I) • 1).det) (hX : IsUnit (z • 1 - X).det) :
    1 - collarU z.im K * oldResponse z X =
      ((2 * z.im : ℝ) * Complex.I) • ((K + ((z.im : ℂ) * Complex.I) • 1)⁻¹ *
        (K + (z.re : ℂ) • 1 - X) * (z • 1 - X)⁻¹) := by
  set P := (K + ((z.im : ℂ) * Complex.I) • 1)⁻¹
  set Q := (z • 1 - X)⁻¹
  set a : ℂ := ((2 * z.im : ℝ) * Complex.I)
  have hP : P * (K + ((z.im : ℂ) * Complex.I) • 1) = 1 := nonsing_inv_mul _ hK
  have hQ : (z • 1 - X) * Q = 1 := mul_nonsing_inv _ hX
  have hz : (K + (z.re : ℂ) • 1 - X) =
      (z • 1 - X) + (K + ((z.im : ℂ) * Complex.I) • 1) - a • 1 := by
    have : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
    simp only [a]
    rw [show (z • (1 : Matrix q q ℂ)) = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • 1 from by
      rw [← this]]
    push_cast
    module
  have e1 : P * (z • 1 - X + (K + ((z.im : ℂ) * Complex.I) • 1) - a • 1) * Q =
      P + Q - a • (P * Q) := by
    rw [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul,
      Matrix.mul_assoc P (z • 1 - X) Q, hQ, hP, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [hz, e1]
  unfold collarU oldResponse
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul]
  simp only [a]
  push_cast
  module

/-- The stage factorization: if `M`, `G - e`, `z - X_κ` and
`K_c + iη` are invertible and `η = Im z ≠ 0`, then
`det H^before / det H^after = det(G-e) · det(K_c+iη)/(2iη)^{|q|} · det(I - U r_κ)`. -/
theorem collar_stage_factorization (M : Matrix o o ℂ) (Co : Matrix o q ℂ) (Co' : Matrix q o ℂ)
    (Ao : Matrix q q ℂ) (Bo : Matrix q g ℂ) (Bo' : Matrix g q ℂ) (Gm : Matrix g g ℂ) (z : ℂ)
    (hM : IsUnit M.det) (hG : IsUnit Gm.det)
    (hK : IsUnit (collarK z.re Ao Bo Bo' Gm + ((z.im : ℂ) * Complex.I) • 1).det)
    (hX : IsUnit (z • 1 - oldSchur M Co Co').det) (hη : z.im ≠ 0) :
    (collarBefore M Co Co' Ao Bo Bo' Gm).det / (collarAfter M Co Co' z).det =
      Gm.det * ((collarK z.re Ao Bo Bo' Gm + ((z.im : ℂ) * Complex.I) • 1).det /
          (((2 * z.im : ℝ) : ℂ) * Complex.I) ^ Fintype.card q) *
        (1 - collarU z.im (collarK z.re Ao Bo Bo' Gm) *
          oldResponse z (oldSchur M Co Co')).det := by
  rw [det_collarBefore M Co Co' Ao Bo Bo' Gm hM hG, det_collarAfter M Co Co' z hM,
    one_sub_collarU_mul_oldResponse z _ _ hK hX, det_smul, det_mul, det_mul,
    det_nonsing_inv, det_nonsing_inv]
  have hKX : collarK z.re Ao Bo Bo' Gm + (z.re : ℂ) • 1 - oldSchur M Co Co' =
      Ao - oldSchur M Co Co' - Bo * Gm⁻¹ * Bo' := by
    unfold collarK; abel
  rw [hKX]
  have h2 : (((2 * z.im : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    have : ((2 * z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hη
    exact mul_ne_zero this Complex.I_ne_zero
  have hMd := hM.ne_zero
  have hKd := hK.ne_zero
  have hXd := hX.ne_zero
  simp only [Ring.inverse_eq_inv']
  field_simp
  have h2' : (Complex.I * ((2 * z.im : ℝ) : ℂ)) ^ Fintype.card q ≠ 0 :=
    pow_ne_zero _ (by rw [mul_comm]; exact h2)
  rw [mul_div_assoc, div_self h2', mul_one]

/-- A square matrix whose numerical range lies strictly in the upper half-plane is invertible. -/
theorem isUnit_det_of_im_pos (A : Matrix q q ℂ)
    (h : ∀ v : q → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ A *ᵥ v).im) : IsUnit A.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have := h v hv
  rw [hAv, dotProduct_zero] at this
  simp at this

omit [DecidableEq q] in
/-- `v* v = Σ |vᵢ|²`. -/
theorem star_dotProduct_self_eq (v : q → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

omit [DecidableEq q] in
/-- `Σ |vᵢ|² > 0` for `v ≠ 0`. -/
theorem sum_normSq_pos {v : q → ℂ} (hv : v ≠ 0) : 0 < ∑ i, Complex.normSq (v i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
    (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i))

/-- `K + iη` is invertible for Hermitian `K` and `η > 0`. -/
theorem isUnit_det_hermitian_add (K : Matrix q q ℂ) (hK : K.IsHermitian) {η : ℝ} (hη : 0 < η) :
    IsUnit (K + ((η : ℂ) * Complex.I) • 1).det := by
  apply isUnit_det_of_im_pos
  intro v hv
  rw [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
    star_dotProduct_self_eq, Complex.add_im, smul_eq_mul]
  have h0 := hK.im_star_dotProduct_mulVec_self v
  rw [RCLike.im_to_complex] at h0
  rw [h0]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.I_re, Complex.I_im]
  have := sum_normSq_pos hv
  nlinarith

omit [DecidableEq q] in
/-- If `M` has numerical range in the closed upper half-plane, then `X = Cᴴ M⁻¹ C` has numerical
range in the closed lower half-plane. -/
theorem im_oldSchur_nonpos (M : Matrix o o ℂ) (Co : Matrix o q ℂ) (hM : IsUnit M.det)
    (hIm : ∀ u : o → ℂ, 0 ≤ (star u ⬝ᵥ M *ᵥ u).im) (v : q → ℂ) :
    (star v ⬝ᵥ oldSchur M Co (Co)ᴴ *ᵥ v).im ≤ 0 := by
  set w := Co *ᵥ v
  set u := M⁻¹ *ᵥ w
  have hw : M *ᵥ u = w := by
    simp only [u, mulVec_mulVec, mul_nonsing_inv _ hM, one_mulVec]
  have h1 : star v ⬝ᵥ oldSchur M Co (Co)ᴴ *ᵥ v = star w ⬝ᵥ u := by
    simp only [oldSchur, w, u]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  have h2 : star w ⬝ᵥ u = star (star u ⬝ᵥ M *ᵥ u) := by
    rw [← hw, star_dotProduct]
  rw [h1, h2, Complex.star_def, Complex.conj_im]
  linarith [hIm u]

/-- `z - Cᴴ M⁻¹ C` is invertible when `Im z > 0` and `M` has numerical range in the closed
upper half-plane. -/
theorem isUnit_det_sub_oldSchur (M : Matrix o o ℂ) (Co : Matrix o q ℂ) (hM : IsUnit M.det)
    (hIm : ∀ u : o → ℂ, 0 ≤ (star u ⬝ᵥ M *ᵥ u).im) {z : ℂ} (hz : 0 < z.im) :
    IsUnit (z • 1 - oldSchur M Co (Co)ᴴ).det := by
  apply isUnit_det_of_im_pos
  intro v hv
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    star_dotProduct_self_eq, Complex.sub_im, smul_eq_mul]
  have h0 := im_oldSchur_nonpos M Co hM hIm v
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  have := sum_normSq_pos hv
  nlinarith

omit [Fintype q] in
/-- `K_c` is Hermitian for Hermitian `A - e` and `G - e`. -/
theorem collarK_isHermitian (ξ : ℝ) {Ao : Matrix q q ℂ} (Bo : Matrix q g ℂ) {Gm : Matrix g g ℂ}
    (hA : Ao.IsHermitian) (hG : Gm.IsHermitian) :
    (collarK ξ Ao Bo (Bo)ᴴ Gm).IsHermitian := by
  unfold collarK
  refine (hA.sub ?_).sub (isHermitian_mul_mul_conjTranspose Bo hG.inv)
  simp [IsHermitian, conjTranspose_smul]

/-- The stage factorization in its Hermitian setting: `Aₒ = A - e`, `Gm = G - e`
Hermitian, the old interior `M` invertible with numerical range in the closed upper
half-plane, couplings `Cₒ, Cₒᴴ` and `B, Bᴴ`, and `Im z > 0`. -/
theorem collar_stage_factorization_hermitian (M : Matrix o o ℂ) (Co : Matrix o q ℂ)
    (Ao : Matrix q q ℂ) (Bo : Matrix q g ℂ) (Gm : Matrix g g ℂ) (z : ℂ)
    (hM : IsUnit M.det) (hIm : ∀ u : o → ℂ, 0 ≤ (star u ⬝ᵥ M *ᵥ u).im)
    (hA : Ao.IsHermitian) (hGh : Gm.IsHermitian) (hG : IsUnit Gm.det) (hz : 0 < z.im) :
    (collarBefore M Co (Co)ᴴ Ao Bo (Bo)ᴴ Gm).det / (collarAfter M Co (Co)ᴴ z).det =
      Gm.det * ((collarK z.re Ao Bo (Bo)ᴴ Gm + ((z.im : ℂ) * Complex.I) • 1).det /
          (((2 * z.im : ℝ) : ℂ) * Complex.I) ^ Fintype.card q) *
        (1 - collarU z.im (collarK z.re Ao Bo (Bo)ᴴ Gm) *
          oldResponse z (oldSchur M Co (Co)ᴴ)).det :=
  collar_stage_factorization M Co _ Ao Bo _ Gm z hM hG
    (isUnit_det_hermitian_add _ (collarK_isHermitian _ Bo hA hGh) hz)
    (isUnit_det_sub_oldSchur M Co hM hIm hz) hz.ne'

omit [DecidableEq q] in
/-- A Hermitian matrix plus `i·diag(d)` with `d ≥ 0` has numerical range in the closed upper
half-plane. -/
theorem im_star_dotProduct_herm_add_diag_nonneg [DecidableEq q] (H : Matrix q q ℂ)
    (hH : H.IsHermitian) (d : q → ℝ) (hd : ∀ i, 0 ≤ d i) (u : q → ℂ) :
    0 ≤ (star u ⬝ᵥ (H + diagonal fun i => (d i : ℂ) * Complex.I) *ᵥ u).im := by
  rw [add_mulVec, dotProduct_add, Complex.add_im]
  have h0 := hH.im_star_dotProduct_mulVec_self u
  rw [RCLike.im_to_complex] at h0
  rw [h0, zero_add]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.im_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have : star (u i) * ((d i : ℂ) * Complex.I * u i) =
      ((d i * Complex.normSq (u i) : ℝ) : ℂ) * Complex.I := by
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [this]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero]
  exact mul_nonneg (hd i) (Complex.normSq_nonneg _)

end BlockBand.Endpoints
