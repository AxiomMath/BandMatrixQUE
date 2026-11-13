module

public import BlockBand.Endpoints.Response.PassDerivativeNorms

/-!
# Schur reconstruction of the full inverse from the interior Schur complement

For `𝓜 = [[A, B], [B*, z]]` (`A` Hermitian, `Im z = η > 0`) the interior Schur complement is
`S = A - z⁻¹ B B*`; its imaginary part is `β B B*`, `β = η/|z|² = -Im z⁻¹ > 0`.

* `schurFullInv`: the explicit block inverse `[[S⁻¹, -z⁻¹S⁻¹B], [-z⁻¹B*S⁻¹, z⁻¹ + z⁻²B*S⁻¹B]]`;
  `fromBlocks_mul_schurFullInv`: it is a right inverse when `S` is invertible, hence
  `isUnit_det_fromBlocks_of_schur` (invertibility of `𝓜` reduces to that of `S`) and
  `fromBlocks_inv_eq_schurFullInv`.
* Ward bounds, using only `Im S = β B B*` (no moment of `‖B‖`):
  `‖B*S⁻¹‖² ≤ ‖S⁻¹‖/β`, `‖S⁻¹B‖² ≤ ‖S⁻¹‖/β`, `‖B*S⁻¹B‖ ≤ 1/β`.
* `norm_fromBlocks_inv_le`: `‖𝓜⁻¹‖ ≤ ‖S⁻¹‖ + 2|z|⁻¹ √(‖S⁻¹‖/β) + |z|⁻¹ + |z|⁻²/β`
  (Euclidean operator norms). The coupling norm `‖B‖` does not appear, so no moments of the
  endpoint-coupling norms are needed.
* `isUnit_schur_of_hermitianPart`: `S` is invertible as soon as its Hermitian part
  `A - Re(z⁻¹)BB*` is.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix Complex
open scoped Matrix.Norms.L2Operator ComplexConjugate

variable {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

/-!
### Operator norm of a block matrix
-/

omit [DecidableEq m] [DecidableEq p] in
theorem vecNormSq_sum (x : m ⊕ p → ℂ) :
    vecNormSq x = vecNormSq (x ∘ Sum.inl) + vecNormSq (x ∘ Sum.inr) := by
  simp [vecNormSq, Fintype.sum_sum_type]

omit [DecidableEq m] [DecidableEq p] in
theorem vecNormSq_add_le (x y : m → ℂ) :
    Real.sqrt (vecNormSq (x + y)) ≤ Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y) := by
  rw [vecNormSq_eq_norm_sq, vecNormSq_eq_norm_sq, vecNormSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    map_add]
  exact norm_add_le _ _

omit [DecidableEq m] [DecidableEq p] in
theorem sqrt_vecNormSq_mulVec_le {k l : Type*} [Fintype k] [Fintype l] [DecidableEq l]
    (X : Matrix k l ℂ)
    (v : l → ℂ) : Real.sqrt (vecNormSq (X *ᵥ v)) ≤ ‖X‖ * Real.sqrt (vecNormSq v) := by
  rw [← Real.sqrt_sq (norm_nonneg X), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (vecNormSq_mulVec_le X v)

/-- `‖[[P, Q], [R, T]]‖ ≤ ‖P‖ + ‖Q‖ + ‖R‖ + ‖T‖` (Euclidean operator norms). -/
theorem norm_fromBlocks_le (P : Matrix m m ℂ) (Q : Matrix m p ℂ) (R : Matrix p m ℂ)
    (T : Matrix p p ℂ) : ‖fromBlocks P Q R T‖ ≤ ‖P‖ + ‖Q‖ + ‖R‖ + ‖T‖ := by
  refine l2_opNorm_le_of_vecNormSq (by positivity) fun v => ?_
  rw [fromBlocks_mulVec, vecNormSq_sum, vecNormSq_sum v]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  set x := v ∘ Sum.inl
  set y := v ∘ Sum.inr
  set a := Real.sqrt (vecNormSq x)
  set c := Real.sqrt (vecNormSq y)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have h1 : Real.sqrt (vecNormSq (P *ᵥ x + Q *ᵥ y)) ≤ ‖P‖ * a + ‖Q‖ * c :=
    (vecNormSq_add_le _ _).trans (add_le_add (sqrt_vecNormSq_mulVec_le P x)
      (sqrt_vecNormSq_mulVec_le Q y))
  have h2 : Real.sqrt (vecNormSq (R *ᵥ x + T *ᵥ y)) ≤ ‖R‖ * a + ‖T‖ * c :=
    (vecNormSq_add_le _ _).trans (add_le_add (sqrt_vecNormSq_mulVec_le R x)
      (sqrt_vecNormSq_mulVec_le T y))
  have hx : vecNormSq x = a ^ 2 := (Real.sq_sqrt (vecNormSq_nonneg _)).symm
  have hy : vecNormSq y = c ^ 2 := (Real.sq_sqrt (vecNormSq_nonneg _)).symm
  have h1' : vecNormSq (P *ᵥ x + Q *ᵥ y) ≤ (‖P‖ * a + ‖Q‖ * c) ^ 2 := by
    rw [← Real.sq_sqrt (vecNormSq_nonneg (P *ᵥ x + Q *ᵥ y))]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have h2' : vecNormSq (R *ᵥ x + T *ᵥ y) ≤ (‖R‖ * a + ‖T‖ * c) ^ 2 := by
    rw [← Real.sq_sqrt (vecNormSq_nonneg (R *ᵥ x + T *ᵥ y))]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  rw [hx, hy]
  have hP := norm_nonneg P
  have hQ := norm_nonneg Q
  have hR := norm_nonneg R
  have hT := norm_nonneg T
  have hac : a ≤ Real.sqrt (a ^ 2 + c ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hca : c ≤ Real.sqrt (a ^ 2 + c ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  set r := Real.sqrt (a ^ 2 + c ^ 2)
  have hr2 : r ^ 2 = a ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
  have e1 : ‖P‖ * a + ‖Q‖ * c ≤ (‖P‖ + ‖Q‖) * r := by nlinarith
  have e2 : ‖R‖ * a + ‖T‖ * c ≤ (‖R‖ + ‖T‖) * r := by nlinarith
  have f1 : (‖P‖ * a + ‖Q‖ * c) ^ 2 ≤ ((‖P‖ + ‖Q‖) * r) ^ 2 :=
    pow_le_pow_left₀ (by positivity) e1 2
  have f2 : (‖R‖ * a + ‖T‖ * c) ^ 2 ≤ ((‖R‖ + ‖T‖) * r) ^ 2 :=
    pow_le_pow_left₀ (by positivity) e2 2
  calc vecNormSq (P *ᵥ x + Q *ᵥ y) + vecNormSq (R *ᵥ x + T *ᵥ y)
      ≤ ((‖P‖ + ‖Q‖) * r) ^ 2 + ((‖R‖ + ‖T‖) * r) ^ 2 := add_le_add (h1'.trans f1) (h2'.trans f2)
    _ ≤ (‖P‖ + ‖Q‖ + ‖R‖ + ‖T‖) ^ 2 * (a ^ 2 + c ^ 2) := by
        rw [mul_pow, mul_pow, hr2]
        have : (‖P‖ + ‖Q‖) ^ 2 + (‖R‖ + ‖T‖) ^ 2 ≤ (‖P‖ + ‖Q‖ + ‖R‖ + ‖T‖) ^ 2 := by
          nlinarith
        nlinarith [sq_nonneg a, sq_nonneg c]

/-!
### The explicit block inverse
-/

/-- The block inverse of `[[A, B], [B*, z]]` built from `Sinv = S⁻¹`, `S = A - z⁻¹BB*`. -/
def schurFullInv (B : Matrix m p ℂ) (z : ℂ) (Sinv : Matrix m m ℂ) :
    Matrix (m ⊕ p) (m ⊕ p) ℂ :=
  fromBlocks Sinv (-(z⁻¹ • (Sinv * B))) (-(z⁻¹ • (Bᴴ * Sinv)))
    (z⁻¹ • (1 : Matrix p p ℂ) + (z⁻¹ * z⁻¹) • (Bᴴ * Sinv * B))

theorem fromBlocks_mul_schurFullInv {A : Matrix m m ℂ} {B : Matrix m p ℂ} {z : ℂ} (hz : z ≠ 0)
    {Sinv : Matrix m m ℂ} (hS : (A - z⁻¹ • (B * Bᴴ)) * Sinv = 1) :
    fromBlocks A B Bᴴ (z • (1 : Matrix p p ℂ)) * schurFullInv B z Sinv = 1 := by
  have hA : A * Sinv = 1 + z⁻¹ • (B * Bᴴ * Sinv) := by
    rw [sub_mul, smul_mul_assoc, sub_eq_iff_eq_add] at hS
    rw [hS]
  rw [schurFullInv, fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, hA]
    abel
  · rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, hA, Matrix.mul_add,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.one_mul,
      Matrix.smul_mul, smul_add, smul_smul]
    simp only [Matrix.mul_assoc]
    abel
  · rw [Matrix.mul_neg, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hz,
      one_smul]
    abel
  · rw [Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul,
      smul_smul, mul_inv_cancel₀ hz, one_smul, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    simp only [Matrix.mul_assoc]
    abel

/-- Invertibility reduces to the Schur complement: if `S = A - z⁻¹BB*` is invertible and
`z ≠ 0`, then `[[A, B], [B*, z]]` is invertible. -/
theorem isUnit_det_fromBlocks_of_schur {A : Matrix m m ℂ} {B : Matrix m p ℂ} {z : ℂ}
    (hz : z ≠ 0) (hS : IsUnit (A - z⁻¹ • (B * Bᴴ)).det) :
    IsUnit (fromBlocks A B Bᴴ (z • (1 : Matrix p p ℂ))).det :=
  isUnit_det_of_right_inverse
    (fromBlocks_mul_schurFullInv hz (mul_nonsing_inv _ hS))

theorem fromBlocks_inv_eq_schurFullInv {A : Matrix m m ℂ} {B : Matrix m p ℂ} {z : ℂ}
    (hz : z ≠ 0) (hS : IsUnit (A - z⁻¹ • (B * Bᴴ)).det) :
    (fromBlocks A B Bᴴ (z • (1 : Matrix p p ℂ)))⁻¹ =
      schurFullInv B z (A - z⁻¹ • (B * Bᴴ))⁻¹ :=
  inv_eq_right_inv (fromBlocks_mul_schurFullInv hz (mul_nonsing_inv _ hS))

/-!
### Ward bounds
-/

omit [DecidableEq m] [DecidableEq p] in
/-- `Im⟨u, S u⟩ = β |B* u|²` for `S = A - z⁻¹ B B*`, `A` Hermitian, `β = -Im z⁻¹`. -/
theorem schur_quad_im {A : Matrix m m ℂ} (hA : A.IsHermitian) (B : Matrix m p ℂ) (z : ℂ)
    (u : m → ℂ) :
    (star u ⬝ᵥ ((A - z⁻¹ • (B * Bᴴ)) *ᵥ u)).im = -(z⁻¹).im * vecNormSq (Bᴴ *ᵥ u) := by
  have hg : star u ⬝ᵥ ((B * Bᴴ) *ᵥ u) = (vecNormSq (Bᴴ *ᵥ u) : ℂ) := by
    have := star_dotProduct_gram_mulVec Bᴴ u
    rwa [conjTranspose_conjTranspose] at this
  have hAim : (star u ⬝ᵥ (A *ᵥ u)).im = 0 := by
    have h := star_dotProduct_conjTranspose_mulVec A u
    rw [hA.eq] at h
    have := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im] at this
    linarith
  rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, hg, smul_eq_mul,
    Complex.sub_im, hAim, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
  ring

omit [DecidableEq p] in
/-- Ward bound. If `β |T u|² ≤ |Im⟨u, S u⟩|` for all `u` (`β > 0`) and `S` is invertible,
then `‖T S⁻¹‖² ≤ ‖S⁻¹‖/β`. -/
theorem norm_mul_inv_sq_le_of_ward {S : Matrix m m ℂ} {T : Matrix p m ℂ} {β : ℝ} (hβ : 0 < β)
    (hS : IsUnit S.det) (hW : ∀ u, β * vecNormSq (T *ᵥ u) ≤ |(star u ⬝ᵥ (S *ᵥ u)).im|) :
    ‖T * S⁻¹‖ ^ 2 ≤ ‖S⁻¹‖ / β := by
  have hb : 0 ≤ ‖S⁻¹‖ / β := div_nonneg (norm_nonneg _) hβ.le
  suffices h : ‖T * S⁻¹‖ ≤ Real.sqrt (‖S⁻¹‖ / β) by
    calc ‖T * S⁻¹‖ ^ 2 ≤ Real.sqrt (‖S⁻¹‖ / β) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := Real.sq_sqrt hb
  refine l2_opNorm_le_of_vecNormSq (Real.sqrt_nonneg _) fun x => ?_
  rw [Real.sq_sqrt hb, ← mulVec_mulVec]
  set u := S⁻¹ *ᵥ x
  have hSu : S *ᵥ u = x := by rw [mulVec_mulVec, mul_nonsing_inv _ hS, one_mulVec]
  have h1 := hW u
  rw [hSu] at h1
  have h2 : |(star u ⬝ᵥ x).im| ≤ Real.sqrt (vecNormSq u * vecNormSq x) := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (norm_star_dotProduct_sq_le u x)
  have h3 : vecNormSq u ≤ ‖S⁻¹‖ ^ 2 * vecNormSq x := vecNormSq_mulVec_le _ _
  have h4 : Real.sqrt (vecNormSq u * vecNormSq x) ≤ ‖S⁻¹‖ * vecNormSq x := by
    rw [show ‖S⁻¹‖ * vecNormSq x = Real.sqrt ((‖S⁻¹‖ * vecNormSq x) ^ 2) from
      (Real.sqrt_sq (mul_nonneg (norm_nonneg _) (vecNormSq_nonneg _))).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow]
    nlinarith [vecNormSq_nonneg x]
  have h5 : β * vecNormSq (T *ᵥ u) ≤ ‖S⁻¹‖ * vecNormSq x := h1.trans (h2.trans h4)
  rw [div_mul_eq_mul_div, le_div_iff₀ hβ]
  linarith

/-- Ward bound for the port block. If `β |B* u|² ≤ |Im⟨u, S u⟩|` for all `u` and `S` is
invertible, then `‖B* S⁻¹ B‖ ≤ 1/β`. -/
theorem norm_conjTranspose_mul_inv_mul_le {S : Matrix m m ℂ} {B : Matrix m p ℂ} {β : ℝ}
    (hβ : 0 < β) (hS : IsUnit S.det)
    (hW : ∀ u, β * vecNormSq (Bᴴ *ᵥ u) ≤ |(star u ⬝ᵥ (S *ᵥ u)).im|) :
    ‖Bᴴ * S⁻¹ * B‖ ≤ 1 / β := by
  refine l2_opNorm_le_of_vecNormSq (by positivity) fun y => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  set u := S⁻¹ *ᵥ (B *ᵥ y)
  have hSu : S *ᵥ u = B *ᵥ y := by rw [mulVec_mulVec, mul_nonsing_inv _ hS, one_mulVec]
  have h1 := hW u
  rw [hSu, star_dotProduct_mulVec_eq] at h1
  set a := vecNormSq (Bᴴ *ᵥ u)
  have ha : 0 ≤ a := vecNormSq_nonneg _
  have hy : 0 ≤ vecNormSq y := vecNormSq_nonneg _
  have h2 : |(star (Bᴴ *ᵥ u) ⬝ᵥ y).im| ≤ Real.sqrt (a * vecNormSq y) := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (norm_star_dotProduct_sq_le _ y)
  have h3 : (β * a) ^ 2 ≤ a * vecNormSq y := by
    have := h1.trans h2
    have h0 : 0 ≤ β * a := mul_nonneg hβ.le ha
    calc (β * a) ^ 2 ≤ Real.sqrt (a * vecNormSq y) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = _ := Real.sq_sqrt (mul_nonneg ha hy)
  rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  rcases ha.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact hy
  · have : β ^ 2 * a * a ≤ vecNormSq y * a := by nlinarith
    nlinarith

/-- Reconstruction bound. For `A` Hermitian, `Im z > 0` and `S = A - z⁻¹BB*` invertible:
`‖[[A, B], [B*, z]]⁻¹‖ ≤ ‖S⁻¹‖ + 2|z|⁻¹ √(‖S⁻¹‖/β) + |z|⁻¹ + |z|⁻²/β`, `β = -Im z⁻¹ > 0`. -/
theorem norm_fromBlocks_inv_le {A : Matrix m m ℂ} (hA : A.IsHermitian) (B : Matrix m p ℂ)
    {z : ℂ} (hz : 0 < z.im) (hS : IsUnit (A - z⁻¹ • (B * Bᴴ)).det) :
    ‖(fromBlocks A B Bᴴ (z • (1 : Matrix p p ℂ)))⁻¹‖ ≤
      ‖(A - z⁻¹ • (B * Bᴴ))⁻¹‖ + 2 * ‖z‖⁻¹ * Real.sqrt (‖(A - z⁻¹ • (B * Bᴴ))⁻¹‖ / (-(z⁻¹).im)) +
        ‖z‖⁻¹ + ‖z‖⁻¹ ^ 2 / (-(z⁻¹).im) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz; exact lt_irrefl _ hz
  set S := A - z⁻¹ • (B * Bᴴ) with hSdef
  set β := -(z⁻¹).im with hβdef
  have hβ : 0 < β := by
    rw [hβdef, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hz (Complex.normSq_pos.2 hz0)
  have hW : ∀ u, β * vecNormSq (Bᴴ *ᵥ u) ≤ |(star u ⬝ᵥ (S *ᵥ u)).im| := fun u => by
    rw [schur_quad_im hA B z u]
    exact le_abs_self _
  have hSH : IsUnit Sᴴ.det := by rw [det_conjTranspose]; exact hS.star
  have hWH : ∀ u, β * vecNormSq (Bᴴ *ᵥ u) ≤ |(star u ⬝ᵥ (Sᴴ *ᵥ u)).im| := fun u => by
    rw [star_dotProduct_conjTranspose_mulVec, Complex.star_def, Complex.conj_im, abs_neg]
    exact hW u
  have h1 := norm_mul_inv_sq_le_of_ward hβ hS hW
  have h2 := norm_mul_inv_sq_le_of_ward hβ hSH hWH
  rw [← conjTranspose_nonsing_inv, l2_opNorm_conjTranspose] at h2
  have h2' : ‖S⁻¹ * B‖ = ‖Bᴴ * S⁻¹ᴴ‖ := by
    rw [← l2_opNorm_conjTranspose, conjTranspose_mul]
  have h3 := norm_conjTranspose_mul_inv_mul_le hβ hS hW
  have hsq : ∀ {x : ℝ}, 0 ≤ x → x ^ 2 ≤ ‖S⁻¹‖ / β → x ≤ Real.sqrt (‖S⁻¹‖ / β) :=
    fun hx h => Real.le_sqrt_of_sq_le h
  have e1 : ‖Bᴴ * S⁻¹‖ ≤ Real.sqrt (‖S⁻¹‖ / β) := hsq (norm_nonneg _) h1
  have e2 : ‖S⁻¹ * B‖ ≤ Real.sqrt (‖S⁻¹‖ / β) := by rw [h2']; exact hsq (norm_nonneg _) h2
  rw [show fromBlocks A B Bᴴ (z • (1 : Matrix p p ℂ)) = fromBlocks A B Bᴴ (z • 1) from rfl,
    fromBlocks_inv_eq_schurFullInv hz0 hS, schurFullInv]
  refine (norm_fromBlocks_le _ _ _ _).trans ?_
  rw [norm_neg, norm_neg, norm_smul, norm_smul, norm_inv]
  have e3 : ‖z⁻¹ • (1 : Matrix p p ℂ) + (z⁻¹ * z⁻¹) • (Bᴴ * S⁻¹ * B)‖ ≤
      ‖z‖⁻¹ + ‖z‖⁻¹ ^ 2 / β := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, norm_inv]
      exact (mul_le_mul_of_nonneg_left l2_opNorm_one_le (by positivity)).trans (by simp)
    · rw [norm_smul, norm_mul, norm_inv, ← sq, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hzn : 0 ≤ ‖z‖⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left e1 hzn, mul_le_mul_of_nonneg_left e2 hzn]

omit [DecidableEq p] in
/-- `S = A - z⁻¹BB*` is invertible as soon as its Hermitian part `A - Re(z⁻¹) BB*` is
(`A` Hermitian, `Im z > 0`): a null vector `v` of `S` has `B* v = 0` by the Ward identity. -/
theorem isUnit_schur_of_hermitianPart {A : Matrix m m ℂ} (hA : A.IsHermitian) (B : Matrix m p ℂ)
    {z : ℂ} (hz : 0 < z.im) (hY : IsUnit (A - (((z⁻¹).re : ℝ) : ℂ) • (B * Bᴴ)).det) :
    IsUnit (A - z⁻¹ • (B * Bᴴ)).det := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz; exact lt_irrefl _ hz
  have hβ : 0 < -(z⁻¹).im := by
    rw [Complex.inv_im, neg_div, neg_neg]
    exact div_pos hz (Complex.normSq_pos.2 hz0)
  rw [← isUnit_iff_isUnit_det]
  refine mulVec_injective_iff_isUnit.1 fun v w hvw => ?_
  have h0 : (A - z⁻¹ • (B * Bᴴ)) *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
  set x := v - w
  have hq := schur_quad_im hA B z x
  rw [h0, dotProduct_zero, Complex.zero_im] at hq
  have hB0 : vecNormSq (Bᴴ *ᵥ x) = 0 := by
    have := vecNormSq_nonneg (Bᴴ *ᵥ x)
    nlinarith
  have hBx : Bᴴ *ᵥ x = 0 := vecNormSq_eq_zero hB0
  have hYx : (A - (((z⁻¹).re : ℝ) : ℂ) • (B * Bᴴ)) *ᵥ x = 0 := by
    have e1 : (A - z⁻¹ • (B * Bᴴ)) *ᵥ x = A *ᵥ x := by
      rw [sub_mulVec, smul_mulVec, ← mulVec_mulVec, hBx, mulVec_zero, smul_zero, sub_zero]
    rw [sub_mulVec, smul_mulVec, ← mulVec_mulVec, hBx, mulVec_zero, smul_zero, sub_zero,
      ← e1, h0]
  have hinj := mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 hY)
  have : x = 0 := hinj (by rw [hYx, mulVec_zero])
  exact sub_eq_zero.1 this

end BlockBand.Endpoints
