module

public import BlockBand.DeterminantScore.HorizontalVariation

/-!
# Row Schur inverse of a bordered matrix

For a scalar `u`, a vector `y` and a minor `B` with inverse `C`, the bordered matrix
`rowMatrix B u y = [[u, y*], [y, B]]` has the block inverse `inverseCandidate C a y` with Schur
scalar `a = u - y* C y` (`rowMatrix_inverse`), together with rank-one product and trace identities
used to write the inverse trace as a polynomial. The inverse identities require a nonzero Schur
scalar and an invertible minor. No measure is involved.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Row
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Product of two outer products. -/
theorem rankOne_mul (u v w z : ι → ℂ) :
    rankOne u v * rankOne w z =
      (dotProduct (star v) w) • rankOne u z := by
  ext i j
  change (∑ k, (u i * star (v k)) * (w k * star (z j))) =
    (∑ k, star (v k) * w k) * (u i * star (z j))
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

omit [DecidableEq ι] in
/-- Trace of an outer product. -/
theorem trace_rankOne (u v : ι → ℂ) :
    (rankOne u v).trace = dotProduct (star v) u := by
  change (∑ i, u i * star (v i)) = ∑ i, star (v i) * u i
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Square trace of a rank-one update (no Hermitian hypothesis). -/
theorem trace_square_rankOne_update (D : Matrix ι ι ℂ) (u : ι → ℂ) (r : ℂ) :
    ((D + r • rankOne u u) ^ 2).trace =
      (D ^ 2).trace + 2 * r * dotProduct (star u) (D *ᵥ u) +
      r ^ 2 * (dotProduct (star u) u) ^ 2 := by
  have hcross : (rankOne u u * D).trace = dotProduct (star u) (D *ᵥ u) := by
    rw [Matrix.trace_mul_comm, trace_mul_rankOne]
  simp only [pow_two, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    trace_mul_rankOne, hcross, rankOne_mul, trace_rankOne]
  ring

/-- The bordered matrix with one scalar coordinate `u`, row `y` and minor `B`. -/
def rowMatrix (B : Matrix ι ι ℂ) (u : ℂ) (y : ι → ℂ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  fromBlocks (fun _ _ => u) (fun _ j => star (y j)) (fun i _ => y i) B

/-- The real-row Schur scalar, as a complex scalar before Hermitian simplification. -/
def schurScalar (C : Matrix ι ι ℂ) (u : ℂ) (y : ι → ℂ) : ℂ :=
  u - dotProduct (star y) (C *ᵥ y)

/-- The block inverse formula, built from the inverse `C` of the minor and the Schur scalar. -/
def inverseCandidate (C : Matrix ι ι ℂ) (a : ℂ) (y : ι → ℂ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  let w := C *ᵥ y
  fromBlocks (fun _ _ => a⁻¹) (fun _ j => -(a⁻¹ * star (w j)))
    (fun i _ => -(a⁻¹ * w i)) (C + a⁻¹ • rankOne w w)

/-- Right multiplication by the block inverse formula is the identity. -/
theorem rowMatrix_mul_inverseCandidate (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (hunit : IsUnit B.det) (u : ℂ) (y : ι → ℂ)
    (ha : schurScalar B⁻¹ u y ≠ 0) :
    rowMatrix B u y * inverseCandidate B⁻¹ (schurScalar B⁻¹ u y) y = 1 := by
  let C := B⁻¹
  let w := C *ᵥ y
  let a := schurScalar C u y
  let q := dotProduct (star y) w
  have hBC : B * C = 1 := B.mul_nonsing_inv hunit
  have hC : C.IsHermitian := hB.inv
  have hw : B *ᵥ w = y := by
    change B *ᵥ (C *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec]
  have hstar (j : ι) : (∑ k, star (y k) * C k j) = star (w j) := by
    change _ = star (∑ k, C j k * y k)
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have he : star (C j k) = C k j := congrFun (congrFun hC k) j
    rw [star_mul, he]
  have haq : a = u - q := rfl
  have hane : a ≠ 0 := ha
  have hq : (∑ k, star (y k) * w k) = q := rfl
  change rowMatrix B u y * inverseCandidate C a y = 1
  ext (i | i) (j | j)
  · cases i; cases j
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_unique]
    change u * a⁻¹ + (∑ k, star (y k) * (-(a⁻¹ * w k))) = 1
    have hs : (∑ k, star (y k) * (-(a⁻¹ * w k))) = -(a⁻¹ * q) := by
      rw [← hq, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hs]
    calc
      u * a⁻¹ - a⁻¹ * q = a * a⁻¹ := by rw [haq]; ring
      _ = 1 := mul_inv_cancel₀ hane
  · cases i
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_unique]
    change u * (-(a⁻¹ * star (w j))) +
      (∑ k, star (y k) * (C k j + a⁻¹ * (w k * star (w j)))) = 0
    have hs : (∑ k, star (y k) * (C k j + a⁻¹ * (w k * star (w j)))) =
        star (w j) + a⁻¹ * q * star (w j) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, hstar]
      congr 1
      rw [← hq, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hs]
    calc
      u * (-(a⁻¹ * star (w j))) + (star (w j) + a⁻¹ * q * star (w j)) =
          star (w j) - (a * a⁻¹) * star (w j) := by rw [haq]; ring
      _ = 0 := by rw [mul_inv_cancel₀ hane]; ring
  · cases j
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_unique]
    change y i * a⁻¹ + (∑ k, B i k * (-(a⁻¹ * w k))) = 0
    have hs : (∑ k, B i k * (-(a⁻¹ * w k))) = -(a⁻¹ * (B *ᵥ w) i) := by
      change _ = -(a⁻¹ * ∑ k, B i k * w k)
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hs, hw]
    ring
  · simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_unique]
    change y i * (-(a⁻¹ * star (w j))) +
      (∑ k, B i k * (C k j + a⁻¹ * (w k * star (w j)))) =
      (1 : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) (Sum.inr i) (Sum.inr j)
    simp only [Matrix.one_apply, Sum.inr.injEq]
    have hs : (∑ k, B i k * (C k j + a⁻¹ * (w k * star (w j)))) =
        (B * C) i j + a⁻¹ * (B *ᵥ w) i * star (w j) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      change (∑ k, B i k * (a⁻¹ * (w k * star (w j)))) =
        a⁻¹ * (∑ k, B i k * w k) * star (w j)
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hs, hBC, hw]
    simp only [Matrix.one_apply]
    ring

/-- For a nonsingular bordered matrix, the matrix inverse equals the block inverse formula. -/
theorem rowMatrix_inverse (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (hunit : IsUnit B.det) (u : ℂ) (y : ι → ℂ)
    (ha : schurScalar B⁻¹ u y ≠ 0) :
    (rowMatrix B u y)⁻¹ = inverseCandidate B⁻¹ (schurScalar B⁻¹ u y) y :=
  Matrix.inv_eq_right_inv (rowMatrix_mul_inverseCandidate B hB hunit u y ha)

end BlockBand.DeterminantScore.Row
