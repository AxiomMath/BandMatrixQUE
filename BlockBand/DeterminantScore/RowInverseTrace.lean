module

public import BlockBand.DeterminantScore.RowBlockAlgebra

/-!
# The inverse trace of a bordered matrix as a polynomial

For an invertible Hermitian minor `B` and a nonzero Schur scalar `a`, the block inverse of
`rowMatrix B u y` is a rank-one update of the minor inverse embedded by zero, and
`a² Tr(M⁻²)` is an explicit polynomial in `a` and the quadratic forms `y* C^j y` of `C = B⁻¹`
(`rowMatrix_inverse_square_polynomial`). All traces are unnormalized; no measure is involved.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.Row
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Minor inverse embedded by zero on the restored scalar row. -/
def embeddedMinor (C : Matrix ι ι ℂ) : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  fromBlocks 0 0 0 C

/-- Rank-one Schur graph on the restored scalar row. -/
def inverseGraph (w : ι → ℂ) : Unit ⊕ ι → ℂ :=
  Sum.elim (fun _ => 1) (fun i => -w i)

omit [DecidableEq ι] in
/-- The block inverse is a rank-one update of the embedded minor inverse. -/
theorem inverseCandidate_eq_rankOne_update (C : Matrix ι ι ℂ) (a : ℂ) (y : ι → ℂ) :
    inverseCandidate C a y = embeddedMinor C +
      a⁻¹ • rankOne (inverseGraph (C *ᵥ y)) (inverseGraph (C *ᵥ y)) := by
  ext (i | i) (j | j)
  · change a⁻¹ = 0 + a⁻¹ * ((1 : ℂ) * star 1)
    simp
  · change -(a⁻¹ * star ((C *ᵥ y) j)) = 0 +
      a⁻¹ * ((1 : ℂ) * star (-(C *ᵥ y) j))
    simp
  · change -(a⁻¹ * (C *ᵥ y) i) = 0 +
      a⁻¹ * ((-(C *ᵥ y) i) * star (1 : ℂ))
    simp
  · change C i j + a⁻¹ * ((C *ᵥ y) i * star ((C *ᵥ y) j)) =
      C i j + a⁻¹ * ((-(C *ᵥ y) i) * star (-(C *ᵥ y) j))
    simp

/-- The square of the embedded minor inverse has the trace of the minor inverse square. -/
theorem trace_embeddedMinor_sq (C : Matrix ι ι ℂ) :
    ((embeddedMinor C) ^ 2).trace = (C ^ 2).trace := by
  simp [pow_two, embeddedMinor, Matrix.fromBlocks_multiply,
    Matrix.trace, Fintype.sum_sum_type]

omit [DecidableEq ι] in
/-- Squared length of the Schur graph vector. -/
theorem dotProduct_inverseGraph (w : ι → ℂ) :
    dotProduct (star (inverseGraph w)) (inverseGraph w) =
      1 + dotProduct (star w) w := by
  simp [inverseGraph, dotProduct, Fintype.sum_sum_type]

omit [DecidableEq ι] in
/-- Quadratic form of the embedded minor inverse on the graph vector. -/
theorem quadratic_inverseGraph (C : Matrix ι ι ℂ) (w : ι → ℂ) :
    dotProduct (star (inverseGraph w)) (embeddedMinor C *ᵥ inverseGraph w) =
      dotProduct (star w) (C *ᵥ w) := by
  simp [inverseGraph, embeddedMinor, dotProduct, Matrix.mulVec,
    Fintype.sum_sum_type, Finset.mul_sum]

/-- Square trace of the block inverse, before cancelling the Schur pole. -/
theorem trace_inverseCandidate_sq (C : Matrix ι ι ℂ) (a : ℂ) (y : ι → ℂ) :
    ((inverseCandidate C a y) ^ 2).trace =
      (C ^ 2).trace + 2 * a⁻¹ * dotProduct (star (C *ᵥ y)) (C *ᵥ (C *ᵥ y)) +
      (a⁻¹) ^ 2 * (1 + dotProduct (star (C *ᵥ y)) (C *ᵥ y)) ^ 2 := by
  rw [inverseCandidate_eq_rankOne_update, trace_square_rankOne_update,
    trace_embeddedMinor_sq, quadratic_inverseGraph, dotProduct_inverseGraph]

/-- Hermitian minor inversion changes the graph norm into the C² quadratic form. -/
theorem quadratic_inverse_graph_sq (C : Matrix ι ι ℂ) (hC : C.IsHermitian) (y : ι → ℂ) :
    dotProduct (star (C *ᵥ y)) (C *ᵥ y) =
      dotProduct (star y) ((C ^ 2) *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hC.eq,
    Matrix.mulVec_mulVec, ← pow_two]

/-- Hermitian minor inversion changes the graph C form into the C³ quadratic form. -/
theorem quadratic_inverse_graph_cube (C : Matrix ι ι ℂ) (hC : C.IsHermitian) (y : ι → ℂ) :
    dotProduct (star (C *ᵥ y)) (C *ᵥ (C *ᵥ y)) =
      dotProduct (star y) ((C ^ 3) *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hC.eq,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp [pow_succ, Matrix.mul_assoc]

/-- At a nonzero Schur scalar, `a² Tr(M⁻²)` as a polynomial, with the cubic and quartic terms kept
in their signed grouping. The inverse is built from `B` and its Schur scalar. -/
theorem rowMatrix_inverse_square_polynomial (B : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (hunit : IsUnit B.det) (u : ℂ) (y : ι → ℂ)
    (ha : schurScalar B⁻¹ u y ≠ 0) :
    (schurScalar B⁻¹ u y) ^ 2 * (((rowMatrix B u y)⁻¹) ^ 2).trace =
      (schurScalar B⁻¹ u y) ^ 2 * (B⁻¹ ^ 2).trace +
      2 * schurScalar B⁻¹ u y * dotProduct (star y) ((B⁻¹ ^ 3) *ᵥ y) +
      (1 + dotProduct (star y) ((B⁻¹ ^ 2) *ᵥ y)) ^ 2 := by
  rw [rowMatrix_inverse B hB hunit u y ha, trace_inverseCandidate_sq,
    quadratic_inverse_graph_sq B⁻¹ hB.inv y,
    quadratic_inverse_graph_cube B⁻¹ hB.inv y]
  field_simp [ha]

end BlockBand.DeterminantScore.Row
