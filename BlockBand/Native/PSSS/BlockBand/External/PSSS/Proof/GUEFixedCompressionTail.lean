module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEFirstRowMarginal

/-!
# Fixed-compression conditional branch bound

This module realifies a deterministic complex Hermitian compression and applies
the APSSS `quadraticRatio_tail` theorem to its row-quadratic branch.
The scalar/row normalization is the one supplied by `GUEFirstRowMarginal`:
the row real and imaginary coordinates have been multiplied by `√(2N)`.
No random-compression integration is used here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- Real block representation of a complex matrix, indexed by coordinate and
real/imaginary selector. -/
def complexMatrixRealification {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ := fun p q =>
  if p.2 = 0 then
    if q.2 = 0 then (A p.1 q.1).re else -(A p.1 q.1).im
  else
    if q.2 = 0 then (A p.1 q.1).im else (A p.1 q.1).re

/-- Real and imaginary coordinates of a complex vector. -/
def complexVectorRealification {n : ℕ} (z : Fin n → ℂ) :
    Fin n × Fin 2 → ℝ := fun p => if p.2 = 0 then (z p.1).re else (z p.1).im

/-- Realification intertwines complex matrix-vector multiplication. -/
theorem complexMatrixRealification_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    complexMatrixRealification A *ᵥ complexVectorRealification z =
      complexVectorRealification (A *ᵥ z) := by
  funext p
  rcases p with ⟨i, r⟩
  fin_cases r <;>
    simp [complexMatrixRealification, complexVectorRealification,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Complex.mul_re,
      Complex.mul_im, Finset.sum_add_distrib] <;> ring

/-- Hermitian complex matrices realify to symmetric real matrices. -/
theorem complexMatrixRealification_isSymm {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (complexMatrixRealification A).IsSymm := by
  change (complexMatrixRealification A)ᵀ = complexMatrixRealification A
  ext p q
  rcases p with ⟨i, r⟩
  rcases q with ⟨j, s⟩
  have h := congrFun₂ hA.eq j i
  simp only [conjTranspose_apply] at h
  fin_cases r <;> fin_cases s <;>
    simp [complexMatrixRealification, ← h]

/-- A nonzero complex matrix has nonzero realification. -/
theorem complexMatrixRealification_ne_zero {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ≠ 0) :
    complexMatrixRealification A ≠ 0 := by
  intro h
  apply hA
  ext i j
  have hre := congrFun₂ h (i, 0) (j, 0)
  have him := congrFun₂ h (i, 1) (j, 0)
  simp [complexMatrixRealification] at hre him
  apply Complex.ext
  · simpa using hre
  · simpa using him

/-- Canonical finite ordinal indexing of real and imaginary row coordinates. -/
noncomputable def complexRealCoordinateEquivFin (n : ℕ) :
    (Fin n × Fin 2) ≃ Fin (2 * n) := by
  simpa [Fintype.card_prod, Nat.mul_comm] using
    (Fintype.equivFin (Fin n × Fin 2))

/-- Realification reindexed in the exact `Fin m` form consumed by
`quadraticRatio_tail`. -/
def fixedCompressionRealMatrix {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  Matrix.reindex (complexRealCoordinateEquivFin n)
    (complexRealCoordinateEquivFin n) (complexMatrixRealification D⁻¹)

/-- The real fixed-compression matrix is symmetric. -/
theorem fixedCompressionRealMatrix_isSymm {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    (fixedCompressionRealMatrix D).IsSymm := by
  apply Matrix.IsSymm.reindex
  exact complexMatrixRealification_isSymm hD.inv

/-- Invertibility makes the real fixed-compression matrix nonzero in every
positive dimension. -/
theorem fixedCompressionRealMatrix_ne_zero {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (hD : D.det ≠ 0) :
    fixedCompressionRealMatrix D ≠ 0 := by
  have hreal : complexMatrixRealification D⁻¹ ≠ 0 := by
    apply complexMatrixRealification_ne_zero
    intro hinv
    have hone : D * D⁻¹ = 1 :=
      Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.mpr hD)
    rw [hinv, mul_zero] at hone
    have hdiag := congrFun₂ hone ⟨0, hn⟩ ⟨0, hn⟩
    simp at hdiag
  unfold fixedCompressionRealMatrix
  intro hz
  apply hreal
  apply (Matrix.reindex (complexRealCoordinateEquivFin n)
    (complexRealCoordinateEquivFin n)).injective
  simpa using hz

end PSSSNative.BlockBand.PSSS
