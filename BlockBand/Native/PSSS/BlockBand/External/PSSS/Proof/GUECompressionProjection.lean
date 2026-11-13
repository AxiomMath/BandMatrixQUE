module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEWeightedCompressionTail
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.PublicGUE

/-!
# Orthogonal-compression weights in canonical GUE coordinates

The projection away from the first coordinate deletes the first row and column, so weights of the
projected compression of a canonical GUE matrix depend measurably on the compression coordinates
only.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The orthogonal projection `1 - φφ*` onto `φ⊥`, as a matrix. -/
noncomputable def orthProj {N : ℕ} (φ : EuclideanSpace ℂ (Fin N)) :
    Matrix (Fin N) (Fin N) ℂ :=
  1 - Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))

/-- The canonical coordinate vector, bundled in Euclidean space. -/
noncomputable def canonicalFirstEuclidean {N : ℕ} (hN : 0 < N) :
    EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (phaseFixedCoordinateVector ⟨0, hN⟩)

/-- Projecting a matrix away from the zeroth coordinate simply deletes its
zeroth row and column. -/
theorem orthProj_canonicalFirst_apply {N : ℕ} (hN : 0 < N)
    (H : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (orthProj (canonicalFirstEuclidean hN) * H *
      orthProj (canonicalFirstEuclidean hN)) i j =
      if i = ⟨0, hN⟩ ∨ j = ⟨0, hN⟩ then 0 else H i j := by
  classical
  let e : Fin N := ⟨0, hN⟩
  have hP : orthProj (canonicalFirstEuclidean hN) =
      Matrix.diagonal fun i : Fin N => if i = e then 0 else 1 := by
    ext a b
    by_cases ha : a = e
    · subst a
      simp [orthProj, canonicalFirstEuclidean, phaseFixedCoordinateVector,
        Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.diagonal_apply,
        Pi.single_apply, e, eq_comm]
    · by_cases hb : b = e
      · subst b
        simp [orthProj, canonicalFirstEuclidean, phaseFixedCoordinateVector,
          Matrix.vecMulVec_apply, e, ha]
      · by_cases hab : a = b
        · subst b
          simp [orthProj, canonicalFirstEuclidean, phaseFixedCoordinateVector,
            Matrix.vecMulVec_apply, e, ha]
        · simp [orthProj, canonicalFirstEuclidean, phaseFixedCoordinateVector,
            Matrix.vecMulVec_apply, e, ha, hb, hab]
  rw [hP]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i = e
  · simp [hi, e]
  · by_cases hj : j = e
    · simp [hj, e]
    · simp [hi, hj, e]

/-- Removing the zeroth row and column discards the first-row
coordinate block, so the projected full reconstruction depends only on the
compression coordinates. -/
theorem orthProj_hermitianGUEBlock_eq_projectedCompression {N : ℕ}
    (hN : 0 < N) (x : HermitianCoordinateSpace N) :
    orthProj (canonicalFirstEuclidean hN) * (hermitianGUEBlock N x).1 *
        orthProj (canonicalFirstEuclidean hN) =
      orthProj (canonicalFirstEuclidean hN) *
        (compressionGUEHermitian N (compressionGUECoordinates N x)).1 *
        orthProj (canonicalFirstEuclidean hN) := by
  classical
  let P := orthProj (canonicalFirstEuclidean hN)
  let R := (firstRowGUEHermitian N (firstRowGUECoordinates N x)).1
  let C := (compressionGUEHermitian N (compressionGUECoordinates N x)).1
  have hR : P * R * P = 0 := by
    ext i j
    rw [orthProj_canonicalFirst_apply hN]
    by_cases hi : i = ⟨0, hN⟩
    · simp [hi]
    · by_cases hj : j = ⟨0, hN⟩
      · simp [hj]
      · simp only [hi, hj, or_self, ↓reduceIte, Matrix.zero_apply]
        have hi0 : (i : ℕ) ≠ 0 := by
          intro h
          apply hi
          exact Fin.ext h
        have hj0 : (j : ℕ) ≠ 0 := by
          intro h
          apply hj
          exact Fin.ext h
        simp [R, firstRowGUEHermitian, hermitianGUEBlock,
          hermitianOfFinCoordinates, hermitianOfCoordinates,
          hermitianMatrixOfCoordinates, hermitianUpperEntry,
          extendFirstRowGUECoordinates, IsFirstRowGUECoordinate,
          Equiv.symm_apply_apply, hi0, hj0]
  have hsum : R + C = (hermitianGUEBlock N x).1 :=
    firstRowGUEHermitian_add_compressionGUEHermitian N x
  change P * (hermitianGUEBlock N x).1 * P = P * C * P
  rw [← hsum]
  rw [Matrix.mul_add, Matrix.add_mul, hR, zero_add]

/-- In particular, weights of the projected compression are measurable in the
compression coordinate. -/
theorem measurable_projectedCompressionWeight {N : ℕ} (hN : 0 < N)
    (F : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞) (hF : Measurable F) :
    Measurable fun u : CompressionGUECoordinate N → ℝ =>
      F (orthProj (canonicalFirstEuclidean hN) *
        (compressionGUEHermitian N u).1 *
        orthProj (canonicalFirstEuclidean hN)) := by
  have hC : Measurable fun u : CompressionGUECoordinate N → ℝ =>
      (compressionGUEHermitian N u).1 :=
    continuous_subtype_val.measurable.comp (measurable_compressionGUEHermitian N)
  apply hF.comp
  rw [Matrix.measurable_iff]
  intro i j
  simp only [Matrix.mul_apply]
  fun_prop

end PSSSNative.BlockBand.PSSS
