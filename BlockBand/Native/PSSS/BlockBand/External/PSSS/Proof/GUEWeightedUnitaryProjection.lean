module
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECanonicalWeightedAllDimensions
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEArbitraryFixedVectorTail
/-!
# Unitary transport of orthogonal-compression weights

Orthogonal projections and compressions transform covariantly under unitary conjugation, and
conjugation preserves the measurability of matrix weights.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace PSSSNative.BlockBand.PSSS
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Orthogonal projection transforms covariantly under a unitary matrix. -/
theorem orthProj_eq_unitary_mul_canonical_mul_conjTranspose {N : ℕ} (hN : 0 < N)
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (φ : EuclideanSpace ℂ (Fin N))
    (hUφ : U *ᵥ phaseFixedCoordinateVector ⟨0, hN⟩ = WithLp.ofLp φ) :
    orthProj φ = U * orthProj (canonicalFirstEuclidean hN) * Uᴴ := by
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  unfold orthProj canonicalFirstEuclidean
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_one, hUU]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  rw [hUφ]
  rw [← star_mulVec]
  rw [hUφ]

/-- Compression of a conjugated matrix at the canonical coordinate is the
unitary conjugate of compression at the transported vector. -/
theorem unitary_mul_canonicalCompression_mul_conjTranspose {N : ℕ} (hN : 0 < N)
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (φ : EuclideanSpace ℂ (Fin N))
    (hUφ : U *ᵥ phaseFixedCoordinateVector ⟨0, hN⟩ = WithLp.ofLp φ)
    (V : Matrix (Fin N) (Fin N) ℂ) :
    U * (orthProj (canonicalFirstEuclidean hN) * (Uᴴ * V * U) *
      orthProj (canonicalFirstEuclidean hN)) * Uᴴ =
      orthProj φ * V * orthProj φ := by
  rw [orthProj_eq_unitary_mul_canonical_mul_conjTranspose hN U hU φ hUφ]
  simp [Matrix.mul_assoc]

/-- Conjugating a matrix argument preserves measurability of an arbitrary
measurable matrix weight. -/
theorem measurable_unitaryConjugatedWeight {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ)
    (F : (Matrix (Fin N) (Fin N) ℂ) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun X : Matrix (Fin N) (Fin N) ℂ => F (U * X * Uᴴ)) := by
  apply hF.comp
  exact ((continuous_const.mul continuous_id).mul continuous_const).measurable

end PSSSNative.BlockBand.PSSS
