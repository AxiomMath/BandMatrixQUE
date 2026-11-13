module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPCentered

/-!
# GUE block adapter for the CEH Gaussian loop

The reconstructed Hermitian GUE block is the finite linear combination of its real-coordinate
directions, so the Gaussian integration-by-parts master cancellation for the two-resolvent word
holds with the GUE block in place of the coordinate-direction source.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal

/-- The reconstructed Hermitian GUE block is exactly the finite linear
combination of its canonical real-coordinate directions. -/
theorem hermitianGUEBlock_eq_sum_coordinateDirections
    (N : ℕ) (y : HermitianCoordinateSpace N) :
    (hermitianGUEBlock N y).1 =
      ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ((y k : ℝ) : ℂ) • gueCoordinateDirection N k := by
  have hy : y = ∑ k, (y k) • Pi.single k (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  have hcomp :
      y ∘ hermitianCoordinateEquivFin N =
        ∑ k, (y k) •
          (Pi.single k (1 : ℝ) ∘ hermitianCoordinateEquivFin N) := by
    funext c
    simpa using congrFun hy (hermitianCoordinateEquivFin N c)
  change hermitianCoordinatesLinearMap N
      (y ∘ hermitianCoordinateEquivFin N) = _
  rw [hcomp, map_sum]
  simp_rw [LinearMap.map_smul]
  rfl

/-- Left multiplication by the reconstructed GUE block agrees
entrywise with the coordinate-direction source used in the Gaussian IBP
master equation. -/
theorem hermitianGUEBlock_mul_twoResolvent_apply
    {N : ℕ} (y : HermitianCoordinateSpace N)
    (X : Matrix (Fin N) (Fin N) ℂ) (p q : Fin N) :
    ((hermitianGUEBlock N y).1 * X) p q =
      ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a * X a q := by
  rw [hermitianGUEBlock_eq_sum_coordinateDirections, Finset.sum_mul]
  simp_rw [Matrix.smul_mul]
  rw [sum_smul_mul_apply]

/-- Literal-block form of the normalized `lambda = 1` master cancellation. -/
theorem normalizedGUE_literalBlock_masterCancellation
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      ((hermitianGUEBlock N y).1 *
        (fullGUEResolvent H₁ z₁ y * A *
          fullGUEResolvent H₂ z₂ y)) p q
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) +
      (∫ y : HermitianCoordinateSpace N,
        ((N : ℂ)⁻¹ * (fullGUEResolvent H₁ z₁ y).trace) *
            (fullGUEResolvent H₁ z₁ y * A *
              fullGUEResolvent H₂ z₂ y) p q +
          ((N : ℂ)⁻¹ *
            (fullGUEResolvent H₁ z₁ y * A *
              fullGUEResolvent H₂ z₂ y).trace) *
            fullGUEResolvent H₂ z₂ y p q
        ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) = 0 := by
  rw [show (fun y : HermitianCoordinateSpace N =>
      ((hermitianGUEBlock N y).1 *
        (fullGUEResolvent H₁ z₁ y * A *
          fullGUEResolvent H₂ z₂ y)) p q) =
      (fun y => ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y) by
    funext y
    exact hermitianGUEBlock_mul_twoResolvent_apply y _ p q]
  exact normalizedGUE_masterCancellation
    hN H₁ H₂ A hH₁ hH₂ hz₁ hz₂ p q

end CEHNative.BlockBand.External.CEH
