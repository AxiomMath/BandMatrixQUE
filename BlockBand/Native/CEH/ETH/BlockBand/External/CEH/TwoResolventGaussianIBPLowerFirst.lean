module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPAdjoint

/-!
# Lower-first and order-reversal adapters for CEH Gaussian loops

Complex conjugation and conjugate transpose commute with the normalized GUE expectation, and the
adjointed upper MDE solution satisfies the lower-first inverse identity, which gives the
lower-first centered MDE source for the Gaussian loop.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal
open PencilAdapter

/-- Complex conjugation commutes with the normalized GUE expectation without
any extra law or integrability hypothesis. -/
theorem normalizedGUE_integral_star
    {N : ℕ} (F : HermitianCoordinateSpace N → ℂ) :
    (∫ y, star (F y) ∂normalizedGUEMeasure N) =
      star (∫ y, F y ∂normalizedGUEMeasure N) := by
  exact integral_conj

/-- Entrywise form of order reversal under conjugate transpose and normalized
GUE expectation. -/
theorem normalizedGUE_integral_conjTranspose_entry
    {N : ℕ} (F : HermitianCoordinateSpace N → Matrix (Fin N) (Fin N) ℂ)
    (p q : Fin N) :
    (∫ y, (F y)ᴴ p q ∂normalizedGUEMeasure N) =
      star (∫ y, F y q p ∂normalizedGUEMeasure N) := by
  simp only [Matrix.conjTranspose_apply]
  exact normalizedGUE_integral_star (fun y => F y q p)

/-- Lower-first centered MDE source after left multiplication, assuming only the algebraic
lower inverse equation. In particular no `IsSolution` is demanded of lower-half-plane data. -/
theorem pencilAdapter_lowerFirst_centeredSource_of_inverse
    {N : ℕ} (f : Spectrum N) (lambda : ℝ) (m t : ℂ)
    (A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (hz₁ : z₁.im ≠ 0)
    (hMQ : mdeMatrix f lambda z₁ m * mdePencil f lambda z₁ m = 1)
    (y : HermitianCoordinateSpace N) :
    mdeMatrix f lambda z₁ m *
        underlinedTwoResolventWord (lambda : ℂ)
          (hermitianGUEBlock N y).1
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂) =
      -(resolvent f lambda (hermitianGUEBlock N y).1 z₁ * A *
          resolvent f lambda (hermitianGUEBlock N y).1 z₂) +
        mdeMatrix f lambda z₁ m *
          (A + (((lambda : ℂ) ^ 2 * t) •
            (1 : Matrix (Fin N) (Fin N) ℂ))) *
          resolvent f lambda (hermitianGUEBlock N y).1 z₂ +
        mdeMatrix f lambda z₁ m *
          centeredTraceRemainder (lambda : ℂ) m t
            (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
            (resolvent f lambda (hermitianGUEBlock N y).1 z₂) := by
  rw [pencilAdapter_underlined_mdeSource f lambda m t A z₁ z₂ hz₁ y]
  rw [Matrix.mul_add, Matrix.mul_add]
  rw [show mdeMatrix f lambda z₁ m *
      (-(mdePencil f lambda z₁ m *
        resolvent f lambda (hermitianGUEBlock N y).1 z₁ * A *
        resolvent f lambda (hermitianGUEBlock N y).1 z₂)) =
      -(resolvent f lambda (hermitianGUEBlock N y).1 z₁ * A *
        resolvent f lambda (hermitianGUEBlock N y).1 z₂) by
    rw [Matrix.mul_neg]
    simp only [← Matrix.mul_assoc, hMQ, Matrix.one_mul]]
  simp only [Matrix.mul_assoc]

/-- The adjointed upper MDE objects satisfy the lower-first inverse identity at the conjugate
spectral parameter. -/
theorem upperSolution_adjoint_mdeInverse
    {N : ℕ} (hN : 0 < N) (f : Spectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (z : ℂ) (hz : 0 < z.im) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let m := CEHNative.BlockBand.CEH.upperSolution hN f hs z hz
    mdeMatrix f lambda (star z) (star m) *
      mdePencil f lambda (star z) (star m) = 1 := by
  dsimp only
  let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  let m := CEHNative.BlockBand.CEH.upperSolution hN f hs z hz
  have hm := CEHNative.BlockBand.CEH.upperSolution_isSolution
    hN f hs z hz
  have hu := mdeMatrix_mul_mdePencil f lambda hlambda.le z m hz hm.2
  have huc := congrArg Matrix.conjTranspose hu
  have hcomm := mul_eq_one_comm.mp (by
    simpa [Matrix.conjTranspose_mul] using huc)
  simpa [mdeMatrix_conjTranspose, mdePencil_conjTranspose] using hcomm

/-- The lower-first centered source for the adjointed upper solution; all inverse and
half-plane premises are discharged. -/
theorem upperSolution_adjoint_centeredSource
    {N : ℕ} (hN : 0 < N) (f : Spectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda) (z₁ z₂ : ℂ)
    (hz₁ : 0 < z₁.im) (t : ℂ)
    (A : Matrix (Fin N) (Fin N) ℂ) (y : HermitianCoordinateSpace N) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let m₁ := CEHNative.BlockBand.CEH.upperSolution hN f hs z₁ hz₁
    mdeMatrix f lambda (star z₁) (star m₁) *
      underlinedTwoResolventWord (lambda : ℂ) (hermitianGUEBlock N y).1
        (resolvent f lambda (hermitianGUEBlock N y).1 (star z₁)) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂) =
      -(resolvent f lambda (hermitianGUEBlock N y).1 (star z₁) * A *
          resolvent f lambda (hermitianGUEBlock N y).1 z₂) +
        mdeMatrix f lambda (star z₁) (star m₁) *
          (A + (((lambda : ℂ) ^ 2 * t) •
            (1 : Matrix (Fin N) (Fin N) ℂ))) *
          resolvent f lambda (hermitianGUEBlock N y).1 z₂ +
        mdeMatrix f lambda (star z₁) (star m₁) *
          centeredTraceRemainder (lambda : ℂ) (star m₁) t
            (resolvent f lambda (hermitianGUEBlock N y).1 (star z₁)) A
            (resolvent f lambda (hermitianGUEBlock N y).1 z₂) := by
  dsimp only
  let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  let m₁ := CEHNative.BlockBand.CEH.upperSolution hN f hs z₁ hz₁
  apply pencilAdapter_lowerFirst_centeredSource_of_inverse
  · simp [ne_of_gt hz₁]
  · exact upperSolution_adjoint_mdeInverse hN f lambda hlambda z₁ hz₁

end CEHNative.BlockBand.External.CEH
