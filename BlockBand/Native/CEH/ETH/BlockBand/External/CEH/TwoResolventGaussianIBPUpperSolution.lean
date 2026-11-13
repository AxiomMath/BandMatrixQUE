module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPIntegrability
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEExistence
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEMatrixAdapter

/-!
# Upper-MDE specialization of the CEH Gaussian loop

This module specializes the exact integrated centered-error equation to the
unconditional upper-half-plane scalar Dyson solutions.  All solution,
positivity, inverse-pencil, and stability-nonvanishing premises are discharged
from the existing finite-dimensional MDE theory.  The two remaining random
terms are displayed and are not assumed small.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal
open PencilAdapter

/-- The four deterministic/random inverse equations specialized to the two
unconditional upper-half-plane scalar MDE solutions. -/
theorem upperSolution_actualInverseEquations
    {N : ℕ} (hN : 0 < N) (f : Spectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (z₁ z₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (y : HermitianCoordinateSpace N) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let m₁ := CEHNative.BlockBand.CEH.upperSolution
      hN f hs z₁ hz₁
    let m₂ := CEHNative.BlockBand.CEH.upperSolution
      hN f hs z₂ hz₂
    mdeMatrix f lambda z₁ m₁ * mdePencil f lambda z₁ m₁ = 1 ∧
      mdeMatrix f lambda z₂ m₂ * mdePencil f lambda z₂ m₂ = 1 ∧
      resolventPencil f lambda (hermitianGUEBlock N y).1 z₁ *
          resolvent f lambda (hermitianGUEBlock N y).1 z₁ = 1 ∧
        resolventPencil f lambda (hermitianGUEBlock N y).1 z₂ *
          resolvent f lambda (hermitianGUEBlock N y).1 z₂ = 1 := by
  dsimp only
  let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  let m₁ := CEHNative.BlockBand.CEH.upperSolution
    hN f hs z₁ hz₁
  let m₂ := CEHNative.BlockBand.CEH.upperSolution
    hN f hs z₂ hz₂
  have hm₁ : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₁ m₁ :=
    CEHNative.BlockBand.CEH.upperSolution_isSolution
      hN f hs z₁ hz₁
  have hm₂ : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₂ m₂ :=
    CEHNative.BlockBand.CEH.upperSolution_isSolution
      hN f hs z₂ hz₂
  exact pencilAdapter_actualInverseEquations
    f lambda hlambda.le z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂ y

/-- The ordinary (`++`) CEH stability denominator for the two unconditional
upper solutions is nonzero. -/
theorem upperSolution_plain_stability_ne_zero
    {N : ℕ} (hN : 0 < N) (f : Spectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (z₁ z₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let m₁ := CEHNative.BlockBand.CEH.upperSolution
      hN f hs z₁ hz₁
    let m₂ := CEHNative.BlockBand.CEH.upperSolution
      hN f hs z₂ hz₂
    stabilityDenominator (lambda : ℂ)
      (NTrace (mdeMatrix f lambda z₁ m₁ *
        mdeMatrix f lambda z₂ m₂)) ≠ 0 := by
  dsimp only
  let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  let m₁ := CEHNative.BlockBand.CEH.upperSolution
    hN f hs z₁ hz₁
  let m₂ := CEHNative.BlockBand.CEH.upperSolution
    hN f hs z₂ hz₂
  have hm₁ : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₁ m₁ :=
    CEHNative.BlockBand.CEH.upperSolution_isSolution
      hN f hs z₁ hz₁
  have hm₂ : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₂ m₂ :=
    CEHNative.BlockBand.CEH.upperSolution_isSolution
      hN f hs z₂ hz₂
  simpa using constellation_stability_ne_zero hN f lambda hlambda.le
    z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂
    AdjointChoice.plain AdjointChoice.plain

/-- **Paper-facing upper-solution two-resolvent expectation identity.**
The deterministic comparison is the CEH `twoResolventApprox` built
from the two unconditional scalar MDE solutions.  The right side isolates
exactly (i) the one-resolvent deviation from the second MDE matrix and (ii) the
centered trace remainder. -/
theorem upperSolution_centeredError_expectation
    {N : ℕ} (hN : 0 < N) (f : Spectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (A : Matrix (Fin N) (Fin N) ℂ)
    (z₁ z₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (p q : Fin N) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let m₁ := CEHNative.BlockBand.CEH.upperSolution
      hN f hs z₁ hz₁
    let m₂ := CEHNative.BlockBand.CEH.upperSolution
      hN f hs z₂ hz₂
    let M₁ := mdeMatrix f lambda z₁ m₁
    let M₂ := mdeMatrix f lambda z₂ m₂
    let Mhat := twoResolventApprox (lambda : ℂ) M₁ A M₂
    let t := NTrace Mhat
    (∫ y : HermitianCoordinateSpace N,
      (resolvent f lambda (hermitianGUEBlock N y).1 z₁ * A *
        resolvent f lambda (hermitianGUEBlock N y).1 z₂ - Mhat) p q
      ∂normalizedGUEMeasure N) =
    ∫ y : HermitianCoordinateSpace N,
      (M₁ * (A + (((lambda : ℂ) ^ 2 * t) •
          (1 : Matrix (Fin N) (Fin N) ℂ))) *
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂ - M₂) +
        M₁ * centeredTraceRemainder (lambda : ℂ) m₁ t
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂)) p q
      ∂normalizedGUEMeasure N := by
  dsimp only
  let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  let m₁ := CEHNative.BlockBand.CEH.upperSolution
    hN f hs z₁ hz₁
  let m₂ := CEHNative.BlockBand.CEH.upperSolution
    hN f hs z₂ hz₂
  let M₁ := mdeMatrix f lambda z₁ m₁
  let M₂ := mdeMatrix f lambda z₂ m₂
  have hm₁ : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₁ m₁ :=
    CEHNative.BlockBand.CEH.upperSolution_isSolution
      hN f hs z₁ hz₁
  have hm₂ : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₂ m₂ :=
    CEHNative.BlockBand.CEH.upperSolution_isSolution
      hN f hs z₂ hz₂
  have hstable : stabilityDenominator (lambda : ℂ)
      (NTrace (M₁ * M₂)) ≠ 0 := by
    simpa [M₁, M₂] using constellation_stability_ne_zero
      hN f lambda hlambda.le z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂
      AdjointChoice.plain AdjointChoice.plain
  exact pencilAdapter_centeredError_expectation
    hN f lambda hlambda.le m₁ A M₂ hz₁ (ne_of_gt hz₂) hm₁ hstable p q

end CEHNative.BlockBand.External.CEH
