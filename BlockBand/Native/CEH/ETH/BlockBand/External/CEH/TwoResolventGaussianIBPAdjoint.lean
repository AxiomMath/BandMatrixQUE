module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPUpperSolution

/-!
# Adjoint CEH Gaussian-loop adapter

The reconstructed GUE block is Hermitian pointwise.  Consequently taking an
adjoint of a random resolvent changes only the spectral parameter from `z` to
`star z`; no change of the normalized real-coordinate product measure is
needed.  This module uses that fact to derive the nontrivial `+-` expectation
identity from the integrated lower-half-plane adapter.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal
open PencilAdapter

/-- Conjugation acts trivially on the concrete reconstructed GUE block because
that block is Hermitian for every real coordinate configuration. -/
theorem hermitianGUEBlock_conjTranspose
    (N : ℕ) (y : HermitianCoordinateSpace N) :
    (hermitianGUEBlock N y).1ᴴ = (hermitianGUEBlock N y).1 :=
  (hermitianGUEBlock N y).2.eq

/-- The adjoint random resolvent is the same-coordinate lower-half-plane
resolvent.  Thus normalized GUE conjugation requires no pushforward law. -/
theorem chooseAdjoint_resolvent_eq_starParameter
    {N : ℕ} (f : Spectrum N) (lambda : ℝ)
    (z : ℂ) (y : HermitianCoordinateSpace N) :
    chooseAdjoint AdjointChoice.adjoint
        (resolvent f lambda (hermitianGUEBlock N y).1 z) =
      resolvent f lambda (hermitianGUEBlock N y).1 (star z) := by
  exact resolvent_conjTranspose f lambda (hermitianGUEBlock N y).1
    (hermitianGUEBlock N y).2 z

/-- Entrywise integrability of the adjoint resolvent, obtained by identifying
it with the lower-half-plane resolvent under the unchanged normalized GUE
coordinate measure. -/
theorem integrable_chooseAdjoint_resolvent_entry
    {N : ℕ} (f : Spectrum N) (lambda : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (i j : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      chooseAdjoint AdjointChoice.adjoint
        (resolvent f lambda (hermitianGUEBlock N y).1 z) i j)
      (normalizedGUEMeasure N) := by
  have hzstar : (star z).im ≠ 0 := by simp [hz]
  have h : Integrable (fun y : HermitianCoordinateSpace N =>
      resolvent f lambda (hermitianGUEBlock N y).1 (star z) i j)
      (normalizedGUEMeasure N) := by
    simpa only [← scaledFullGUEResolvent_deformationMatrix] using
      integrable_scaledFullGUEResolvent_entry
        (deformationMatrix f) (deformationMatrix_isHermitian f)
        lambda hzstar i j
  apply h.congr
  filter_upwards with y
  exact (congrFun (congrFun
    (chooseAdjoint_resolvent_eq_starParameter f lambda z y) i) j).symm

/-- Adjoint-resolvent integration is lower-half-plane integration
with the same normalized GUE measure. -/
theorem integral_chooseAdjoint_resolvent_eq_starParameter
    {N : ℕ} (f : Spectrum N) (lambda : ℝ) (z : ℂ) (i j : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      chooseAdjoint AdjointChoice.adjoint
        (resolvent f lambda (hermitianGUEBlock N y).1 z) i j
      ∂normalizedGUEMeasure N) =
    ∫ y : HermitianCoordinateSpace N,
      resolvent f lambda (hermitianGUEBlock N y).1 (star z) i j
      ∂normalizedGUEMeasure N := by
  apply integral_congr_ae
  filter_upwards with y
  exact congrFun (congrFun
    (chooseAdjoint_resolvent_eq_starParameter f lambda z y) i) j

/-- **The nontrivial `+-` upper-solution expectation identity.**  The second
random and deterministic resolvents are adjointed.  Pointwise Hermiticity of
the GUE block converts this to the lower spectral parameter `star z₂`, while
all stability, solution, inverse, measurability, and integrability premises are
discharged by existing APIs. -/
theorem upperSolution_plain_adjoint_centeredError_expectation
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
    let M₂ := chooseAdjoint AdjointChoice.adjoint
      (mdeMatrix f lambda z₂ m₂)
    let Mhat := twoResolventApprox (lambda : ℂ) M₁ A M₂
    let t := NTrace Mhat
    (∫ y : HermitianCoordinateSpace N,
      (resolvent f lambda (hermitianGUEBlock N y).1 z₁ * A *
        chooseAdjoint AdjointChoice.adjoint
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂) - Mhat) p q
      ∂normalizedGUEMeasure N) =
    ∫ y : HermitianCoordinateSpace N,
      (M₁ * (A + (((lambda : ℂ) ^ 2 * t) •
          (1 : Matrix (Fin N) (Fin N) ℂ))) *
          (chooseAdjoint AdjointChoice.adjoint
            (resolvent f lambda (hermitianGUEBlock N y).1 z₂) - M₂) +
        M₁ * centeredTraceRemainder (lambda : ℂ) m₁ t
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (chooseAdjoint AdjointChoice.adjoint
            (resolvent f lambda (hermitianGUEBlock N y).1 z₂))) p q
      ∂normalizedGUEMeasure N := by
  dsimp only
  let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  let m₁ := CEHNative.BlockBand.CEH.upperSolution
    hN f hs z₁ hz₁
  let m₂ := CEHNative.BlockBand.CEH.upperSolution
    hN f hs z₂ hz₂
  let M₁ := mdeMatrix f lambda z₁ m₁
  let M₂ := chooseAdjoint AdjointChoice.adjoint
    (mdeMatrix f lambda z₂ m₂)
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
      AdjointChoice.plain AdjointChoice.adjoint
  have hz₂star : (star z₂).im ≠ 0 := by simp [ne_of_gt hz₂]
  have h := pencilAdapter_centeredError_expectation
    hN f lambda hlambda.le m₁ A M₂ hz₁ hz₂star hm₁ hstable p q
  simpa only [chooseAdjoint_resolvent_eq_starParameter] using h

end CEHNative.BlockBand.External.CEH
