module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPLowerFirst

/-!
# Integrated lower-first CEH centered-error identities

Pointwise and integrated centered-error identities for the two-resolvent word in the lower-first
adjoint constellations, obtained from an MDE inverse and the integrability of the resolvent
words.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal
open PencilAdapter

/-- Lower-first pointwise centered-error identity from an MDE inverse. -/
theorem pencilAdapter_lowerFirst_centeredError_identity
    {N : ℕ} (f : Spectrum N) (lambda : ℝ) (m₁ : ℂ)
    (A M₁ M₂ : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (hz₁ : z₁.im ≠ 0)
    (hM₁ : M₁ = mdeMatrix f lambda z₁ m₁)
    (hMQ : M₁ * mdePencil f lambda z₁ m₁ = 1)
    (hstable : stabilityDenominator (lambda : ℂ) (NTrace (M₁ * M₂)) ≠ 0)
    (y : HermitianCoordinateSpace N) :
    let G₁ := resolvent f lambda (hermitianGUEBlock N y).1 z₁
    let G₂ := resolvent f lambda (hermitianGUEBlock N y).1 z₂
    let Mhat := twoResolventApprox (lambda : ℂ) M₁ A M₂
    let t := NTrace Mhat
    G₁ * A * G₂ - Mhat =
      M₁ * (A + (((lambda : ℂ) ^ 2 * t) •
        (1 : Matrix (Fin N) (Fin N) ℂ))) * (G₂ - M₂) +
      M₁ * centeredTraceRemainder (lambda : ℂ) m₁ t G₁ A G₂ -
      M₁ * underlinedTwoResolventWord (lambda : ℂ)
        (hermitianGUEBlock N y).1 G₁ A G₂ := by
  dsimp only
  subst M₁
  let G₁ := resolvent f lambda (hermitianGUEBlock N y).1 z₁
  let G₂ := resolvent f lambda (hermitianGUEBlock N y).1 z₂
  let M₁ := mdeMatrix f lambda z₁ m₁
  let Mhat := twoResolventApprox (lambda : ℂ) M₁ A M₂
  let t := NTrace Mhat
  have hs := pencilAdapter_lowerFirst_centeredSource_of_inverse
    f lambda m₁ t A z₁ z₂ hz₁ hMQ y
  have hf := twoResolventApprox_fixedPoint (lambda : ℂ) M₁ A M₂ hstable
  change M₁ * underlinedTwoResolventWord (lambda : ℂ)
      (hermitianGUEBlock N y).1 G₁ A G₂ =
    -(G₁ * A * G₂) + M₁ * (A + (((lambda : ℂ) ^ 2 * t) •
      (1 : Matrix (Fin N) (Fin N) ℂ))) * G₂ +
      M₁ * centeredTraceRemainder (lambda : ℂ) m₁ t G₁ A G₂ at hs
  change Mhat = M₁ * A * M₂ +
    ((lambda : ℂ) ^ 2 * t) • (M₁ * M₂) at hf
  change G₁ * A * G₂ - Mhat =
    M₁ * (A + (((lambda : ℂ) ^ 2 * t) •
      (1 : Matrix (Fin N) (Fin N) ℂ))) * (G₂ - M₂) +
    M₁ * centeredTraceRemainder (lambda : ℂ) m₁ t G₁ A G₂ -
    M₁ * underlinedTwoResolventWord (lambda : ℂ)
      (hermitianGUEBlock N y).1 G₁ A G₂
  rw [hs, hf]
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  noncomm_ring

/-- Fully integrated lower-first centered-error equation.  Every use of
linearity is justified by the concrete integrability adapters. -/
theorem pencilAdapter_lowerFirst_centeredError_expectation
    {N : ℕ} (hN : 0 < N) (f : Spectrum N) (lambda : ℝ) (m₁ : ℂ)
    (A M₁ M₂ : Matrix (Fin N) (Fin N) ℂ) {z₁ z₂ : ℂ}
    (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (hM₁ : M₁ = mdeMatrix f lambda z₁ m₁)
    (hMQ : M₁ * mdePencil f lambda z₁ m₁ = 1)
    (hstable : stabilityDenominator (lambda : ℂ) (NTrace (M₁ * M₂)) ≠ 0)
    (p q : Fin N) :
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
  let Mhat := twoResolventApprox (lambda : ℂ) M₁ A M₂
  let t := NTrace Mhat
  let oneTerm := fun y : HermitianCoordinateSpace N =>
    M₁ * (A + (((lambda : ℂ) ^ 2 * t) • (1 : Matrix (Fin N) (Fin N) ℂ))) *
      (resolvent f lambda (hermitianGUEBlock N y).1 z₂ - M₂)
  let remTerm := fun y : HermitianCoordinateSpace N =>
    M₁ * centeredTraceRemainder (lambda : ℂ) m₁ t
      (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
      (resolvent f lambda (hermitianGUEBlock N y).1 z₂)
  let underTerm := fun y : HermitianCoordinateSpace N =>
    M₁ * underlinedTwoResolventWord (lambda : ℂ) (hermitianGUEBlock N y).1
      (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
      (resolvent f lambda (hermitianGUEBlock N y).1 z₂)
  have hone := integrable_pencilAdapter_centeredError_oneResolvent
    f lambda t M₁ M₂ A hz₂ p q
  have hrem := integrable_pencilAdapter_left_centeredTraceRemainder
    hN f lambda m₁ t M₁ A hz₁ hz₂ p q
  have hunder := integrable_pencilAdapter_left_underlinedWord
    hN f lambda M₁ A hz₁ hz₂ p q
  rw [show (fun y : HermitianCoordinateSpace N =>
      (resolvent f lambda (hermitianGUEBlock N y).1 z₁ * A *
        resolvent f lambda (hermitianGUEBlock N y).1 z₂ - Mhat) p q) =
      (fun y => (oneTerm y + remTerm y - underTerm y) p q) by
    funext y
    exact congrFun (congrFun
      (pencilAdapter_lowerFirst_centeredError_identity f lambda m₁ A M₁ M₂
        z₁ z₂ hz₁ hM₁ hMQ hstable y) p) q]
  change (∫ y, (oneTerm y + remTerm y - underTerm y) p q
      ∂normalizedGUEMeasure N) =
    ∫ y, (oneTerm y + remTerm y) p q ∂normalizedGUEMeasure N
  simp only [Matrix.add_apply, Matrix.sub_apply]
  calc
    (∫ y, oneTerm y p q + remTerm y p q - underTerm y p q
      ∂normalizedGUEMeasure N) =
      (∫ y, oneTerm y p q + remTerm y p q ∂normalizedGUEMeasure N) -
        ∫ y, underTerm y p q ∂normalizedGUEMeasure N :=
      integral_sub (hone.add hrem) hunder
    _ = _ := by rw [pencilAdapter_left_underlined_expectation_eq_zero
      hN f lambda M₁ A hz₁ hz₂ p q, sub_zero]

/-- Spectral parameter selected by an adjoint choice. -/
def chosenSpectralParameter (c : AdjointChoice) (z : ℂ) : ℂ :=
  match c with
  | .plain => z
  | .adjoint => star z

theorem chooseAdjoint_resolvent_eq_chosenParameter
    {N : ℕ} (f : Spectrum N) (lambda : ℝ) (c : AdjointChoice)
    (z : ℂ) (y : HermitianCoordinateSpace N) :
    chooseAdjoint c (resolvent f lambda (hermitianGUEBlock N y).1 z) =
      resolvent f lambda (hermitianGUEBlock N y).1
        (chosenSpectralParameter c z) := by
  cases c
  · rfl
  · exact chooseAdjoint_resolvent_eq_starParameter f lambda z y

/-- The two source-shaped constellations `-+` and `--`, uniformly indexed by the second adjoint
choice. -/
theorem upperSolution_adjointFirst_centeredError_expectation
    {N : ℕ} (hN : 0 < N) (f : Spectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (A : Matrix (Fin N) (Fin N) ℂ)
    (z₁ z₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (c₂ : AdjointChoice) (p q : Fin N) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let m₁ := CEHNative.BlockBand.CEH.upperSolution hN f hs z₁ hz₁
    let m₂ := CEHNative.BlockBand.CEH.upperSolution hN f hs z₂ hz₂
    let M₁ := chooseAdjoint .adjoint (mdeMatrix f lambda z₁ m₁)
    let M₂ := chooseAdjoint c₂ (mdeMatrix f lambda z₂ m₂)
    let Mhat := twoResolventApprox (lambda : ℂ) M₁ A M₂
    let t := NTrace Mhat
    (∫ y : HermitianCoordinateSpace N,
      (chooseAdjoint .adjoint
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) * A *
        chooseAdjoint c₂
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂) - Mhat) p q
      ∂normalizedGUEMeasure N) =
    ∫ y : HermitianCoordinateSpace N,
      (M₁ * (A + (((lambda : ℂ) ^ 2 * t) •
          (1 : Matrix (Fin N) (Fin N) ℂ))) *
          (chooseAdjoint c₂
            (resolvent f lambda (hermitianGUEBlock N y).1 z₂) - M₂) +
        M₁ * centeredTraceRemainder (lambda : ℂ) (star m₁) t
          (chooseAdjoint .adjoint
            (resolvent f lambda (hermitianGUEBlock N y).1 z₁)) A
          (chooseAdjoint c₂
            (resolvent f lambda (hermitianGUEBlock N y).1 z₂))) p q
      ∂normalizedGUEMeasure N := by
  dsimp only
  let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  let m₁ := CEHNative.BlockBand.CEH.upperSolution hN f hs z₁ hz₁
  let m₂ := CEHNative.BlockBand.CEH.upperSolution hN f hs z₂ hz₂
  let M₁ := chooseAdjoint .adjoint (mdeMatrix f lambda z₁ m₁)
  let M₂ := chooseAdjoint c₂ (mdeMatrix f lambda z₂ m₂)
  have hm₁ := CEHNative.BlockBand.CEH.upperSolution_isSolution
    hN f hs z₁ hz₁
  have hm₂ := CEHNative.BlockBand.CEH.upperSolution_isSolution
    hN f hs z₂ hz₂
  have hstable : stabilityDenominator (lambda : ℂ)
      (NTrace (M₁ * M₂)) ≠ 0 := by
    simpa [M₁, M₂] using constellation_stability_ne_zero hN f lambda hlambda.le
      z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂ .adjoint c₂
  have hMQ : M₁ * mdePencil f lambda (star z₁) (star m₁) = 1 := by
    change (mdeMatrix f lambda z₁ m₁)ᴴ *
      mdePencil f lambda (star z₁) (star m₁) = 1
    rw [mdeMatrix_conjTranspose]
    exact upperSolution_adjoint_mdeInverse hN f lambda hlambda z₁ hz₁
  have hz₁' : (star z₁).im ≠ 0 := by simp [ne_of_gt hz₁]
  have hz₂' : (chosenSpectralParameter c₂ z₂).im ≠ 0 := by
    cases c₂ <;> simp [chosenSpectralParameter, ne_of_gt hz₂]
  have h := pencilAdapter_lowerFirst_centeredError_expectation
    hN f lambda (star m₁) A M₁ M₂ hz₁' hz₂'
    (by simp [M₁, mdeMatrix_conjTranspose]) hMQ hstable p q
  simpa only [chooseAdjoint_resolvent_eq_chosenParameter,
    chosenSpectralParameter] using h

end CEHNative.BlockBand.External.CEH
