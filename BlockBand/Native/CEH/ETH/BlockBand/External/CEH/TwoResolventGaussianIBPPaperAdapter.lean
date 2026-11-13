module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPScaled

/-!
# Paper-facing CEH adapter for the scaled Gaussian loop

This module identifies the scaled full-coordinate resolvent with CEH's
`PencilAdapter.resolvent`, then combines the exact Gaussian cancellation with
the random and MDE inverse equations.  The remaining terms are
centered observables; no concentration or local-law estimate is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal
open PencilAdapter

/-- The scaled full-coordinate resolvent is definitionally the CEH resolvent
of the diagonal deformation and the reconstructed Hermitian GUE block. -/
theorem scaledFullGUEResolvent_deformationMatrix
    {N : ℕ} (f : Spectrum N) (lambda : ℝ) (z : ℂ)
    (y : HermitianCoordinateSpace N) :
    scaledFullGUEResolvent (deformationMatrix f) lambda z y =
      resolvent f lambda (hermitianGUEBlock N y).1 z := by
  rfl

/-- The random-source part of CEH's underlined word. -/
def underlinedRandomSource {N : ℕ} (lambda : ℂ)
    (W G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  lambda • (W * G₁ * A * G₂)

/-- The two trace-feedback terms in CEH's underlined word. -/
def underlinedTraceFeedback {N : ℕ} (lambda : ℂ)
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (lambda ^ 2 * NTrace G₁) • (G₁ * A * G₂) +
    (lambda ^ 2 * NTrace (G₁ * A * G₂)) • G₂

/-- The source/feedback split is exactly the previously defined underlined
word. -/
theorem underlinedTwoResolventWord_eq_source_add_feedback
    {N : ℕ} (lambda : ℂ)
    (W G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    underlinedTwoResolventWord lambda W G₁ A G₂ =
      underlinedRandomSource lambda W G₁ A G₂ +
        underlinedTraceFeedback lambda G₁ A G₂ := by
  unfold underlinedTwoResolventWord underlinedRandomSource
    underlinedTraceFeedback
  abel

/-- The scaled Gaussian IBP cancellation in the exact paper-facing split of
`underlinedTwoResolventWord`.  Keeping the two Bochner integrals separate
records precisely the form produced by coordinate IBP without silently
assuming an additional integrability lemma. -/
theorem pencilAdapter_splitUnderlined_masterCancellation
    {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      underlinedRandomSource (lambda : ℂ)
        (hermitianGUEBlock N y).1
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) +
      (∫ y : HermitianCoordinateSpace N,
        underlinedTraceFeedback (lambda : ℂ)
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q
        ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) = 0 := by
  have h := scaledNormalizedGUE_literalBlock_masterCancellation
    hN (deformationMatrix f) (deformationMatrix f) A
    (deformationMatrix_isHermitian f) (deformationMatrix_isHermitian f)
    lambda hz₁ hz₂ p q
  simpa only [underlinedRandomSource, underlinedTraceFeedback,
    scaledFullGUEResolvent_deformationMatrix, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.smul_mul, Matrix.mul_assoc,
    NTrace, CEHNative.BlockBand.Conventions.normalizedTrace] using h

/-- Pointwise CEH MDE-source identity for the reconstructed GUE block
and the random resolvents.  The random inverse equation is discharged,
not supplied as a certificate. -/
theorem pencilAdapter_underlined_mdeSource
    {N : ℕ} (f : Spectrum N) (lambda : ℝ) (m t : ℂ)
    (A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (hz₁ : z₁.im ≠ 0) (y : HermitianCoordinateSpace N) :
    underlinedTwoResolventWord (lambda : ℂ)
        (hermitianGUEBlock N y).1
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂) =
      -(mdePencil f lambda z₁ m *
          resolvent f lambda (hermitianGUEBlock N y).1 z₁ * A *
          resolvent f lambda (hermitianGUEBlock N y).1 z₂) +
        (A + (((lambda : ℂ) ^ 2 * t) •
          (1 : Matrix (Fin N) (Fin N) ℂ))) *
          resolvent f lambda (hermitianGUEBlock N y).1 z₂ +
        centeredTraceRemainder (lambda : ℂ) m t
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂) := by
  apply underlinedTwoResolventWord_mdeSource
  exact resolventPencil_mul_resolvent f lambda
    (hermitianGUEBlock N y).1 (hermitianGUEBlock N y).2 hz₁

/-- The two deterministic MDE and two random resolvent inverse equations for
the paper-facing objects. -/
theorem pencilAdapter_actualInverseEquations
    {N : ℕ} (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (z₁ m₁ z₂ m₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hm₁ : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₁ m₁)
    (hm₂ : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₂ m₂)
    (y : HermitianCoordinateSpace N) :
    mdeMatrix f lambda z₁ m₁ * mdePencil f lambda z₁ m₁ = 1 ∧
      mdeMatrix f lambda z₂ m₂ * mdePencil f lambda z₂ m₂ = 1 ∧
      resolventPencil f lambda (hermitianGUEBlock N y).1 z₁ *
          resolvent f lambda (hermitianGUEBlock N y).1 z₁ = 1 ∧
        resolventPencil f lambda (hermitianGUEBlock N y).1 z₂ *
          resolvent f lambda (hermitianGUEBlock N y).1 z₂ = 1 := by
  exact ⟨mdeMatrix_mul_mdePencil f lambda hlambda z₁ m₁ hz₁ hm₁.2,
    mdeMatrix_mul_mdePencil f lambda hlambda z₂ m₂ hz₂ hm₂.2,
    resolventPencil_mul_resolvent f lambda
      (hermitianGUEBlock N y).1 (hermitianGUEBlock N y).2 (ne_of_gt hz₁),
    resolventPencil_mul_resolvent f lambda
      (hermitianGUEBlock N y).1 (hermitianGUEBlock N y).2 (ne_of_gt hz₂)⟩

/-- Left multiplication by the MDE inverse removes the first MDE
pencil in the centered source identity.  Both inverse equations are discharged
from the scalar MDE solution and the concrete random resolvent. -/
theorem pencilAdapter_mdeInverse_centeredSource
    {N : ℕ} (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (m t : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (hz₁ : 0 < z₁.im)
    (hm : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₁ m)
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
  rw [pencilAdapter_underlined_mdeSource
    f lambda m t A z₁ z₂ (ne_of_gt hz₁) y]
  have hMQ := mdeMatrix_mul_mdePencil f lambda hlambda z₁ m hz₁ hm.2
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

/-- Pointwise centered error equation around the deterministic CEH
two-resolvent approximation.  Its last term has zero split expectation by
`pencilAdapter_splitUnderlined_masterCancellation`; the first two terms are
the one-resolvent and centered-trace remainders still requiring
probabilistic estimates. -/
theorem pencilAdapter_centeredError_identity
    {N : ℕ} (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (m₁ : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (z₁ z₂ : ℂ)
    (hz₁ : 0 < z₁.im)
    (hm₁ : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₁ m₁)
    (M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hstable : stabilityDenominator (lambda : ℂ)
      (NTrace (mdeMatrix f lambda z₁ m₁ * M₂)) ≠ 0)
    (y : HermitianCoordinateSpace N) :
    let M₁ := mdeMatrix f lambda z₁ m₁
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
  let M₁ := mdeMatrix f lambda z₁ m₁
  let G₁ := resolvent f lambda (hermitianGUEBlock N y).1 z₁
  let G₂ := resolvent f lambda (hermitianGUEBlock N y).1 z₂
  let Mhat := twoResolventApprox (lambda : ℂ) M₁ A M₂
  let t := NTrace Mhat
  have hsource := pencilAdapter_mdeInverse_centeredSource
    f lambda hlambda m₁ t A z₁ z₂ hz₁ hm₁ y
  have hfixed := twoResolventApprox_fixedPoint
    (lambda : ℂ) M₁ A M₂ hstable
  change G₁ * A * G₂ - Mhat =
    M₁ * (A + (((lambda : ℂ) ^ 2 * t) •
      (1 : Matrix (Fin N) (Fin N) ℂ))) * (G₂ - M₂) +
    M₁ * centeredTraceRemainder (lambda : ℂ) m₁ t G₁ A G₂ -
    M₁ * underlinedTwoResolventWord (lambda : ℂ)
      (hermitianGUEBlock N y).1 G₁ A G₂
  change M₁ * underlinedTwoResolventWord (lambda : ℂ)
      (hermitianGUEBlock N y).1 G₁ A G₂ =
    -(G₁ * A * G₂) +
      M₁ * (A + (((lambda : ℂ) ^ 2 * t) •
        (1 : Matrix (Fin N) (Fin N) ℂ))) * G₂ +
      M₁ * centeredTraceRemainder (lambda : ℂ) m₁ t G₁ A G₂ at hsource
  change Mhat = M₁ * A * M₂ +
    ((lambda : ℂ) ^ 2 * t) • (M₁ * M₂) at hfixed
  rw [hsource, hfixed]
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_one]
  noncomm_ring

/-- **Centered split expectation equation.**  Gaussian IBP, the concrete
random inverse equation, and the centered trace decomposition give this exact
identity.  The two displayed feedback integrals are deliberately retained:
cancelling them into a single Bochner integral requires only a routine
integrability adapter, not a probabilistic estimate.  The sole uncontrolled
quantity is the `centeredTraceRemainder`. -/
theorem pencilAdapter_centered_splitExpectation
    {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ) (m t : ℂ)
    (A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      (-(mdePencil f lambda z₁ m *
          resolvent f lambda (hermitianGUEBlock N y).1 z₁ * A *
          resolvent f lambda (hermitianGUEBlock N y).1 z₂) +
        (A + (((lambda : ℂ) ^ 2 * t) •
          (1 : Matrix (Fin N) (Fin N) ℂ))) *
          resolvent f lambda (hermitianGUEBlock N y).1 z₂ +
        centeredTraceRemainder (lambda : ℂ) m t
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂) -
        underlinedTraceFeedback (lambda : ℂ)
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂)) p q
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) +
      (∫ y : HermitianCoordinateSpace N,
        underlinedTraceFeedback (lambda : ℂ)
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q
        ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) = 0 := by
  have hcancel := pencilAdapter_splitUnderlined_masterCancellation
    hN f lambda A hz₁ hz₂ p q
  rw [← hcancel]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  have hsource := pencilAdapter_underlined_mdeSource
    f lambda m t A z₁ z₂ hz₁ y
  rw [underlinedTwoResolventWord_eq_source_add_feedback] at hsource
  have hentry := congrFun (congrFun hsource p) q
  simp only [Matrix.add_apply, Matrix.sub_apply] at hentry ⊢
  linear_combination -hentry

end CEHNative.BlockBand.External.CEH
