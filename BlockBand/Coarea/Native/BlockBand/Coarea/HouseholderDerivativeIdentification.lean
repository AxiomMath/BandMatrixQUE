module

public import BlockBand.Coarea.Native.BlockBand.Coarea.HouseholderFrameDerivative

/-!
# Identification of the phase-fixed Householder derivative

This module identifies the algebraic first variation of the phase-fixed
Householder frame with its Fréchet derivative.  All derivatives are
taken over `ℝ`, so complex conjugation contributes its real-linear derivative.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- Evaluation of a matrix entry as a real continuous linear map. -/
def matrixEntryEvaluationCLM
    {ι : Type*} [Fintype ι] (a b : ι) :
    Matrix ι ι ℂ →L[ℝ] ℂ :=
  ({ toFun := fun A => A a b
     map_add' := by intro A B; rfl
     map_smul' := by intro c A; rfl } :
    Matrix ι ι ℂ →ₗ[ℝ] ℂ).toContinuousLinearMap

/-- The explicit algebraic first variation is the Fréchet derivative
of the phase-fixed Householder frame on its nonsingular chart. -/
theorem hasFDerivAt_phaseFixedHouseholderFrame_algebraic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hden : 1 + (v i).re ≠ 0) :
    HasFDerivAt (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w)
      (phaseFixedHouseholderAlgebraicDifferential i v).toContinuousLinearMap v := by
  have hentry (a b : ι) : HasFDerivAt
      (fun w : EuclideanSpace ℂ ι => phaseFixedHouseholderFrame i w a b)
      ((matrixEntryEvaluationCLM a b).comp
        (phaseFixedHouseholderAlgebraicDifferential i v).toContinuousLinearMap) v := by
    rw [show (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w a b) =
      fun w : EuclideanSpace ℂ ι => -(if a = b then 1 else 0) +
        (((1 + (w i).re)⁻¹ : ℝ) : ℂ) *
          (w a + phaseFixedCoordinateVector i a) *
          star (w b + phaseFixedCoordinateVector i b) by
    funext w
    rw [phaseFixedHouseholderFrame_apply]
    rfl]
    have hea (k : ι) : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι => w k) (euclideanEvaluationCLM k) v :=
      (euclideanEvaluationCLM k).hasFDerivAt
    have hre : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι => (w i).re)
        (Complex.reCLM.comp (euclideanEvaluationCLM i)) v :=
      Complex.reCLM.hasFDerivAt.comp v (hea i)
    have hdenom : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι => 1 + (w i).re)
        (Complex.reCLM.comp (euclideanEvaluationCLM i)) v := by
      convert (hasFDerivAt_const (1 : ℝ) v).add hre using 1; simp
    have hinv := (hasFDerivAt_inv hden).comp v hdenom
    have hcoeff := Complex.ofRealCLM.hasFDerivAt.comp v hinv
    have hleft : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι =>
          w a + phaseFixedCoordinateVector i a)
        (euclideanEvaluationCLM a) v := by
      convert (hea a).add
        (hasFDerivAt_const (phaseFixedCoordinateVector i a) v) using 1; simp
    have hright : HasFDerivAt
        (fun w : EuclideanSpace ℂ ι =>
          star (w b + phaseFixedCoordinateVector i b))
        (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp
        (euclideanEvaluationCLM b)) v := by
      convert ((hea b).add
        (hasFDerivAt_const (phaseFixedCoordinateVector i b) v)).star using 1; simp
    apply ((hasFDerivAt_const
        (-(if a = b then (1 : ℂ) else 0)) v).add
        ((hcoeff.mul hleft).mul hright)).congr_fderiv
    apply ContinuousLinearMap.ext
    intro u
    simp [matrixEntryEvaluationCLM, euclideanEvaluationCLM,
      phaseFixedHouseholderAlgebraicDifferential, Matrix.vecMulVec_apply,
      phaseFixedHouseholderShift, smul_eq_mul]
    ring
  have hpi := hasFDerivAt_pi.mpr (fun a =>
    hasFDerivAt_pi.mpr (fun b => hentry a b))
  have heq :
      (phaseFixedHouseholderAlgebraicDifferential i v).toContinuousLinearMap =
        ContinuousLinearMap.pi (fun a => ContinuousLinearMap.pi (fun b =>
          (matrixEntryEvaluationCLM a b).comp
            (phaseFixedHouseholderAlgebraicDifferential i v).toContinuousLinearMap)) := by
    apply ContinuousLinearMap.ext
    intro u
    ext a b
    rfl
  rw [heq]
  exact hpi

/-- Consequently Mathlib's bundled `fderiv` is exactly the algebraic formula. -/
theorem fderiv_phaseFixedHouseholderFrame_eq_algebraic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hden : 1 + (v i).re ≠ 0) :
    fderiv ℝ (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w) v =
      (phaseFixedHouseholderAlgebraicDifferential i v).toContinuousLinearMap :=
  (hasFDerivAt_phaseFixedHouseholderFrame_algebraic i v hden).fderiv

end CoareaNative.BlockBand
