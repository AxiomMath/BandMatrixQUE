module
public import BlockBand.Coarea.Native.BlockBand.Coarea.HouseholderDerivativeIdentification
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Full differential of moving Householder conjugation

For a fixed matrix `A`, the conjugation `w ↦ U(w) A U(w)ᴴ` by the phase-fixed Householder frame
`U(w)` is differentiable wherever `1 + Re wᵢ ≠ 0`, with an explicit real Fréchet derivative.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand
open Matrix

/-- The full real-linear first variation of conjugation by the moving
phase-fixed Householder frame. -/
def movingPhaseFixedConjugationDifferential
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι) (A : Matrix ι ι ℂ) :
    EuclideanSpace ℂ ι →ₗ[ℝ] Matrix ι ι ℂ where
  toFun u := movingUnitaryConjugationAlgebraicDifferential
    (phaseFixedHouseholderFrame i v)
    (phaseFixedHouseholderAlgebraicDifferential i v u) A
  map_add' u z := by
    rw [map_add]
    simp only [movingUnitaryConjugationAlgebraicDifferential,
      conjTranspose_add, add_mul, mul_add]
    abel
  map_smul' c u := by
    change movingUnitaryConjugationAlgebraicDifferential _
      (phaseFixedHouseholderAlgebraicDifferential i v (c • u)) A = _
    rw [map_smul]
    ext a b
    simp [movingUnitaryConjugationAlgebraicDifferential, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]

/-- Each entry of the algebraic Householder differential is the derivative of
the corresponding frame entry. -/
theorem hasFDerivAt_phaseFixedHouseholderFrame_entry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i a b : ι) (v : EuclideanSpace ℂ ι)
    (hden : 1 + (v i).re ≠ 0) :
    HasFDerivAt (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w a b)
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

/-- The full derivative of moving Householder conjugation is the sum of the
frame variation on the left and its conjugate-transpose variation on the
right.  This proof is entrywise, avoiding any commutativity assumption on
matrix multiplication. -/
theorem hasFDerivAt_phaseFixedHouseholder_conjugation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι) (A : Matrix ι ι ℂ)
    (hden : 1 + (v i).re ≠ 0) :
    HasFDerivAt (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w * A *
        (phaseFixedHouseholderFrame i w)ᴴ)
      (movingPhaseFixedConjugationDifferential i v A).toContinuousLinearMap v := by
  have hentry (a b : ι) :=
    hasFDerivAt_phaseFixedHouseholderFrame_entry i a b v hden
  have hout (a b : ι) : HasFDerivAt
      (fun w : EuclideanSpace ℂ ι =>
        (phaseFixedHouseholderFrame i w * A *
          (phaseFixedHouseholderFrame i w)ᴴ) a b)
      ((matrixEntryEvaluationCLM a b).comp
        (movingPhaseFixedConjugationDifferential i v A).toContinuousLinearMap) v := by
    change HasFDerivAt (fun w : EuclideanSpace ℂ ι =>
      ∑ x : ι, (∑ y : ι,
        phaseFixedHouseholderFrame i w a y * A y x) *
          star (phaseFixedHouseholderFrame i w b x)) _ v
    have hterm (x y : ι) :=
      ((hentry a y).mul
        (hasFDerivAt_const (𝕜 := ℝ) (A y x) v)).mul
          (hentry b x).star
    have hsum := HasFDerivAt.sum (u := Finset.univ) (x := v)
      (fun x _ => HasFDerivAt.sum (u := Finset.univ) (x := v)
        (fun y _ => hterm x y))
    have hsum' : HasFDerivAt (fun w : EuclideanSpace ℂ ι =>
        ∑ x : ι, ∑ y : ι,
          phaseFixedHouseholderFrame i w a y * A y x *
            star (phaseFixedHouseholderFrame i w b x)) _ v :=
      hsum.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun w => by
          simp only [Pi.mul_apply, Finset.sum_apply]))
    have hsum'' : HasFDerivAt (fun w : EuclideanSpace ℂ ι =>
        ∑ x : ι, (∑ y : ι,
          phaseFixedHouseholderFrame i w a y * A y x) *
            star (phaseFixedHouseholderFrame i w b x)) _ v :=
      hsum'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun w => by
          simp only [Finset.sum_mul]))
    apply hsum''.congr_fderiv
    apply ContinuousLinearMap.ext
    intro u
    simp [movingPhaseFixedConjugationDifferential,
      movingUnitaryConjugationAlgebraicDifferential, matrixEntryEvaluationCLM,
      Matrix.mul_apply, Finset.sum_add_distrib, Finset.sum_mul]
    apply Eq.trans ?_ (add_comm _ _)
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring
    · apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring
  have hpi := hasFDerivAt_pi.mpr (fun a =>
    hasFDerivAt_pi.mpr (fun b => hout a b))
  have heq :
      (movingPhaseFixedConjugationDifferential i v A).toContinuousLinearMap =
        ContinuousLinearMap.pi (fun a => ContinuousLinearMap.pi (fun b =>
          (matrixEntryEvaluationCLM a b).comp
            (movingPhaseFixedConjugationDifferential i v A).toContinuousLinearMap)) := by
    apply ContinuousLinearMap.ext
    intro u
    ext a b
    rfl
  rw [heq]
  exact hpi

/-- Mathlib's bundled derivative of moving conjugation is the explicit
paper-level algebraic differential. -/
theorem fderiv_phaseFixedHouseholder_conjugation_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι) (A : Matrix ι ι ℂ)
    (hden : 1 + (v i).re ≠ 0) :
    fderiv ℝ (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w * A *
        (phaseFixedHouseholderFrame i w)ᴴ) v =
      (movingPhaseFixedConjugationDifferential i v A).toContinuousLinearMap :=
  (hasFDerivAt_phaseFixedHouseholder_conjugation i v A hden).fderiv

end CoareaNative.BlockBand
