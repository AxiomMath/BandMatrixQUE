module

public import BlockBand.Coarea.Native.BlockBand.Coarea.SelectedCoordinateEigenpairChart
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Differentiability of the phase-fixed Householder frame

The phase-fixed Householder formula is rational in the real and imaginary
coordinates of its vector argument.  This module proves Fréchet
differentiability throughout the nonsingular chart and records the exact
first-order algebraic formula.  It also packages the corresponding moving
conjugation differential and identifies its canonical off-diagonal block with
the gap action `(E I - B)z`.

The final equality between the explicitly packaged algebraic differential and
Mathlib's `fderiv` is intentionally isolated: establishing it requires a lengthy
entrywise derivative normalization, while differentiability and the paper's
canonical off-diagonal differential are proved here without an assumption.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- Coordinate evaluation on complex Euclidean space as a real continuous
linear map. -/
def euclideanEvaluationCLM
    {ι : Type*} [Fintype ι] (i : ι) :
    EuclideanSpace ℂ ι →L[ℝ] ℂ :=
  ({ toFun := fun v => v i
     map_add' := by intro x y; rfl
     map_smul' := by intro c x; simp } :
    EuclideanSpace ℂ ι →ₗ[ℝ] ℂ).toContinuousLinearMap

/-- Componentwise conjugation after evaluation is real differentiable. -/
theorem differentiableAt_star_euclideanEvaluation
    {ι : Type*} [Fintype ι] (i : ι) (v : EuclideanSpace ℂ ι) :
    DifferentiableAt ℝ (fun w : EuclideanSpace ℂ ι => star (w i)) v := by
  exact (euclideanEvaluationCLM i).differentiableAt.star

/-- The explicit Householder frame is Fréchet differentiable wherever its real
denominator is nonzero. -/
theorem differentiableAt_phaseFixedHouseholderFrame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hden : 1 + (v i).re ≠ 0) :
    DifferentiableAt ℝ
      (fun w : EuclideanSpace ℂ ι => phaseFixedHouseholderFrame i w) v := by
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  rw [show (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w a b) =
      fun w : EuclideanSpace ℂ ι => -(if a = b then 1 else 0) +
        (((1 + (w i).re)⁻¹ : ℝ) : ℂ) *
          (w a + phaseFixedCoordinateVector i a) *
          star (w b + phaseFixedCoordinateVector i b) by
    funext w
    rw [phaseFixedHouseholderFrame_apply]
    rfl]
  have hea (k : ι) : DifferentiableAt ℝ
      (fun w : EuclideanSpace ℂ ι => w k) v :=
    (euclideanEvaluationCLM k).differentiableAt
  have hre : DifferentiableAt ℝ
      (fun w : EuclideanSpace ℂ ι => (w i).re) v := by
    exact Complex.reCLM.differentiableAt.comp v (hea i)
  have hcoeff : DifferentiableAt ℝ
      (fun w : EuclideanSpace ℂ ι =>
        (((1 + (w i).re)⁻¹ : ℝ) : ℂ)) v := by
    exact Complex.ofRealCLM.differentiableAt.comp v
      (((differentiableAt_const (1 : ℝ)).add hre).inv hden)
  have hleft : DifferentiableAt ℝ
      (fun w : EuclideanSpace ℂ ι =>
        w a + phaseFixedCoordinateVector i a) v :=
    (hea a).add (differentiableAt_const (phaseFixedCoordinateVector i a))
  have hright : DifferentiableAt ℝ
      (fun w : EuclideanSpace ℂ ι =>
        star (w b + phaseFixedCoordinateVector i b)) v := by
    exact ((hea b).add
      (differentiableAt_const (phaseFixedCoordinateVector i b))).star
  exact (differentiableAt_const
    (-(if a = b then (1 : ℂ) else 0))).add
      ((hcoeff.mul hleft).mul hright)

/-- The Fréchet derivative of the Householder frame, bundled with its
verified derivative statement. -/
theorem hasFDerivAt_phaseFixedHouseholderFrame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hden : 1 + (v i).re ≠ 0) :
    HasFDerivAt (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w)
      (fderiv ℝ (fun w : EuclideanSpace ℂ ι =>
        phaseFixedHouseholderFrame i w) v) v :=
  (differentiableAt_phaseFixedHouseholderFrame i v hden).hasFDerivAt

/-- The algebraic first variation of the Householder matrix.

For `w=v+eᵢ`, `d=1+Re(vᵢ)`, and variation `u`, this is
`-Re(uᵢ)d⁻² wwᴴ + d⁻¹(uwᴴ + wuᴴ)`. -/
def phaseFixedHouseholderAlgebraicDifferential
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι →ₗ[ℝ] Matrix ι ι ℂ where
  toFun u :=
    -((((1 + (v i).re)⁻¹ ^ 2 * (u i).re : ℝ) : ℂ) •
      Matrix.vecMulVec (phaseFixedHouseholderShift i v)
        (star (phaseFixedHouseholderShift i v))) +
    (((1 + (v i).re)⁻¹ : ℝ) : ℂ) •
      (Matrix.vecMulVec u (star (phaseFixedHouseholderShift i v)) +
       Matrix.vecMulVec (phaseFixedHouseholderShift i v) (star u))
  map_add' u z := by
    ext a b
    simp [Matrix.vecMulVec_apply]
    ring
  map_smul' c u := by
    ext a b
    simp [Matrix.vecMulVec_apply, smul_eq_mul]
    ring

/-- First variation of conjugation by a moving frame. -/
def movingUnitaryConjugationAlgebraicDifferential
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H dH A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  dH * A * Hᴴ + H * A * dHᴴ

/-- The canonical infinitesimal moving-frame conjugation is the commutator with
the skew-Hermitian projective rotation. -/
theorem movingConjugationDifferential_canonical
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) (z : n → ℂ) :
    movingUnitaryConjugationAlgebraicDifferential
      1 (eigenpairInfinitesimalRotation z)
      (eigenpairCanonicalMatrix E B) =
    eigenpairInfinitesimalRotation z * eigenpairCanonicalMatrix E B -
      eigenpairCanonicalMatrix E B * eigenpairInfinitesimalRotation z := by
  rw [movingUnitaryConjugationAlgebraicDifferential,
    eigenpairInfinitesimalRotation_conjTranspose]
  simp
  noncomm_ring

/-- Its lower-left/off-diagonal component is exactly `(E I - B)z`. -/
theorem movingConjugationDifferential_canonical_lowerLeft
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) (z : n → ℂ) (j : n) :
    movingUnitaryConjugationAlgebraicDifferential
      1 (eigenpairInfinitesimalRotation z)
      (eigenpairCanonicalMatrix E B)
      (Sum.inr j) (Sum.inl Unit.unit) =
    (eigenpairGapMatrix E B *ᵥ z) j := by
  rw [movingConjugationDifferential_canonical]
  exact eigenpair_commutator_lowerLeft E B z j

/-- Thus the moving-frame off-diagonal component agrees with the project-wide
canonical coordinate differential. -/
theorem movingConjugationDifferential_eq_canonicalCoordinate_offdiag
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : ℝ) (B : Matrix n n ℂ) (z : n → ℂ) (j : n) :
    movingUnitaryConjugationAlgebraicDifferential
      1 (eigenpairInfinitesimalRotation z)
      (eigenpairCanonicalMatrix E B)
      (Sum.inr j) (Sum.inl Unit.unit) =
    (eigenpairCanonicalCoordinateDifferential E B
      (0, (0, z))).2.2 j := by
  rw [movingConjugationDifferential_canonical_lowerLeft]
  rfl

end CoareaNative.BlockBand
