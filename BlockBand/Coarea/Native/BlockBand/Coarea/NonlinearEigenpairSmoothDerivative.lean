module

public import BlockBand.Coarea.Native.BlockBand.Coarea.NonlinearEigenpairChartDerivative
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairAtlasReconstruction
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth coordinate form of the nonlinear eigenpair decoder

This module proves the joint Fréchet derivative of moving
Householder conjugation from any coherently normed finite-dimensional source,
then transports the nonlinear eigenpair decoder algebraically to the paper's
finite real Hermitian coordinates.  It also proves the zero-slice inverse
identity and the exact gap-density determinant after transport.

The final specialization to `HasFDerivAt` on `HermitianCoordinateSpace d`
is not stated here: in Mathlib, that abbreviation is
a plain finite function type, whose standalone `Pi.addCommGroup` and
`Pi.Function.module` instances are not definitionally equal to the additive
and module fields underlying the available `Pi.normedAddCommGroup` and
`Pi.normedSpace`.  Composing the algebraic chart equivalences with a Fréchet
derivative therefore exposes a kernel-level typeclass diamond.  Resolving it
requires changing the analytic coordinate carrier to
`EuclideanSpace ℝ (Fin ...)` (and transporting the existing measurable atlas),
or one coherent coordinate topology on it.  No global instance is introduced
here, and no smooth-atlas completion is claimed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

/-- A real-linear map into a finite complex matrix space is continuous when
its source is finite dimensional.  We bundle this entrywise because Mathlib
does not place a norm on raw `Matrix` types. -/
def matrixLinearMapToContinuous
    {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [Fintype ι]
    (L : X →ₗ[ℝ] Matrix ι ι ℂ) :
    X →L[ℝ] Matrix ι ι ℂ :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
    ({ toFun := fun x => L x a b
       map_add' := fun x y => by simp
       map_smul' := fun c x => by simp } : X →ₗ[ℝ] ℂ).toContinuousLinearMap

@[simp] theorem matrixLinearMapToContinuous_apply
    {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [Fintype ι]
    (L : X →ₗ[ℝ] Matrix ι ι ℂ) (x : X) :
    matrixLinearMapToContinuous L x = L x := by
  rfl

/-- Fixed two-sided multiplication on an arbitrary finite matrix index. -/
def matrixFixedConjugationLinearMap
    {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ where
  toFun A := H * A * Hᴴ
  map_add' A C := by simp [mul_add, add_mul]
  map_smul' c A := by
    change H * ((c : ℂ) • A) * Hᴴ = (c : ℂ) • (H * A * Hᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Joint derivative of a moving phase-fixed Householder conjugation when
both the frame vector and the conjugated matrix vary. -/
theorem hasFDerivAt_phaseFixedHouseholder_joint_conjugation
    {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [Fintype ι] [DecidableEq ι]
    (i : ι) (w : X → EuclideanSpace ℂ ι)
    (A : X → Matrix ι ι ℂ) (x : X)
    (w' : X →L[ℝ] EuclideanSpace ℂ ι)
    (A' : X →ₗ[ℝ] Matrix ι ι ℂ)
    (hw : HasFDerivAt w w' x)
    (hAentry : ∀ a b, HasFDerivAt (fun y => A y a b)
      ((matrixEntryEvaluationCLM a b).comp
        (matrixLinearMapToContinuous A')) x)
    (hden : 1 + (w x i).re ≠ 0) :
    HasFDerivAt (fun y =>
      phaseFixedHouseholderFrame i (w y) * A y *
        (phaseFixedHouseholderFrame i (w y))ᴴ)
      (matrixLinearMapToContinuous
        ((movingPhaseFixedConjugationDifferential i (w x) (A x)).comp
            w'.toLinearMap +
          (matrixFixedConjugationLinearMap
            (phaseFixedHouseholderFrame i (w x))).comp
              A')) x := by
  have hHentry (a b : ι) :=
    (hasFDerivAt_phaseFixedHouseholderFrame_entry i a b (w x) hden).comp x hw
  have hout (a b : ι) : HasFDerivAt
      (fun y => (phaseFixedHouseholderFrame i (w y) * A y *
        (phaseFixedHouseholderFrame i (w y))ᴴ) a b)
      ((matrixEntryEvaluationCLM a b).comp
        (matrixLinearMapToContinuous
          ((movingPhaseFixedConjugationDifferential i (w x) (A x)).comp
              w'.toLinearMap +
            (matrixFixedConjugationLinearMap
              (phaseFixedHouseholderFrame i (w x))).comp
              A'))) x := by
    change HasFDerivAt (fun y =>
      ∑ c : ι, (∑ z : ι,
        phaseFixedHouseholderFrame i (w y) a z * A y z c) *
          star (phaseFixedHouseholderFrame i (w y) b c)) _ x
    have hterm (c z : ι) :=
      ((hHentry a z).mul (hAentry z c)).mul (hHentry b c).star
    have hsum := HasFDerivAt.sum (u := Finset.univ) (x := x)
      (fun c _ => HasFDerivAt.sum (u := Finset.univ) (x := x)
        (fun z _ => hterm c z))
    have hsum' : HasFDerivAt (fun y =>
        ∑ c : ι, ∑ z : ι,
          phaseFixedHouseholderFrame i (w y) a z * A y z c *
            star (phaseFixedHouseholderFrame i (w y) b c)) _ x :=
      hsum.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by
          simp only [Function.comp_apply, Pi.mul_apply, Finset.sum_apply])
    have hsum'' : HasFDerivAt (fun y =>
        ∑ c : ι, (∑ z : ι,
          phaseFixedHouseholderFrame i (w y) a z * A y z c) *
            star (phaseFixedHouseholderFrame i (w y) b c)) _ x :=
      hsum'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by
          simp only [Finset.sum_mul])
    apply hsum''.congr_fderiv
    apply ContinuousLinearMap.ext
    intro u
    change _ =
      (movingPhaseFixedConjugationDifferential i (w x) (A x) (w' u) +
        matrixFixedConjugationLinearMap
          (phaseFixedHouseholderFrame i (w x)) (A' u)) a b
    simp [
      movingPhaseFixedConjugationDifferential,
      movingUnitaryConjugationAlgebraicDifferential,
      matrixFixedConjugationLinearMap, matrixEntryEvaluationCLM,
      Matrix.mul_apply, Finset.sum_add_distrib, Finset.sum_mul]
    simp only [mul_comm, mul_left_comm, mul_assoc]
    abel
  have hpi := hasFDerivAt_pi.mpr fun a =>
    hasFDerivAt_pi.mpr fun b => hout a b
  apply hpi.congr_fderiv
  apply ContinuousLinearMap.ext
  intro u
  ext a b
  rfl

/-- Entrywise form of the joint conjugation derivative. -/
theorem hasFDerivAt_phaseFixedHouseholder_joint_conjugation_entry
    {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [Fintype ι] [DecidableEq ι]
    (i : ι) (w : X → EuclideanSpace ℂ ι)
    (A : X → Matrix ι ι ℂ) (x : X)
    (w' : X →L[ℝ] EuclideanSpace ℂ ι)
    (A' : X →ₗ[ℝ] Matrix ι ι ℂ)
    (hw : HasFDerivAt w w' x)
    (hAentry : ∀ a b, HasFDerivAt (fun y => A y a b)
      ((matrixEntryEvaluationCLM a b).comp
        (matrixLinearMapToContinuous A')) x)
    (hden : 1 + (w x i).re ≠ 0) (a b : ι) :
    HasFDerivAt (fun y =>
      (phaseFixedHouseholderFrame i (w y) * A y *
        (phaseFixedHouseholderFrame i (w y))ᴴ) a b)
      ((matrixEntryEvaluationCLM a b).comp
        (matrixLinearMapToContinuous
          ((movingPhaseFixedConjugationDifferential i (w x) (A x)).comp
              w'.toLinearMap +
            (matrixFixedConjugationLinearMap
              (phaseFixedHouseholderFrame i (w x))).comp A'))) x := by
  have h := hasFDerivAt_phaseFixedHouseholder_joint_conjugation
    i w A x w' A' hw hAentry hden
  exact hasFDerivAt_pi.mp (hasFDerivAt_pi.mp h a) b

/-- Read finite real Hermitian coordinates after undoing a selected-coordinate
matrix reindexing. -/
def selectedMatrixFinCoordinateReadCLM {d : ℕ} (i : Fin d) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ →L[ℝ]
      HermitianCoordinateSpace d :=
  ContinuousLinearMap.pi fun k =>
    let c := (hermitianCoordinateEquivFin d).symm k
    match c with
    | .inl a =>
        Complex.reCLM.comp (matrixEntryEvaluationCLM
          (selectedCoordinateEquiv i a) (selectedCoordinateEquiv i a))
    | .inr (.inl ab) =>
        Complex.reCLM.comp (matrixEntryEvaluationCLM
          (selectedCoordinateEquiv i ab.1.1)
          (selectedCoordinateEquiv i ab.1.2))
    | .inr (.inr ab) =>
        Complex.imCLM.comp (matrixEntryEvaluationCLM
          (selectedCoordinateEquiv i ab.1.1)
          (selectedCoordinateEquiv i ab.1.2))

/-- Explicit real-linear equivalence between finite real Hermitian coordinates
and the project-wide Hermitian matrix subtype. -/
def hermitianFinCoordinatesLinearEquiv (d : ℕ) :
    HermitianCoordinateSpace d ≃ₗ[ℝ] RealHermitianMatrix (Fin d) where
  toFun := hermitianOfFinCoordinates d
  invFun := fun A => coordinatesOfHermitian A ∘ (hermitianCoordinateEquivFin d).symm
  left_inv x := by
    funext j
    have h := congrFun (coordinatesOfHermitian_hermitianOfCoordinates
      (x ∘ hermitianCoordinateEquivFin d))
      ((hermitianCoordinateEquivFin d).symm j)
    simpa [hermitianOfFinCoordinates] using h
  right_inv A := by
    apply Subtype.ext
    have hc :
        coordinatesOfHermitian
            (⟨A.1, A.2⟩ : HermitianMatrix (Fin d)) =
          (fun c => coordinatesOfHermitian A c) := by
      funext c
      rcases c with c | c
      · rfl
      · rcases c with c | c <;> rfl
    have h := congrArg Subtype.val
      (hermitianOfCoordinates_coordinatesOfHermitian
        (⟨A.1, A.2⟩ : HermitianMatrix (Fin d)))
    rw [hc] at h
    simpa [hermitianOfFinCoordinates, Function.comp_def] using h
  map_add' x y := by
    apply Subtype.ext
    exact (hermitianCoordinatesLinearMap d).map_add
      (x ∘ hermitianCoordinateEquivFin d)
      (y ∘ hermitianCoordinateEquivFin d)
  map_smul' c x := by
    apply Subtype.ext
    exact (hermitianCoordinatesLinearMap d).map_smul c
      (x ∘ hermitianCoordinateEquivFin d)

/-- Full selected eigenpair block coordinates as a linear equivalence from the
normed finite real Hermitian coordinate space. -/
def selectedEigenpairFinCoordinateLinearEquiv {d : ℕ} (i : Fin d) :
    HermitianCoordinateSpace d ≃ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (hermitianFinCoordinatesLinearEquiv d).trans
    (selectedCoordinateEigenpairLinearEquiv i)

/-- The zero-projective slice, expressed in the ambient normed real coordinate
space. -/
def selectedEigenpairZeroSliceCoordinates {d : ℕ} (i : Fin d)
    (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    HermitianCoordinateSpace d :=
  (selectedEigenpairFinCoordinateLinearEquiv i).symm
    (E, ((0 : Fin (d - 1) → ℂ), B))

/-- The nonlinear selected eigenpair decoder conjugated into finite real
Hermitian coordinates on both source and target. -/
def selectedEigenpairFinCoordinateChartDecode {d : ℕ} (i : Fin d) :
    HermitianCoordinateSpace d → HermitianCoordinateSpace d :=
  fun x => (selectedEigenpairFinCoordinateLinearEquiv i).symm
    (selectedEigenpairCoordinateChartDecode i
      (selectedEigenpairFinCoordinateLinearEquiv i x))

/-- Reading selected finite coordinates after canonical block reconstruction
is the inverse of the full selected block-coordinate equivalence. -/
theorem selectedMatrixFinCoordinateRead_decode
    {d : ℕ} (i : Fin d)
    (y : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    selectedMatrixFinCoordinateReadCLM i
        ((eigenpairHermitianBlockLinearEquiv (Fin (d - 1))).symm y).1 =
      (selectedEigenpairFinCoordinateLinearEquiv i).symm y := by
  let K := (eigenpairHermitianBlockLinearEquiv (Fin (d - 1))).symm y
  have hs :
      (selectedCoordinateEigenpairLinearEquiv i).symm y =
        selectedCoordinateHermitianUnreindex i K := by
    change selectedCoordinateHermitianUnreindex i
        ((eigenpairHermitianBlockLinearEquiv (Fin (d - 1))).symm y) =
      selectedCoordinateHermitianUnreindex i K
    rfl
  symm
  funext k
  change (hermitianFinCoordinatesLinearEquiv d).symm
      ((selectedCoordinateEigenpairLinearEquiv i).symm y) k = _
  rw [hs]
  generalize hc : (hermitianCoordinateEquivFin d).symm k = c
  change coordinatesOfHermitian
      (⟨(selectedCoordinateHermitianUnreindex i K).1,
        (selectedCoordinateHermitianUnreindex i K).2⟩ :
          HermitianMatrix (Fin d))
      ((hermitianCoordinateEquivFin d).symm k) = _
  rw [hc]
  rcases c with a | c
  · simp [selectedMatrixFinCoordinateReadCLM, coordinatesOfHermitian,
      selectedCoordinateHermitianUnreindex, Matrix.reindex_apply, K, hc,
      matrixEntryEvaluationCLM]
  · rcases c with ab | ab <;>
      simp [selectedMatrixFinCoordinateReadCLM, coordinatesOfHermitian,
        selectedCoordinateHermitianUnreindex, Matrix.reindex_apply, K, hc,
        matrixEntryEvaluationCLM]

/-- The transported decoder is obtained by reading real Hermitian coordinates
from the selected-coordinate unreindexing of the canonical nonlinear matrix. -/
theorem selectedEigenpairFinCoordinateChartDecode_eq_read
    {d : ℕ} (i : Fin d) (x : HermitianCoordinateSpace d) :
    selectedEigenpairFinCoordinateChartDecode i x =
      selectedMatrixFinCoordinateReadCLM i
        (canonicalEigenpairChartDecode
          (selectedEigenpairFinCoordinateLinearEquiv i x)).1 := by
  rw [selectedEigenpairFinCoordinateChartDecode,
    selectedEigenpairCoordinateChartDecode_eq_canonical]
  funext k
  change (hermitianFinCoordinatesLinearEquiv d).symm
      ((selectedCoordinateEigenpairLinearEquiv i).symm
        ((eigenpairHermitianBlockLinearEquiv (Fin (d - 1)))
          (canonicalEigenpairChartDecode
            (selectedEigenpairFinCoordinateLinearEquiv i x)))) k = _
  generalize hc : (hermitianCoordinateEquivFin d).symm k = c
  let K := canonicalEigenpairChartDecode
    (selectedEigenpairFinCoordinateLinearEquiv i x)
  have hs :
      (selectedCoordinateEigenpairLinearEquiv i).symm
          ((eigenpairHermitianBlockLinearEquiv (Fin (d - 1))) K) =
        selectedCoordinateHermitianUnreindex i K := by
    change selectedCoordinateHermitianUnreindex i
        ((eigenpairHermitianBlockLinearEquiv (Fin (d - 1))).symm
          ((eigenpairHermitianBlockLinearEquiv (Fin (d - 1))) K)) =
      selectedCoordinateHermitianUnreindex i K
    rw [(eigenpairHermitianBlockLinearEquiv (Fin (d - 1))).symm_apply_apply]
  rw [hs]
  change coordinatesOfHermitian
      (⟨(selectedCoordinateHermitianUnreindex i K).1,
        (selectedCoordinateHermitianUnreindex i K).2⟩ :
          HermitianMatrix (Fin d))
      ((hermitianCoordinateEquivFin d).symm k) = _
  rw [hc]
  rcases c with a | c
  · simp [selectedMatrixFinCoordinateReadCLM, coordinatesOfHermitian,
      selectedCoordinateHermitianUnreindex, Matrix.reindex_apply, K, hc,
      matrixEntryEvaluationCLM]
  · rcases c with ab | ab <;>
      simp [selectedMatrixFinCoordinateReadCLM, coordinatesOfHermitian,
        selectedCoordinateHermitianUnreindex, Matrix.reindex_apply, K, hc,
        matrixEntryEvaluationCLM]

/-- Coordinate transport of the paper's selected-coordinate differential. -/
def selectedEigenpairFinCoordinateDifferential {d : ℕ} (i : Fin d)
    (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    HermitianCoordinateSpace d →ₗ[ℝ] HermitianCoordinateSpace d :=
  (selectedEigenpairFinCoordinateLinearEquiv i).symm.toLinearMap.comp
    ((eigenpairHermitianBlockCoordinateDifferential E B.1).comp
      (selectedEigenpairFinCoordinateLinearEquiv i).toLinearMap)

/-- The coordinate derivative is the Hermitian-coordinate conjugate of
`selectedCoordinateTransportedDifferential`. -/
theorem selectedEigenpairFinCoordinateDifferential_eq_transport
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    selectedEigenpairFinCoordinateDifferential i E B =
      (hermitianFinCoordinatesLinearEquiv d).symm.toLinearMap.comp
        ((selectedCoordinateTransportedDifferential i E B.1).comp
          (hermitianFinCoordinatesLinearEquiv d).toLinearMap) := by
  rfl

/-- The normed-coordinate decoder fixes every zero-projective slice. -/
@[simp] theorem selectedEigenpairFinCoordinateChartDecode_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    selectedEigenpairFinCoordinateChartDecode i
        (selectedEigenpairZeroSliceCoordinates i E B) =
      selectedEigenpairZeroSliceCoordinates i E B := by
  rw [selectedEigenpairFinCoordinateChartDecode]
  rw [selectedEigenpairZeroSliceCoordinates]
  rw [(selectedEigenpairFinCoordinateLinearEquiv i).apply_symm_apply]
  rw [selectedEigenpairCoordinateChartDecode_zero_tangent]

/-- At a zero-projective slice, the transported coordinate differential acts
by decoding the canonical energy/gap/complement variation. -/
theorem selectedEigenpairFinCoordinateDifferential_apply
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (u : HermitianCoordinateSpace d) :
    selectedEigenpairFinCoordinateDifferential i E B u =
      (selectedEigenpairFinCoordinateLinearEquiv i).symm
        (eigenpairHermitianBlockCoordinateDifferential E B.1
          (selectedEigenpairFinCoordinateLinearEquiv i u)) := by
  rfl

/-- The algebraic transported derivative has the exact gap-density determinant.
This is the determinant datum needed by a smooth-chart completion once its
ambient function-space topology is fixed coherently. -/
theorem abs_det_selectedEigenpairFinCoordinateDifferential
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    |LinearMap.det (selectedEigenpairFinCoordinateDifferential i E B)| =
      eigenpairLocalRealJacobianDensity E B.1 := by
  rw [selectedEigenpairFinCoordinateDifferential]
  rw [show LinearMap.det
      ((selectedEigenpairFinCoordinateLinearEquiv i).symm.toLinearMap.comp
        ((eigenpairHermitianBlockCoordinateDifferential E B.1).comp
          (selectedEigenpairFinCoordinateLinearEquiv i).toLinearMap)) =
      LinearMap.det (eigenpairHermitianBlockCoordinateDifferential E B.1) by
    simpa using LinearMap.det_conj
      (eigenpairHermitianBlockCoordinateDifferential E B.1)
      (selectedEigenpairFinCoordinateLinearEquiv i).symm]
  exact abs_det_eigenpairHermitianBlockCoordinateDifferential E B.1

end CoareaNative.BlockBand
