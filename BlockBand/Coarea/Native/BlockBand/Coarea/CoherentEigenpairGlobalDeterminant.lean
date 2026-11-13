module

public import BlockBand.Coarea.Native.BlockBand.Coarea.ProjectiveEigenpairGlobalJacobian
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairDerivativeIdentification

/-!
# Algebraic factorization of the global coherent eigenpair determinant

This module concerns the Fréchet derivative of
`coherentSelectedEigenpairDecode` at an arbitrary affine-projective coordinate.
It transports the energy/gap/complement differential to the coherent
Hermitian carrier.  Off the complementary spectrum, its inverse gives a
canonical, explicitly defined projective correction: gap differential inverse
composed with the derivative.  We prove an exact factorization of the
absolute real determinant into the squared-gap density and the determinant of
this correction.

The full formula
`(1 + ∑ j, Complex.normSq (z j))⁻¹ ^ d * Complex.normSq (det (E I - B))`
is `abs_det_fderiv_coherentSelectedEigenpairDecode_globalInput`. With the factorization here it
gives the determinant of the correction, `abs_det_coherentEigenpairProjectiveCorrection`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

/-- Coherent input corresponding to the block coordinates `(E,z,B)`. -/
def coherentEigenpairGlobalInput {d : ℕ} (i : Fin d) (E : ℝ)
    (z : Fin (d - 1) → ℂ) (B : RealHermitianMatrix (Fin (d - 1))) :
    CoherentHermitianCoordinates d :=
  ⟨(selectedEigenpairFinCoordinateLinearEquiv i).symm (E, (z, B))⟩

/-- Linear equivalence between the coherent Hermitian carrier and the selected
energy/projective/complement block coordinates. -/
def coherentSelectedBlockCoordinateLinearEquiv {d : ℕ} (i : Fin d) :
    CoherentHermitianCoordinates d ≃ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (coherentAnalyticCarrierLinearEquiv (HermitianCoordinateSpace d)).trans
    (selectedEigenpairFinCoordinateLinearEquiv i)

/-- The zero-slice energy/gap/complement differential, conjugated to
the same coherent carrier on which the nonlinear decoder is differentiated. -/
def coherentEigenpairGapDifferential {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    CoherentHermitianCoordinates d →ₗ[ℝ] CoherentHermitianCoordinates d :=
  (coherentSelectedBlockCoordinateLinearEquiv i).symm.toLinearMap.comp
    ((eigenpairHermitianBlockCoordinateDifferential E B.1).comp
      (coherentSelectedBlockCoordinateLinearEquiv i).toLinearMap)

/-- Conjugating by selected coherent coordinates does not change the absolute
real determinant: the coherent gap differential has exactly the
squared-gap density. -/
theorem abs_det_coherentEigenpairGapDifferential {d : ℕ} (i : Fin d)
    (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    |LinearMap.det (coherentEigenpairGapDifferential i E B)| =
      eigenpairLocalRealJacobianDensity E B.1 := by
  let e := coherentSelectedBlockCoordinateLinearEquiv i
  have hdet : LinearMap.det (coherentEigenpairGapDifferential i E B) =
      LinearMap.det (eigenpairHermitianBlockCoordinateDifferential E B.1) := by
    exact LinearMap.det_conj
      (eigenpairHermitianBlockCoordinateDifferential E B.1) e.symm
  rw [hdet, abs_det_eigenpairHermitianBlockCoordinateDifferential]

/-- The coherent gap differential is nonsingular exactly off the complementary
spectrum. -/
theorem det_coherentEigenpairGapDifferential_ne_zero {d : ℕ} (i : Fin d)
    (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    LinearMap.det (coherentEigenpairGapDifferential i E B) ≠ 0 := by
  intro hzero
  have habs : |LinearMap.det (coherentEigenpairGapDifferential i E B)| = 0 := by
    rw [hzero, abs_zero]
  rw [abs_det_coherentEigenpairGapDifferential,
    eigenpairLocalRealJacobianDensity_eq_normSq_det] at habs
  exact hgap (Complex.normSq_eq_zero.mp habs)

/-- The decoder is differentiable at the arbitrary coherent input
used below, so its `fderiv` is the Fréchet derivative rather than the
default value assigned at a nondifferentiability point. -/
theorem differentiableAt_coherentSelectedEigenpairDecode_globalInput
    {d : ℕ} (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    DifferentiableAt ℝ (coherentSelectedEigenpairDecode i)
      (coherentEigenpairGlobalInput i E z B) := by
  let x := coherentEigenpairGlobalInput i E z B
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let P := coherentSelectedProjectiveInputCLM i
  have hunit : DifferentiableAt ℝ
      (fun y => coherentProjectiveUnitReconstruction e (P y)) x :=
    (differentiableAt_coherentProjectiveUnitReconstruction e (P x)).comp
      x P.differentiableAt
  have hHentry (a b : Unit ⊕ Fin (d - 1)) : DifferentiableAt ℝ
      (fun y => coherentProjectiveHouseholderFrame e (P y) a b) x := by
    change DifferentiableAt ℝ (fun y =>
      coherentPhaseFixedHouseholderFrameEntry e a b
        (coherentProjectiveUnitReconstruction e (P y))) x
    have hden :
        1 + ((coherentProjectiveUnitReconstruction e (P x)).value e).re ≠ 0 := by
      change 1 + (projectiveUnitReconstruction e (P x).value e).re ≠ 0
      have hpos := projectiveUnitReconstruction_self_re_pos e (P x).value
      linarith
    exact (differentiableAt_coherentPhaseFixedHouseholderFrameEntry
      e a b _ hden).comp x hunit
  have hD (a b : Unit ⊕ Fin (d - 1)) : DifferentiableAt ℝ
      (fun y => coherentBlockDiagonalEntryCLM i a b y) x :=
    (coherentBlockDiagonalEntryCLM i a b).differentiableAt
  have hentry (a b : Unit ⊕ Fin (d - 1)) : DifferentiableAt ℝ
      (fun y =>
        let H := coherentProjectiveHouseholderFrame e (P y)
        let D := canonicalBlockDiagonalLinearMap
          (coherentSelectedBlockInputLinearMap i y)
        (H * D * Matrix.conjTranspose H) a b) x := by
    change DifferentiableAt ℝ (fun y => ∑ c, (∑ q,
      coherentProjectiveHouseholderFrame e (P y) a q *
        coherentBlockDiagonalEntryCLM i q c y) *
      star (coherentProjectiveHouseholderFrame e (P y) b c)) x
    fun_prop
  have hfun : DifferentiableAt ℝ (fun y => fun
      (ab : (Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) =>
      let H := coherentProjectiveHouseholderFrame e (P y)
      let D := canonicalBlockDiagonalLinearMap
        (coherentSelectedBlockInputLinearMap i y)
      (H * D * Matrix.conjTranspose H) ab.1 ab.2) x :=
    differentiableAt_pi.mpr fun ab => hentry ab.1 ab.2
  let eR : EuclideanSpace ℂ ((Unit ⊕ Fin (d - 1)) ×
      (Unit ⊕ Fin (d - 1))) ≃L[ℝ]
      (((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) → ℂ) :=
    LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv _ ℂ).toLinearEquiv.restrictScalars ℝ)
  have heuclid : DifferentiableAt ℝ
      (coherentEigenpairConjugationEuclidean i) x := by
    have h := eR.symm.differentiableAt.comp x hfun
    convert h using 1
    funext y
    rfl
  have hconj : DifferentiableAt ℝ (coherentEigenpairConjugation i) x := by
    change DifferentiableAt ℝ (fun y =>
      (⟨coherentEigenpairConjugationEuclidean i y⟩ :
        CoherentComplexMatrix (Unit ⊕ Fin (d - 1)))) x
    exact (HasFDerivAt.coherentOutput heuclid.hasFDerivAt).differentiableAt
  exact (coherentSelectedMatrixReadbackCLM i).differentiableAt.comp x hconj

/-- The bundled derivative used in the determinant factorization is the
Fréchet derivative at every `(E,z,B)`. -/
theorem hasFDerivAt_coherentSelectedEigenpairDecode_globalInput
    {d : ℕ} (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    HasFDerivAt (coherentSelectedEigenpairDecode i)
      (fderiv ℝ (coherentSelectedEigenpairDecode i)
        (coherentEigenpairGlobalInput i E z B))
      (coherentEigenpairGlobalInput i E z B) :=
  (differentiableAt_coherentSelectedEigenpairDecode_globalInput
    i E z B).hasFDerivAt

/-- Canonical projective correction of the arbitrary-point derivative.
It is defined, rather than postulated, by removing the invertible gap
block from the Fréchet derivative of the nonlinear decoder. -/
def coherentEigenpairProjectiveCorrection {d : ℕ} (i : Fin d) (E : ℝ)
    (z : Fin (d - 1) → ℂ) (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    CoherentHermitianCoordinates d →ₗ[ℝ] CoherentHermitianCoordinates d :=
  ((coherentEigenpairGapDifferential i E B).equivOfDetNeZero
      (det_coherentEigenpairGapDifferential_ne_zero i E B hgap)).symm.toLinearMap.comp
    (fderiv ℝ (coherentSelectedEigenpairDecode i)
      (coherentEigenpairGlobalInput i E z B)).toLinearMap

/-- Exact factorization of the arbitrary-point Fréchet
derivative into the coherent gap block and its canonical projective
correction. -/
theorem fderiv_coherentSelectedEigenpairDecode_factorization {d : ℕ}
    (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    (fderiv ℝ (coherentSelectedEigenpairDecode i)
      (coherentEigenpairGlobalInput i E z B)).toLinearMap =
      (coherentEigenpairGapDifferential i E B).comp
        (coherentEigenpairProjectiveCorrection i E z B hgap) := by
  let G := coherentEigenpairGapDifferential i E B
  let hG := det_coherentEigenpairGapDifferential_ne_zero i E B hgap
  let eG := G.equivOfDetNeZero hG
  apply LinearMap.ext
  intro x
  change _ = G (eG.symm
    ((fderiv ℝ (coherentSelectedEigenpairDecode i)
      (coherentEigenpairGlobalInput i E z B)) x))
  change _ = eG (eG.symm
    ((fderiv ℝ (coherentSelectedEigenpairDecode i)
      (coherentEigenpairGlobalInput i E z B)) x))
  rw [eG.apply_symm_apply]
  rfl

/-- At every affine-projective coordinate, off the complementary spectrum: the absolute Jacobian is the squared spectral-gap
density times the absolute determinant of the explicit projective correction. -/
theorem abs_det_fderiv_coherentSelectedEigenpairDecode_factorization {d : ℕ}
    (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    |LinearMap.det ((fderiv ℝ (coherentSelectedEigenpairDecode i)
      (coherentEigenpairGlobalInput i E z B)).toLinearMap)| =
      eigenpairLocalRealJacobianDensity E B.1 *
        |LinearMap.det (coherentEigenpairProjectiveCorrection i E z B hgap)| := by
  rw [fderiv_coherentSelectedEigenpairDecode_factorization i E z B hgap,
    LinearMap.det_comp, abs_mul,
    abs_det_coherentEigenpairGapDifferential]

/-- Spectral-gap form of the exact reduction, ordered to match the
global formula. The first factor equals `(1 + ∑ j, normSq (z j))⁻¹ ^ d`
(`abs_det_coherentEigenpairProjectiveCorrection`). -/
theorem abs_det_fderiv_coherentSelectedEigenpairDecode_eq_correction_mul_normSq
    {d : ℕ} (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    |LinearMap.det ((fderiv ℝ (coherentSelectedEigenpairDecode i)
      (coherentEigenpairGlobalInput i E z B)).toLinearMap)| =
      |LinearMap.det (coherentEigenpairProjectiveCorrection i E z B hgap)| *
        Complex.normSq (eigenpairGapMatrix E B.1).det := by
  rw [abs_det_fderiv_coherentSelectedEigenpairDecode_factorization
    i E z B hgap, eigenpairLocalRealJacobianDensity_eq_normSq_det]
  ring

end CoareaNative.BlockBand
