module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairDerivativeIdentification
public import BlockBand.Coarea.Native.BlockBand.Coarea.ProjectiveUnitReconstructionSmooth

/-!
# Global smoothness of the coherent nonlinear eigenpair decoder

The local Jacobian calculation identifies the derivative on the zero-projective
slice.  Here we prove the complementary analytic statement: throughout the
whole affine projective chart, the phase-fixed normalized eigenvector and its
Householder completion make the finite matrix product
`H(z) D(E,B) H(z)ᴴ` differentiable.  Composing with the selected-coordinate
linear readback gives global differentiability of the coherent nonlinear
eigenpair decoder.

The statements retain the source normalization: the selected affine coordinate
is phase-fixed with positive real selected entry; all remaining coordinates
are finite, and there are no limit or uniformity quantifiers.  Until an explicit
global derivative formula is needed downstream, the unique derivatives are
packed using `fderiv`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

/-- At every coherent coordinate, every entry of the moving-frame conjugation
is real differentiable.  This is the finite matrix-product calculus step. -/
theorem differentiableAt_coherentEigenpairConjugation
    {d : ℕ} (i : Fin d) (x : CoherentHermitianCoordinates d) :
    DifferentiableAt ℝ (coherentEigenpairConjugation i) x := by
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let P := coherentSelectedProjectiveInputCLM i
  have hunit : DifferentiableAt ℝ
      (fun x => coherentProjectiveUnitReconstruction e (P x)) x :=
    (differentiableAt_coherentProjectiveUnitReconstruction e (P x)).comp
      x P.differentiableAt
  have hHentry (a b : Unit ⊕ Fin (d - 1)) : DifferentiableAt ℝ
      (fun x => coherentProjectiveHouseholderFrame e (P x) a b) x := by
    change DifferentiableAt ℝ (fun x =>
      coherentPhaseFixedHouseholderFrameEntry e a b
        (coherentProjectiveUnitReconstruction e (P x))) x
    have hden :
        1 + ((coherentProjectiveUnitReconstruction e (P x)).value e).re ≠ 0 := by
      change 1 + (projectiveUnitReconstruction e (P x).value e).re ≠ 0
      have hpos := projectiveUnitReconstruction_self_re_pos e (P x).value
      linarith
    exact (differentiableAt_coherentPhaseFixedHouseholderFrameEntry
      e a b _ hden).comp x hunit
  have hD (a b : Unit ⊕ Fin (d - 1)) : DifferentiableAt ℝ
      (fun x => coherentBlockDiagonalEntryCLM i a b x) x :=
    (coherentBlockDiagonalEntryCLM i a b).differentiableAt
  have hentry (a b : Unit ⊕ Fin (d - 1)) : DifferentiableAt ℝ
      (fun x =>
        let H := coherentProjectiveHouseholderFrame e (P x)
        let D := canonicalBlockDiagonalLinearMap
          (coherentSelectedBlockInputLinearMap i x)
        (H * D * Matrix.conjTranspose H) a b) x := by
    change DifferentiableAt ℝ (fun x => ∑ c, (∑ z,
      coherentProjectiveHouseholderFrame e (P x) a z *
        coherentBlockDiagonalEntryCLM i z c x) *
      star (coherentProjectiveHouseholderFrame e (P x) b c)) x
    fun_prop
  have hfun : DifferentiableAt ℝ (fun x => fun
      (ab : (Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) =>
      let H := coherentProjectiveHouseholderFrame e (P x)
      let D := canonicalBlockDiagonalLinearMap
        (coherentSelectedBlockInputLinearMap i x)
      (H * D * Matrix.conjTranspose H) ab.1 ab.2) x :=
    differentiableAt_pi.mpr fun
      (ab : (Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) =>
        hentry ab.1 ab.2
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
  change DifferentiableAt ℝ (fun y =>
    (⟨coherentEigenpairConjugationEuclidean i y⟩ :
      CoherentComplexMatrix (Unit ⊕ Fin (d - 1)))) x
  exact (HasFDerivAt.coherentOutput heuclid.hasFDerivAt).differentiableAt

/-- The coherent moving-frame conjugation is differentiable throughout its
entire affine projective chart. -/
theorem differentiable_coherentEigenpairConjugation
    {d : ℕ} (i : Fin d) :
    Differentiable ℝ (coherentEigenpairConjugation i) :=
  fun x => differentiableAt_coherentEigenpairConjugation i x

/-- Packed global Fréchet derivative of coherent moving-frame conjugation.
The derivative is exact and unique even though this interface deliberately
does not expand its finite product-rule formula. -/
theorem hasFDerivAt_coherentEigenpairConjugation
    {d : ℕ} (i : Fin d) (x : CoherentHermitianCoordinates d) :
    HasFDerivAt (coherentEigenpairConjugation i)
      (fderiv ℝ (coherentEigenpairConjugation i) x) x :=
  (differentiableAt_coherentEigenpairConjugation i x).hasFDerivAt

/-- Selected-coordinate linear readback preserves global differentiability of
the nonlinear coherent eigenpair decoder. -/
theorem differentiableAt_coherentSelectedEigenpairDecode
    {d : ℕ} (i : Fin d) (x : CoherentHermitianCoordinates d) :
    DifferentiableAt ℝ (coherentSelectedEigenpairDecode i) x := by
  exact (coherentSelectedMatrixReadbackCLM i).differentiableAt.comp x
    (differentiableAt_coherentEigenpairConjugation i x)

/-- The coherent selected-coordinate decoder is differentiable at every point
of the affine chart. -/
theorem differentiable_coherentSelectedEigenpairDecode
    {d : ℕ} (i : Fin d) :
    Differentiable ℝ (coherentSelectedEigenpairDecode i) :=
  fun x => differentiableAt_coherentSelectedEigenpairDecode i x

/-- Packed global Fréchet derivative of the selected-coordinate readback
decoder. -/
theorem hasFDerivAt_coherentSelectedEigenpairDecode
    {d : ℕ} (i : Fin d) (x : CoherentHermitianCoordinates d) :
    HasFDerivAt (coherentSelectedEigenpairDecode i)
      (fderiv ℝ (coherentSelectedEigenpairDecode i) x) x :=
  (differentiableAt_coherentSelectedEigenpairDecode i x).hasFDerivAt

end CoareaNative.BlockBand
