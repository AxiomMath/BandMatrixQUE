module

public import BlockBand.Native.PSSS.BlockBand.Coarea.SelectedCoordinateEigenpairChart
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import BlockBand.Native.PSSS.BlockBand.Coarea.LagrangeProjectorCorrectness
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Finset.Max
public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.Schur
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth coordinate form of the nonlinear eigenpair decoder

This module proves the joint Fréchet derivative of moving
Householder conjugation from any coherently normed finite-dimensional source,
then transports the nonlinear eigenpair decoder algebraically to the paper's
finite real Hermitian coordinates.  It also proves the zero-slice inverse
identity and the exact gap-density determinant after transport.

The specialization to `HasFDerivAt` on `HermitianCoordinateSpace d` is not
stated here: that abbreviation is
a plain finite function type, whose standalone `Pi.addCommGroup` and
`Pi.Function.module` instances are not definitionally equal to the additive
and module fields underlying the available `Pi.normedAddCommGroup` and
`Pi.normedSpace`.  Composing the algebraic chart equivalences with a Fréchet
derivative therefore exposes a kernel-level typeclass diamond, which disappears
when the analytic coordinate carrier is `EuclideanSpace ℝ (Fin ...)`.  No global
instance is introduced here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace PSSSNative.BlockBand

open Matrix

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

  

end PSSSNative.BlockBand
