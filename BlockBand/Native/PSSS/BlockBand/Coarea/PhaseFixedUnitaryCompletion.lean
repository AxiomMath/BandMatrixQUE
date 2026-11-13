module

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
public import Mathlib.MeasureTheory.Function.Jacobian
public import BlockBand.Native.PSSS.BlockBand.Probability.GaussianNormalization
public import BlockBand.Native.PSSS.BlockBand.Coarea.GaussianRegression

/-!
# Explicit phase-fixed Householder completion

For a unit vector `v` whose distinguished coordinate is positive real, the
reflection

`H(v) = -I + (v + e)(v + e)ᴴ / (1 + vᵢ)`

is nonsingular on the entire phase-fixed affine chart and sends the distinguished
coordinate vector `e` to `v`.  Unlike the usual `v - e` Householder formula, this
choice has denominator `1 + vᵢ`, so it has no singularity at `v = e`.

This module only defines the distinguished coordinate vector `e`,
`phaseFixedCoordinateVector`. The frame itself, its chart-column identity, regularity and
unitarity are developed in `CoareaNative.BlockBand`, where the finite-sum unitarity identity
`CoareaNative.BlockBand.PhaseFixedHouseholderUnitaryIdentity` is proved as
`CoareaNative.BlockBand.phaseFixedHouseholderUnitaryIdentity`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix Set

/-- The standard coordinate vector at `i`. -/
def phaseFixedCoordinateVector {ι : Type*} [DecidableEq ι]
    (i : ι) : ι → ℂ := Pi.single i 1

end PSSSNative.BlockBand
