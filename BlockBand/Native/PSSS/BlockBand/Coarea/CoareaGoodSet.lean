module

public import BlockBand.Native.PSSS.BlockBand.Coarea.HermitianSimpleSpectrum
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
public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.MeasurableMatrixInverse
public import BlockBand.Native.PSSS.BlockBand.Spectral.Measurable.Counts

/-!
# Measurable good sets for eigenpair coarea

This module isolates the unconditional exceptional-set and measurability facts used by
the eigenpair coarea theorem.  It works only with explicit finite-dimensional
Hermitian coordinates.  The simple-spectrum discriminant is null, and for every fixed
Hermitian matrix Lebesgue-almost every energy avoids its finite ordered spectrum.
Consequently the corresponding pole and complementary-collision sets are null for
product Lebesgue measure, and for every measure absolutely continuous with respect to
that product measure.

The core density below records exactly the squared complementary gap determinant and
the additive inertia sector.  It does not involve a random-matrix law or a physical
Schur complement.

Normalization (for the complete coarea formula): ordered ranks are zero-based in Lean, so the
rank equation is written without truncated subtraction as `N_R(E) + N_-(M) + 1 = r.val + 1`.  There are no asymptotic
parameters or limit orders in this module.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal

/-- The explicit simple-spectrum good set is measurable and has full volume. -/
theorem ae_hermitianSimpleSpectrumCoordinates (d : ℕ) :
    ∀ᵐ x ∂(volume : Measure (HermitianCoordinateSpace d)),
      x ∈ hermitianSimpleSpectrumCoordinates d := by
  rw [ae_iff]
  exact volume_hermitianSimpleSpectrumCoordinates_compl d

end PSSSNative.BlockBand
