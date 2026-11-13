module

public import BlockBand.Native.PSSS.BlockBand.Analysis.ProjectedWegnerSchur
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Probability.IdentDistrib
public import BlockBand.Native.PSSS.BlockBand.Basic.Indices
public import BlockBand.Native.PSSS.BlockBand.Spectral.Ordered
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistribIndep

/-!
# Deterministic physical-block reconstruction and the diagonal normalization

This module carries the Gaussian-ring exterior coordinates and an arbitrary normalized
singleton block back to the physical site matrix.  The reconstruction is measurable
and, on the exterior vector and normalized diagonal block, recovers `M.H`
pointwise.

The physical diagonal block is `√c • G`, whereas `schurMatrixTrace` inserts the
standard `GUE_W(1/W)` matrix `G` with coefficient one, so the physical resolvent is
identified with `schurMatrixTrace` only after rescaling the pencil by `(√c)⁻¹`, or
when `c = 1`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix MeasureTheory
open scoped ComplexOrder ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

end GaussianRing
end PSSSNative.BlockBand
