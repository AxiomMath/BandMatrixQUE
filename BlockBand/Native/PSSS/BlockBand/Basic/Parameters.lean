module

public import BlockBand.Native.PSSS.BlockBand.Conventions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Nat

/-!
# Admissible finite parameters and critical-sequence adapters

The total dimension is `L = nW`. Both the finite ratio and every variance
parameter use real division. The physical ring has no parity requirement.
The parameter API fixes `b` before evaluating the integer sequence, and
the critical ratio may be zero without forcing `n → ∞`. Explicit nonzero
dimension witnesses are provided; block embeddings, projections and
cardinality are treated with the site indices.

The endpoint filters are the right-sided real filter `𝓝[τ > 0] 0` and the
real filter `atTop`, **after** the positive finite-ratio critical family.
The adapters only specialize the explicit convergence hypotheses of critical sequences.
They neither prove those hypotheses for this model nor exchange the order
of limits. There is no matrix probability law, Gaussian construction,
eigenvector selection or QUE estimate here.
-/

@[expose] public section

set_option autoImplicit false

namespace PSSSNative.BlockBand

open Filter Topology

/-- The finite model parameters `(n, W, b)` with `n ≥ 4`, `W ≥ 1` and `0 < b < 1/2`. -/
abbrev Params := Conventions.ModelParameters

namespace Params

end Params

namespace CriticalSeq

end CriticalSeq

end PSSSNative.BlockBand
