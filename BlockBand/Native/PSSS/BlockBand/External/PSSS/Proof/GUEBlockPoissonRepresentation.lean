module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEArbitraryFixedVectorTail
public import BlockBand.Native.PSSS.BlockBand.Analysis.HermitianPoissonTrace
public import BlockBand.Native.PSSS.BlockBand.Analysis.PoissonLayerCake
public import BlockBand.Native.PSSS.BlockBand.Analysis.PositiveResolvent

/-!
# Poisson resolvents for one normalized canonical GUE block

This module records the deterministic Ward/Poisson identity in the exact
normalization used by the canonical `GUE_N(1/N)` inverse-tail theorem.  It is
the pointwise block-resolvent representation needed before any probabilistic
layer-cake argument.  No Wegner estimate, conditional block law, or
integrability assertion is made here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder

/-- Shift a Hermitian deformation by a real spectral energy. -/
def energyShiftHermitian {N : ℕ}
    (A : HermitianMatrix (Fin N)) (e : ℝ) : HermitianMatrix (Fin N) :=
  ⟨A.1 - (e : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ),
    A.2.sub (Matrix.isHermitian_one.smul
      (isSelfAdjoint_iff.mpr (Complex.conj_ofReal e)))⟩

end PSSSNative.BlockBand.PSSS
