module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.JumpNormalization
public import Mathlib

/-!
# Cyclic exponential summation and Green row bounds

This module sums the parity-free cyclic-distance estimates proved for the
nearest-neighbour Green kernel.  It keeps the block-constant correction and
the within-block mean-zero identity separate throughout.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERCyclicSummation

open scoped BigOperators
open ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERCharacterAngle ERNearestNeighbor ERCyclicDecay ERJumpNormalization ERHerglotz

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Canonical representatives as an explicit equivalence. -/
def zmodValEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun x := ⟨x.val, x.val_lt⟩
  invFun i := (i.val : ZMod n)
  left_inv x := ZMod.natCast_zmod_val x
  right_inv i := by
    ext
    exact ZMod.val_natCast_of_lt i.isLt

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERCyclicSummation
