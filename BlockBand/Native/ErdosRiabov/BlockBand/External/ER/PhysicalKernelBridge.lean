module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.CyclicGreenSummation

/-!
# Entrywise ER kernel bridge and flattened-distance comparison

This module identifies the matrices `Θ` and `Ξ` of the paper with the physical
site Green correction, including the exact full-site identity subtraction.
It then compares block cyclic distance with the row-major site distance used
in Erdős–Riabov's weighted clauses.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand.GaussianRing.ERPhysicalBridge

open scoped BigOperators
open ERProfile ERDiscreteFourier ERFourierInverse ERFourierAlgebra
  ERCharacterAngle ERNearestNeighbor ERCyclicDecay ERJumpNormalization
  ERCyclicSummation ERHerglotz

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Absolute distance between the canonical block representatives. -/
def blockRepresentativeDistance (p : Params) (x y : ZMod p.n) : ℕ :=
  max x.val y.val - min x.val y.val

end ERNative.BlockBand.GaussianRing.ERPhysicalBridge
