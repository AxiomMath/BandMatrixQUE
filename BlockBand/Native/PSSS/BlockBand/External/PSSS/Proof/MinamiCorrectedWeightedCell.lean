module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedRadialIntegral
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiWeightedSphereAverage

/-!
# Weighted selected-block cell estimate with the fixed-target predecessor

This specialization uses the measurable `fixedTargetPredecessorWeight` on
`Icc a b`.  The weight has no energy, Cauchy, radial, or mesh argument.  Thus
this module does not import or mention the rejected moving-predecessor
specializations.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 700000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The corrected deterministic auxiliary background before adding the
selected normalized GUE block. -/
def correctedSelectedAuxiliaryBackground
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e t : ℝ) : HermitianMatrix (Fin (dims j)) :=
  publicGUERealBackground
    (publicFrozenCanonicalHermitian A₀ j Gext e eta)
    (canonicalFrozenAbsorber
      (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
      (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext) e eta)
    (publicFrozenCanonicalAbsorber_posSemidef A₀ j Gext e heta) t

end PSSSNative.BlockBand.PSSS
