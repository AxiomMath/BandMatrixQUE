module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedAmbientIdentification
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiMovingCountMeasurability

/-!
# Fixed-target predecessor weight in the Minami reduction

PSSS formula (2.13) in arXiv:1608.02922 weights the auxiliary
open-interval multiplicity by the predecessor factorial of the full public
deformation on the fixed target `Icc a b`.  In the ambient compression
representation this fixed count has one canonical zero removed exactly when
zero belongs to `Icc a b`.  The weight below therefore has no energy, Cauchy,
radial, or dyadic parameter.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 300000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The order-`r` predecessor on the fixed target interval: the descending factorial of the
`Icc a b` count of the reconstructed ambient compression, minus one when `0 ∈ Icc a b`.  The
matrix input is totalized by Hermitian part, so this is defined on every projected matrix
argument of the weighted selected-block estimate. -/
def fixedTargetPredecessorWeight
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) (a b : ℝ) (r : ℕ)
    (p : BlockProductDisintegration.ExteriorSample dims j ×
      Matrix (Fin (dims j)) (Fin (dims j)) ℂ) : ℝ≥0∞ :=
  (((eigenCount (reconstructedFullCompression A₀ j φ p.1 p.2)
      (Set.Icc a b) -
        (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r : ℝ≥0∞))

end PSSSNative.BlockBand.PSSS
