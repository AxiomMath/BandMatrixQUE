module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFullCompressionFatou
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.PublicAmbientCompressionEndpointNull

/-!
# Unconditional fixed-target full-compression factorial bound

This module closes the endpoint hypothesis in the full-public compression
Fatou bridge with the heterogeneous public block-product law.  The
predecessor interval is the fixed target `Icc a b`; no moving radial interval
or selected-block endpoint substitute occurs.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 700000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The order-`r` public factorial estimate unconditionally bounds the
canonical-zero-subtracted fixed-target compression predecessor.  Endpoint
nullity is supplied by the full ambient compression theorem under
`publicBlockProductMeasure`.

Source: Peled–Schenker–Shamis–Sodin, formula (2.13), arXiv:1608.02922. -/
theorem publicBlock_lintegral_compressionPredecessor_le_of_publicFactorialAtOrder'
    {C : ℝ} {r k : ℕ} (hind : PublicFactorialAtOrder C r)
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (u : EuclideanSpace ℂ (BlockGUE.Index dims)) (hu : ‖u‖ = 1)
    {a b : ℝ} (hab : a ≤ b) :
    (∫⁻ G,
      ((eigenCount (compressHermitian (publicBlockDeformation A₀ G) u)
        (Set.Icc a b) -
          (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r : ℝ≥0∞)
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
      ENNReal.ofReal (C * (∑ i, (dims i : ℝ)) * (b - a)) ^ r := by
  exact publicBlock_lintegral_compressionPredecessor_le_of_publicFactorialAtOrder
    hind dims hd A₀ u hu hab
      (ae_publicBlock_compressHermitian_fixedEndpoints
        dims hd A₀ u hu a b)

end PSSSNative.BlockBand.PSSS
