module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHCanonicalHeightRectangle
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHSpectralExtractionPackaging

/-!
# Probability packaging for rectangular CEH grids

A product energy-height mesh replaces the unproved Lipschitz modulus of the canonical
spacing graph.  This file records its exact finite union cost.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open MeasureTheory
open scoped ENNReal

/-- The random spectral-pair event inherits the fixed-pair tail with the exact
square of the rectangular-grid cardinality. -/
theorem measure_localETHTwoResolventRandomBadEvent_le_rectangularGrid_sq_mul
    {Ω : Type*} [MeasurableSpace Ω] {N realMesh heightMesh : ℕ}
    (μ : Measure Ω) (f : Ω → ℂ → ℂ → ℂ)
    (etaF : ℝ → ℝ) (ξ E₀ R etaMin etaMax : ℝ)
    (lam : Ω → Fin N → ℝ) (threshold : Fin N → Fin N → ℝ)
    (gridThreshold : ℝ) (p : ENNReal)
    (hsubset :
      localETHTwoResolventRandomBadEvent f etaF ξ lam threshold ⊆
        fixedTwoResolventGridBadEvent f
          (localETHRectangularSpectralGridPoint
            E₀ R etaMin etaMax realMesh heightMesh)
          gridThreshold)
    (hpair : ∀ a b : Fin (realMesh + 1) × Fin (heightMesh + 1),
      μ (fixedTwoResolventGridPairBadEvent f
        (localETHRectangularSpectralGridPoint
          E₀ R etaMin etaMax realMesh heightMesh)
        gridThreshold a b) ≤ p) :
    μ (localETHTwoResolventRandomBadEvent f etaF ξ lam threshold) ≤
      ((((realMesh + 1) * (heightMesh + 1) : ℕ) : ENNReal) ^ 2) * p := by
  simpa [card_localETHRectangularSpectralGridIndex] using
    measure_localETHTwoResolventRandomBadEvent_le_card_sq_mul_of_subset
      μ f etaF ξ lam threshold
      (localETHRectangularSpectralGridPoint
        E₀ R etaMin etaMax realMesh heightMesh)
      gridThreshold p hsubset hpair

end CEHNative.BlockBand.External.CEH
