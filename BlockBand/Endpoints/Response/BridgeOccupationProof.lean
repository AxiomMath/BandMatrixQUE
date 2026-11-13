module

public import BlockBand.Endpoints.Response.BridgeOccupationProofIntegrate

/-!
# The bridge-occupation lemma for measurable versions

`BridgeOccupationStatement` is false as formalized
(`not_bridgeOccupationStatement_of_lifetimeBridge`), because it quantifies over non-measurable
versions of the base density. This file proves the variant `BridgeOccupationMeasStatement`, in
which the version `p` is in addition jointly measurable (`bridgeOccupationMeas_of_kernelBounds`).
Its hypotheses are the following propositions, defined in other modules:
* `LbkSphereKernelPos D₀` and `LbkBaseTransitionLaw D₀` (the parts of the lifetime-bridge lemma
  that identify every measurable version with the explicit kernel), for every `D₀ > 0`;
* `LbkCornerChapmanKolmogorov D₀` (deterministic) for every `D₀ > 0`;
* `LbkHypBridgeMeanLower`, `LbkHypBridgeMeanUpper` (deterministic bounds for the hyperbolic radial
  bridge mean).

The rest is proved here: version independence for measurable versions (`bop_occupation_eq_lbk`),
the factorisation of the occupation density into hyperbolic and spherical parts
(`bop_meanTotal_lbk_eq`), the bound `Y ≤ 1` for the sphere contribution and the pointwise two-sided
bound (`bop_meanTotal_lbk_bounds`), the integration over `(0, T/r₀)` and `(δ, T)` with the exact
exponential integral, and the ratio algebra with `δ`-free constants `c' = c e^{-1}/8`,
`C' = (C+1)/c'`, `r₁ = 3` (`bop_occupation_of_pointwise`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set
open scoped ENNReal

/-- The bridge-occupation lemma for measurable versions (`BridgeOccupationMeasStatement`), from
the transition law, sphere positivity, the corner Chapman–Kolmogorov identity and the two
hyperbolic bridge-mean bounds. -/
theorem bridgeOccupationMeas_of_kernelBounds
    (hbase : ∀ D0 : ℝ, 0 < D0 →
      LbkSphereKernelPos D0 ∧ LbkBaseTransitionLaw D0 ∧ LbkCornerChapmanKolmogorov D0)
    (hL : LbkHypBridgeMeanLower) (hU : LbkHypBridgeMeanUpper) : BridgeOccupationMeasStatement := by
  intro κ hκ
  obtain ⟨c, hc, hcL⟩ := hL κ hκ
  obtain ⟨C, hC, hCU⟩ := hU κ hκ
  refine ⟨c * Real.exp (-1) / 8, by positivity, (C + 1) / (c * Real.exp (-1) / 8), by positivity,
    3, ?_⟩
  intro D0 τ hD0 hτ hDτ p hp hpm r₀ hr₀ T hT
  obtain ⟨hpos, hlaw, hCK⟩ := hbase D0 hD0
  have hz := bop_bridgeStart_mem r₀
  have hr0 : 0 ≤ r₀ := by linarith
  have hfull : bridgeOccupation p (bridgeStart r₀) T 0 T =
      bridgeOccupation (lbkKernel D0) (bridgeStart r₀) T 0 T :=
    bop_occupation_eq_lbk hD0 hlaw hp hpm hz le_rfl le_rfl
  have hlate : ∀ δ ∈ Ioo 0 τ, bridgeOccupation p (bridgeStart r₀) T δ T =
      bridgeOccupation (lbkKernel D0) (bridgeStart r₀) T δ T := fun δ hδ =>
    bop_occupation_eq_lbk hD0 hlaw hp hpm hz hδ.1.le le_rfl
  have hpt : ∀ s ∈ Ioo 0 T,
      ENNReal.ofReal (c * ((Real.cosh ((1 - s / T) * r₀) - 1) / 2)) ≤
          bridgeMeanTotal (lbkKernel D0) (bridgeStart r₀) T s ∧
        bridgeMeanTotal (lbkKernel D0) (bridgeStart r₀) T s ≤
          ENNReal.ofReal (C * Real.exp ((1 - s / T) * r₀)) + 1 := fun s hs =>
    bop_meanTotal_lbk_bounds hD0 hpos hCK hz hs.1 hs.2 (hcL D0 τ hD0 hτ hDτ r₀ hr0 T hT s hs)
      (hCU D0 τ hD0 hτ hDτ r₀ hr0 T hT s hs)
  obtain ⟨h1, h2, h3⟩ := bop_occupation_of_pointwise hc hC hr₀ hT (fun s hs => (hpt s hs).1)
    (fun s hs => (hpt s hs).2)
  refine ⟨?_, ?_, fun δ hδ => ?_⟩
  · rw [hfull]; exact h1
  · rw [hfull]; exact h2
  · rw [hlate δ hδ, hfull]; exact h3 δ hδ

end BlockBand.Endpoints
