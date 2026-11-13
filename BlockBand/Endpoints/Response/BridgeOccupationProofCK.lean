module

public import BlockBand.Endpoints.Response.BridgeOccupationProof

/-!
# The corner Chapman–Kolmogorov identity split into its two coordinate factors

`LbkCornerCKX D₀` (hyperbolic factor: `∫ pX_s(x,x') pX_{T-s}(x',0) dx' = pX_T(x,0)`, the semigroup
property of McKean's kernel, radialised, at the pole) and `LbkCornerCKY D₀` (spherical factor:
`∫ pY_s(y,y') pY_{T-s}(y',0) dy' = pY_T(y,0)`, which follows from Legendre orthogonality
`∫_0^1 P̃_n P̃_m = δ_{nm}/(2n+1)` and a series–integral interchange under a summable majorant)
together give the two-dimensional identity (`lbkCornerCK_of_factors`, Tonelli via `bop_mass_prod`).
Each is a one-dimensional deterministic statement, and the two are independent of each other.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set
open scoped ENNReal

/-- Corner Chapman–Kolmogorov identity for the hyperbolic radial factor. -/
def LbkCornerCKX (D0 : ℝ) : Prop :=
  ∀ T s : ℝ, 0 < s → s < T → ∀ x : ℝ, 0 ≤ x →
    bopXMass D0 x T s = ENNReal.ofReal (lbkKernelX D0 T x 0)

/-- Corner Chapman–Kolmogorov identity for the spherical radial factor. -/
def LbkCornerCKY (D0 : ℝ) : Prop :=
  ∀ T s : ℝ, 0 < s → s < T → ∀ y ∈ Icc (0 : ℝ) 1,
    bopYMass D0 y T s = ENNReal.ofReal (lbkKernelY D0 T y 0)

/-- The two coordinate identities give the corner Chapman–Kolmogorov identity. -/
theorem lbkCornerCK_of_factors {D0 : ℝ} (hD0 : 0 < D0) (hX : LbkCornerCKX D0)
    (hY : LbkCornerCKY D0) : LbkCornerChapmanKolmogorov D0 := by
  intro T s hs hsT z hz
  rw [bop_mass_prod hD0 z T s, hX T s hs hsT z.1 hz.1, hY T s hs hsT z.2 hz.2,
    bop_lbk_corner_eq hD0 z T]

/-- The bridge-occupation lemma for measurable versions, from the two coordinate-wise
Chapman–Kolmogorov identities, the kernel positivity and base transition law, and the two
bridge-mean bounds `LbkHypBridgeMeanLower`, `LbkHypBridgeMeanUpper`. -/
theorem bridgeOccupationMeas_of_factorBounds
    (hbase : ∀ D0 : ℝ, 0 < D0 → LbkSphereKernelPos D0 ∧ LbkBaseTransitionLaw D0 ∧
      LbkCornerCKX D0 ∧ LbkCornerCKY D0)
    (hL : LbkHypBridgeMeanLower) (hU : LbkHypBridgeMeanUpper) : BridgeOccupationMeasStatement :=
  bridgeOccupationMeas_of_kernelBounds (fun D0 hD0 =>
    ⟨(hbase D0 hD0).1, (hbase D0 hD0).2.1,
      lbkCornerCK_of_factors hD0 (hbase D0 hD0).2.2.1 (hbase D0 hD0).2.2.2⟩) hL hU

end BlockBand.Endpoints
