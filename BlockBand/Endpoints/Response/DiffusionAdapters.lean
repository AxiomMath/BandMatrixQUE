module

public import BlockBand.Endpoints.Response.DiffusionCorrespondence

/-!
# The diffusion inputs of the lifetime-bridge and bridge-occupation lemmas

This file proves the seven diffusion inputs (`LbkBaseExistence`, `LbkBaseTransitionLaw`,
`LbkCornerCKX`, `LbkCornerHeatIdentity`, `LbkDoobKilledLaw`, `LbkBridgeExistence`,
`LbkHypRadialGaussCompare`) from the corresponding theorems of `BlockBand.Diffusion`. With them,
`lifetimeBridge_of_doob'` gives `LifetimeBridgeStatement` and `bridgeOccupationMeas_of_baseCKX`
gives `BridgeOccupationMeasStatement`, both with no hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-!
### The seven inputs
-/

/-- Existence of the base diffusion, from `BlockBand.Diffusion.hasExBaseDiffusion` (field by
field). -/
theorem lbkBaseExistence_holds : ∀ D0 : ℝ, 0 < D0 → LbkBaseExistence D0 := fun D0 hD0 z hz => by
  obtain ⟨Ω, m, 𝓖, P, Z, h⟩ := BlockBand.Diffusion.hasExBaseDiffusion D0 hD0 z hz
  exact ⟨Ω, m, 𝓖, P, Z, ⟨h.prob, h.adapted, h.start, h.paths, h.martingale⟩⟩

/-- The transition law of the base diffusion, from
`BlockBand.Diffusion.exLbkBaseTransitionLaw_holds` (field by field). -/
theorem lbkBaseTransitionLaw_holds : ∀ D0 : ℝ, 0 < D0 → LbkBaseTransitionLaw D0 :=
  fun D0 hD0 t ht z hz Ω m 𝓖 P Z hZ =>
    BlockBand.Diffusion.exLbkBaseTransitionLaw_holds D0 hD0 t ht z hz Ω m 𝓖 P Z
      ⟨hZ.prob, hZ.adapted, hZ.start, hZ.paths, hZ.martingale⟩

/-- Corner Chapman–Kolmogorov identity for the hyperbolic factor, from
`BlockBand.Diffusion.exLbkCornerCKX_holds` (by unfolding). -/
theorem lbkCornerCKX_holds : ∀ D0 : ℝ, 0 < D0 → LbkCornerCKX D0 :=
  BlockBand.Diffusion.exLbkCornerCKX_holds

/-- The corner heat identity, from `BlockBand.Diffusion.chLbkCornerHeatIdentity` (by
unfolding). -/
theorem lbkCornerHeatIdentity_holds : ∀ D0 : ℝ, 0 < D0 → LbkCornerHeatIdentity D0 :=
  BlockBand.Diffusion.chLbkCornerHeatIdentity

/-- The Doob killed law, from `BlockBand.Diffusion.dkLbkDoobKilledLaw_holds` (field by field). -/
theorem lbkDoobKilledLaw_holds : ∀ D0 : ℝ, 0 < D0 → LbkDoobKilledLaw D0 :=
  fun D0 hD0 x y hz Ω m 𝓖 P N X Y hP =>
    BlockBand.Diffusion.dkLbkDoobKilledLaw_holds D0 hD0 x y hz Ω m 𝓖 P N X Y
      ⟨hP.prob, hP.adapted, hP.start,
        hP.paths.mono fun _ hp => ⟨hp.antitone, hp.chamber, hp.rightCont, hp.cont, hp.deletion⟩,
        hP.martingale⟩

/-- Existence of the continuous base bridge, from `BlockBand.Diffusion.brLbkBridgeExistence`
(field by field). -/
theorem lbkBridgeExistence_holds : ∀ D0 : ℝ, 0 < D0 → LbkBridgeExistence D0 :=
  fun D0 hD0 x y hz t ht => by
    obtain ⟨Ω, mΩ, P, Z, h⟩ := BlockBand.Diffusion.brLbkBridgeExistence D0 hD0 x y hz t ht
    exact ⟨Ω, mΩ, P, Z, ⟨h.prob, h.meas, h.paths, h.fdd⟩⟩

/-- The radial Gaussian comparison, from `BlockBand.Diffusion.gcHypRadialGaussCompare` (by
unfolding). -/
theorem lbkHypRadialGaussCompare_holds : LbkHypRadialGaussCompare :=
  BlockBand.Diffusion.gcHypRadialGaussCompare

/-!
### The two lemmas
-/

/-- The lifetime-bridge lemma, with no hypotheses: `lifetimeBridge_of_doob'` with its five inputs
supplied by the theorems above. -/
theorem lifetimeBridgeStatement_holds : LifetimeBridgeStatement :=
  lifetimeBridge_of_doob' fun D0 hD0 =>
    ⟨lbkBaseExistence_holds D0 hD0, lbkBaseTransitionLaw_holds D0 hD0,
      lbkCornerHeatIdentity_holds D0 hD0, lbkDoobKilledLaw_holds D0 hD0,
      lbkBridgeExistence_holds D0 hD0⟩

/-- The bridge-occupation lemma in measurable form (`BridgeOccupationMeasStatement`), with no
hypotheses: `bridgeOccupationMeas_of_baseCKX` with its inputs supplied by the theorems above. -/
theorem bridgeOccupationMeasStatement_holds : BridgeOccupationMeasStatement :=
  bridgeOccupationMeas_of_baseCKX
    (fun D0 hD0 => ⟨lbkBaseTransitionLaw_holds D0 hD0, lbkCornerCKX_holds D0 hD0⟩)
    lbkHypRadialGaussCompare_holds

end BlockBand.Endpoints
