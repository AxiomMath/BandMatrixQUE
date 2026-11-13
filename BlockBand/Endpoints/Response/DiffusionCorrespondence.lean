module

public import BlockBand.Diffusion.Base.Existence
public import BlockBand.Diffusion.Base.TransitionLawHolds
public import BlockBand.Diffusion.Heat.Identity
public import BlockBand.Diffusion.Doob.Holds
public import BlockBand.Diffusion.Bridge.Existence
public import BlockBand.Diffusion.Comparison.RadialGaussCompare
public import BlockBand.Endpoints.Response.LifetimeBridgeDoob
public import BlockBand.Endpoints.Response.BridgeOccupationMean

/-!
# Correspondence between the diffusion inputs and their `BlockBand.Diffusion` counterparts

The diffusion inputs used by the lifetime-bridge and bridge-occupation lemmas have identical copies
in `BlockBand.Diffusion` under other names. This file proves that each pair agrees:
* definitionally (`rfl` / `Iff.rfl`) for renamed `def`s with the same body (after unfolding the
  renamed constants), e.g. `baseStrip = exBaseStrip`, `lbkKernel = exKernel`;
* field by field for structures with identical fields;
* as an `Iff` for each of the seven input propositions.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Diffusion (exBaseStrip exBaseGenerator IsExBaseDiffusion HasExBaseDiffusion
  exKernel mkKernelX skKernelY exBopXMass ExLbkBaseTransitionLaw ExLbkCornerCKX chHarm
  ChLbkCornerHeatIdentity IsDkRatioParameter DkDualCoord dkDualChamber dkDualGenerator
  dkDualCoordOf dkDualLift dkDualExtinction dkDualEntrance dkDualEntranceValue dkDualMartingale
  IsDkDualStart IsDkBoundaryDeletionPath IsDkBoundaryDualProcess dkDualPoint dkLastTime
  dkLastPoint dkFddProd dkHarm DkLbkDoobKilledLaw BrIsDualStart brBridgeFddDensity IsBrBaseBridge
  BrLbkBridgeExistence gcX gcEuclRadial gcHypRadial GcLbkHypRadialGaussCompare)
open scoped ENNReal NNReal

/-!
### Definitional correspondences (renamed `def`s)
-/

theorem dfa_baseStrip_eq_diffusion : baseStrip = exBaseStrip := rfl

theorem dfa_baseGenerator_eq_diffusion : baseGenerator = exBaseGenerator := rfl

theorem dfa_lbkKernelX_eq_diffusion : lbkKernelX = mkKernelX := rfl

theorem dfa_lbkKernelY_eq_diffusion : lbkKernelY = skKernelY := rfl

theorem dfa_lbkKernel_eq_diffusion : lbkKernel = exKernel := rfl

theorem dfa_bopXMass_eq_diffusion : bopXMass = exBopXMass := rfl

theorem dfa_lbkHarm_eq_chHarm : lbkHarm = chHarm := rfl

theorem dfa_lbkHarm_eq_dkHarm : lbkHarm = dkHarm := rfl

theorem dfa_isRatioParameter_iff_diffusion {p : ℕ} (x y : Fin p → ℝ) :
    IsRatioParameter x y ↔ IsDkRatioParameter x y := Iff.rfl

theorem dfa_dualCoord_eq_diffusion (q : ℕ) : DualCoord q = DkDualCoord q := rfl

theorem dfa_dualChamber_eq_diffusion (q : ℕ) : dualChamber q = dkDualChamber q := rfl

theorem dfa_dualGenerator_eq_diffusion (D0 : ℝ) {q : ℕ} (f : DualCoord q → ℝ) :
    dualGenerator D0 f = dkDualGenerator D0 f := rfl

theorem dfa_dualCoordOf_eq_diffusion (q : ℕ) (x y : ℕ → ℝ) :
    dualCoordOf q x y = dkDualCoordOf q x y := rfl

theorem dfa_dualLift_eq_diffusion {q : ℕ} (f : DualCoord q → ℝ) (n : ℕ) (x y : ℕ → ℝ) :
    dualLift f n x y = dkDualLift f n x y := rfl

theorem dfa_dualExtinction_eq_diffusion {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) :
    dualExtinction N = dkDualExtinction N := rfl

theorem dfa_dualEntrance_eq_diffusion {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (q : ℕ) :
    dualEntrance N q = dkDualEntrance N q := rfl

theorem dfa_dualEntranceValue_eq_diffusion {Ω : Type*} {q : ℕ} (f : DualCoord q → ℝ)
    (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) :
    dualEntranceValue f N X Y = dkDualEntranceValue f N X Y := rfl

theorem dfa_dualMartingale_eq_diffusion {Ω : Type*} (D0 : ℝ) (q : ℕ) (f : DualCoord q → ℝ)
    (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) :
    dualMartingale D0 q f N X Y = dkDualMartingale D0 q f N X Y := rfl

theorem dfa_isDualStart_iff_dk {p : ℕ} (x y : Fin p → ℝ) :
    IsDualStart x y ↔ IsDkDualStart x y := Iff.rfl

theorem dfa_isDualStart_iff_br {p : ℕ} (x y : Fin p → ℝ) :
    IsDualStart x y ↔ BrIsDualStart x y := Iff.rfl

theorem dfa_dualPoint_eq_diffusion {Ω : Type*} (X Y : ℝ≥0 → Ω → ℕ → ℝ) :
    dualPoint X Y = dkDualPoint X Y := rfl

theorem dfa_lbkLastTime_eq_diffusion {k : ℕ} (ts : Fin k → ℝ) : lbkLastTime ts = dkLastTime ts :=
  rfl

theorem dfa_lbkLastPoint_eq_diffusion {α : Type*} (z : α) {k : ℕ} (zs : Fin k → α) :
    lbkLastPoint z zs = dkLastPoint z zs := rfl

theorem dfa_lbkFddProd_eq_diffusion {α : Type*} (p : ℝ → α → α → ℝ) (z : α) {k : ℕ}
    (ts : Fin k → ℝ) : lbkFddProd p z ts = dkFddProd p z ts := rfl

theorem dfa_bridgeFddDensity_eq_diffusion {α : Type*} (p : ℝ → α → α → ℝ) (z e : α) (t : ℝ)
    {k : ℕ} (ts : Fin k → ℝ) : bridgeFddDensity p z e t ts = brBridgeFddDensity p z e t ts := rfl

theorem dfa_bomX_eq_diffusion : bomX = gcX := rfl

theorem dfa_bomEuclRadial_eq_diffusion : bomEuclRadial = gcEuclRadial := rfl

theorem dfa_lbkHypRadial_eq_diffusion : lbkHypRadial = gcHypRadial := rfl

/-!
### Field-by-field correspondences (field-identical structures)
-/

theorem dfa_isBaseDiffusion_iff_diffusion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ) (z : ℝ × ℝ)
    (Z : ℝ≥0 → Ω → ℝ × ℝ) : IsBaseDiffusion P 𝓖 D0 z Z ↔ IsExBaseDiffusion P 𝓖 D0 z Z :=
  ⟨fun h => ⟨h.prob, h.adapted, h.start, h.paths, h.martingale⟩,
    fun h => ⟨h.prob, h.adapted, h.start, h.paths, h.martingale⟩⟩

theorem dfa_hasBaseDiffusion_iff_diffusion (D0 : ℝ) (z : ℝ × ℝ) :
    HasBaseDiffusion D0 z ↔ HasExBaseDiffusion D0 z :=
  ⟨fun ⟨Ω, m, 𝓖, P, Z, h⟩ => ⟨Ω, m, 𝓖, P, Z, ⟨h.prob, h.adapted, h.start, h.paths, h.martingale⟩⟩,
    fun ⟨Ω, m, 𝓖, P, Z, h⟩ => ⟨Ω, m, 𝓖, P, Z, ⟨h.prob, h.adapted, h.start, h.paths, h.martingale⟩⟩⟩

theorem dfa_isBoundaryDeletionPath_iff_diffusion (n : ℝ≥0 → ℕ) (x y : ℝ≥0 → ℕ → ℝ) :
    IsBoundaryDeletionPath n x y ↔ IsDkBoundaryDeletionPath n x y :=
  ⟨fun h => ⟨h.antitone, h.chamber, h.rightCont, h.cont, h.deletion⟩,
    fun h => ⟨h.antitone, h.chamber, h.rightCont, h.cont, h.deletion⟩⟩

theorem dfa_isBoundaryDualProcess_iff_diffusion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ) {p : ℕ}
    (x y : Fin p → ℝ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) :
    IsBoundaryDualProcess P 𝓖 D0 x y N X Y ↔ IsDkBoundaryDualProcess P 𝓖 D0 x y N X Y :=
  ⟨fun h => ⟨h.prob, h.adapted, h.start,
      h.paths.mono fun _ hp => ⟨hp.antitone, hp.chamber, hp.rightCont, hp.cont, hp.deletion⟩,
      h.martingale⟩,
    fun h => ⟨h.prob, h.adapted, h.start,
      h.paths.mono fun _ hp => ⟨hp.antitone, hp.chamber, hp.rightCont, hp.cont, hp.deletion⟩,
      h.martingale⟩⟩

theorem dfa_isBaseBridge_iff_diffusion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (z : ℝ × ℝ) (t : ℝ) (Z : ℝ → Ω → ℝ × ℝ) :
    IsBaseBridge P p z t Z ↔ IsBrBaseBridge P p z t Z :=
  ⟨fun h => ⟨h.prob, h.meas, h.paths, h.fdd⟩, fun h => ⟨h.prob, h.meas, h.paths, h.fdd⟩⟩

/-!
### The seven input propositions
-/

theorem dfa_lbkBaseExistence_iff_diffusion (D0 : ℝ) :
    LbkBaseExistence D0 ↔ ∀ z ∈ exBaseStrip, HasExBaseDiffusion D0 z :=
  ⟨fun h z hz => (dfa_hasBaseDiffusion_iff_diffusion D0 z).1 (h z hz),
    fun h z hz => (dfa_hasBaseDiffusion_iff_diffusion D0 z).2 (h z hz)⟩

theorem dfa_lbkBaseTransitionLaw_iff_diffusion (D0 : ℝ) :
    LbkBaseTransitionLaw D0 ↔ ExLbkBaseTransitionLaw D0 :=
  ⟨fun h t ht z hz Ω m 𝓖 P Z hZ =>
      h t ht z hz Ω m 𝓖 P Z ⟨hZ.prob, hZ.adapted, hZ.start, hZ.paths, hZ.martingale⟩,
    fun h t ht z hz Ω m 𝓖 P Z hZ =>
      h t ht z hz Ω m 𝓖 P Z ⟨hZ.prob, hZ.adapted, hZ.start, hZ.paths, hZ.martingale⟩⟩

theorem dfa_lbkCornerCKX_iff_diffusion (D0 : ℝ) : LbkCornerCKX D0 ↔ ExLbkCornerCKX D0 := Iff.rfl

theorem dfa_lbkCornerHeatIdentity_iff_diffusion (D0 : ℝ) :
    LbkCornerHeatIdentity D0 ↔ ChLbkCornerHeatIdentity D0 := Iff.rfl

theorem dfa_lbkDoobKilledLaw_iff_diffusion (D0 : ℝ) :
    LbkDoobKilledLaw D0 ↔ DkLbkDoobKilledLaw D0 :=
  ⟨fun h x y hz Ω m 𝓖 P N X Y hP =>
      h x y hz Ω m 𝓖 P N X Y ((dfa_isBoundaryDualProcess_iff_diffusion P 𝓖 D0 _ _ N X Y).2 hP),
    fun h x y hz Ω m 𝓖 P N X Y hP =>
      h x y hz Ω m 𝓖 P N X Y ((dfa_isBoundaryDualProcess_iff_diffusion P 𝓖 D0 _ _ N X Y).1 hP)⟩

theorem dfa_lbkBridgeExistence_iff_diffusion (D0 : ℝ) :
    LbkBridgeExistence D0 ↔ BrLbkBridgeExistence D0 :=
  ⟨fun h x y hz t ht => by
      obtain ⟨Ω, mΩ, P, Z, hZ⟩ := h x y hz t ht
      exact ⟨Ω, mΩ, P, Z, ⟨hZ.prob, hZ.meas, hZ.paths, hZ.fdd⟩⟩,
    fun h x y hz t ht => by
      obtain ⟨Ω, mΩ, P, Z, hZ⟩ := h x y hz t ht
      exact ⟨Ω, mΩ, P, Z, ⟨hZ.prob, hZ.meas, hZ.paths, hZ.fdd⟩⟩⟩

theorem dfa_lbkHypRadialGaussCompare_iff_diffusion :
    LbkHypRadialGaussCompare ↔ GcLbkHypRadialGaussCompare := Iff.rfl

end BlockBand.Endpoints
