module

public import BlockBand.Transmission.DualLift.LOneMart
public import BlockBand.Transmission.DualLift.Interface

/-!
# Assembly: boundary and interior realizations from instantaneous entrance

Conditional on the named statement `LiftEntrance D₀` only.
* **`liftBoundaryDual_of_entrance`**: `LiftEntrance D₀ → LiftBoundaryDual D₀` (`D₀ > 0`): at
  every boundary start `IsDualStart ![x] ![y]`, the realization `(N₂, X₂, Y₂)` of the lifted
  family from `ξ ≡ liftSection x y` on `LΩ Unit` is an `IsBoundaryDualProcess`.
* **`exists_of_entrance`**: hence the contract field `exists_` of `DualBoundaryStartContract`,
  conditional on `LiftEntrance`.
* **`liftDualDeletionInterior_of_entrance`**: at interior starts the same realization is an
  `IsDualDeletionProcess`. This also needs `LiftEntrance`, for "no return" to the faces: the
  lifted path started in `𝒞₁` is not confined to `𝒞₁` by construction.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionUniform BlockBand.Transmission.Dual
  BlockBand.Transmission.Dual.Exists
open scoped NNReal

variable {D0 : ℝ}

/-- The deterministic start `σ(x, y)` on `LΩ Unit`. -/
def sectionStart (x y : ℝ) : LΩ Unit → Fin 6 → ℝ := fun _ => liftSection x y

theorem isLiftStart_section {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hxy : 0 < x + y) : IsLiftStart (Measure.dirac ()) (sectionStart x y) :=
  ⟨stronglyMeasurable_const, fun _ => liftSection_mem hx hy0 hy1 hxy⟩

theorem start_values {x y : ℝ} (F : LiftFamily (Measure.dirac ()) D0 (sectionStart x y))
    (hx : 0 ≤ x) (ω : LΩ Unit) (i : Fin 1) :
    F.X₂ 0 ω i = ![x] i ∧ F.Y₂ 0 ω i = ![y] i := by
  have h := F.Z₂_zero ω
  simp only [sectionStart, liftProj_liftSection hx] at h
  have hi := Fin.fin_one_eq_zero i; subst hi
  simp [LiftFamily.X₂, LiftFamily.Y₂, h]

/-- **Boundary starts**: `LiftEntrance` gives realizations in the boundary class
`IsBoundaryDualProcess`. -/
theorem liftBoundaryDual_of_entrance (hD0 : 0 < D0) (hL : LiftEntrance D0) :
    LiftBoundaryDual D0 := by
  intro x y hxy
  have hx : 0 ≤ x := hxy.2.2.1 0
  have hy := hxy.2.2.2.1 0
  have hs : 0 < x + y := hxy.2.2.2.2 0 0
  have hξ := isLiftStart_section hx hy.1 hy.2 hs
  obtain ⟨F⟩ := nonempty_liftFamily hD0 hξ
  refine ⟨F.N₂, F.X₂, F.Y₂,
    { prob := inferInstance
      adapted := F.adapted₂ hD0 hξ
      start := Eventually.of_forall fun ω => ⟨F.N₂_zero ω, fun i => start_values F hx ω i⟩
      paths := ?_
      martingale := fun q hq hq1 f hf hfc hfs => ?_ }⟩
  · filter_upwards [F.ae_good₂ hD0 hξ, hL Unit (Measure.dirac ()) _ hξ F] with ω h1 h2
    exact F.isBoundaryDeletionPath_N₂ hξ h1 h2
  · obtain rfl : q = 1 := le_antisymm hq1 hq
    exact F.martingale_dualMartingale₂ hD0 hξ hf hfc hfs

/-- **`exists_` of `DualBoundaryStartContract`**, assuming `LiftEntrance` for every `D₀ > 0`. -/
theorem exists_of_entrance (hL : ∀ D0 : ℝ, 0 < D0 → LiftEntrance D0) :
    ∀ D0 : ℝ, 0 < D0 → ∀ x y : ℝ, IsDualStart ![x] ![y] → HasBoundaryDualProcess D0 ![x] ![y] :=
  fun D0 hD0 _ _ hxy => hasBoundaryDualProcess_of_lift (liftBoundaryDual_of_entrance hD0
    (hL D0 hD0)) hxy

/-- **Interior starts**: `LiftEntrance` gives realizations in the deletion class
`IsDualDeletionProcess`. -/
theorem liftDualDeletionInterior_of_entrance (hD0 : 0 < D0) (hL : LiftEntrance D0) :
    LiftDualDeletionInterior D0 := by
  intro x y hxy
  have hx : 0 ≤ x := (hxy.2.2.1 0).le
  have hy := hxy.2.2.2 0
  have hξ := isLiftStart_section hx hy.1.le hy.2.le (by simp at hy ⊢; linarith [hxy.2.2.1 0])
  obtain ⟨F⟩ := nonempty_liftFamily hD0 hξ
  have h0 : ∀ ω, liftProj (sectionStart x y ω) ∈ flatChamber 1 := fun ω => by
    rw [sectionStart, liftProj_liftSection hx]
    simpa using flat_mem_of_ratio hxy
  refine ⟨F.N₂, F.X₂, F.Y₂,
    { prob := inferInstance
      adapted := F.adapted₂ hD0 hξ
      start := Eventually.of_forall fun ω => ⟨F.N₂_zero ω, fun i => start_values F hx ω i⟩
      paths := ?_
      martingale := fun q hq hq1 f hf hfc hfs => ?_ }⟩
  · filter_upwards [F.ae_good₂ hD0 hξ, hL Unit (Measure.dirac ()) _ hξ F] with ω h1 h2
    exact F.isDeletionPath_N₂ hξ h1 h2 (h0 ω)
  · obtain rfl : q = 1 := le_antisymm hq1 hq
    exact F.martingale_dualMartingale₂ hD0 hξ hf hfc hfs

end BlockBand.Transmission.DualLift
