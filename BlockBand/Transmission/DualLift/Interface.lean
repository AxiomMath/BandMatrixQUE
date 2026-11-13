module

public import BlockBand.Transmission.DualLift.Flat
public import BlockBand.Transmission.Dual.UniqueLevel
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# Statements about the lift

Definitions only.
* `LiftEntrance D₀` (instantaneous entrance and no return): for every admissible random start
  and every lifted family, almost surely the flat path is in the open chamber `𝒞₁` at every
  time `t ∈ (0, e_n]` (instantaneous entrance at the faces `x = 0`, `y = 0`, `y = 1`, and no
  return). For starts in `𝒞₁` it also covers `t = 0`. It follows from the characteristics of
  `x`, `y`, `1 − y` along `LiftFamily.Yf` (`isCSM_Yf`).
* `LiftBoundaryDual D₀`: every boundary start of one pair has a realization of the boundary
  class `IsBoundaryDualProcess` on the driver space `LΩ Unit` with the augmented
  filtration. With `HasBoundaryDualProcess` it gives the contract field `exists_`.
* `LiftDualDeletionInterior D₀`: the same realization from an interior start is an
  `IsDualDeletionProcess`.
* `LiftIsDualFrom D₀`: for an augmented-`𝓕₀` random start `Z ∈ 𝒞₁` on `LΩ S`, there is a
  realization in the class `IsDualFrom` at level `1` that starts at `Z` at every `ω` (an input
  of `DualUniqueAt`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionUniform BlockBand.Transmission.Dual
open scoped NNReal

/-- **Instantaneous entrance and no return for the lift**: almost surely the flat path of every
lifted family is in the open chamber `𝒞₁` at every time `t ∈ (0, e_n]`. -/
def LiftEntrance (D0 : ℝ) : Prop :=
  ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (ξ : LΩ S → Fin 6 → ℝ), IsLiftStart μ ξ → ∀ F : LiftFamily μ D0 ξ,
    ∀ᵐ ω ∂LP μ, ∀ n : ℕ, ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) ≤ F.e n ω →
      F.Zp n t ω ∈ flatChamber 1

/-- **Boundary-start realizations on the driver space `LΩ Unit`.** -/
def LiftBoundaryDual (D0 : ℝ) : Prop :=
  ∀ x y : ℝ, IsDualStart ![x] ![y] →
    ∃ (N : ℝ≥0 → LΩ Unit → ℕ) (X Y : ℝ≥0 → LΩ Unit → ℕ → ℝ),
      IsBoundaryDualProcess (LP (Measure.dirac ())) (L𝓖 (Measure.dirac ())) D0 ![x] ![y] N X Y

/-- **Interior-start realizations are deletion processes**: every interior start has a
realization in the class `IsDualDeletionProcess` on `LΩ Unit`. -/
def LiftDualDeletionInterior (D0 : ℝ) : Prop :=
  ∀ x y : ℝ, IsRatioParameter ![x] ![y] →
    ∃ (N : ℝ≥0 → LΩ Unit → ℕ) (X Y : ℝ≥0 → LΩ Unit → ℕ → ℝ),
      IsDualDeletionProcess (LP (Measure.dirac ())) (L𝓖 (Measure.dirac ())) D0 ![x] ![y] N X Y

/-- **Random interior starts give the class `IsDualFrom` at level one.** -/
def LiftIsDualFrom (D0 : ℝ) : Prop :=
  ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (Z : LΩ S → Fin 2 → ℝ), Measurable[L𝓖 μ 0] Z → (∀ ω, Z ω ∈ flatChamber 1) →
    ∃ (N : ℝ≥0 → LΩ S → ℕ) (X Y : ℝ≥0 → LΩ S → ℕ → ℝ),
      IsDualFrom (LP μ) (L𝓖 μ) D0 1 N X Y ∧
        ∀ ω, N 0 ω = 1 ∧ X 0 ω 0 = Z ω 0 ∧ Y 0 ω 0 = Z ω 1

/-- `LiftBoundaryDual` gives the contract field `exists_`. -/
theorem hasBoundaryDualProcess_of_lift {D0 : ℝ} (h : LiftBoundaryDual D0) {x y : ℝ}
    (hxy : IsDualStart ![x] ![y]) : HasBoundaryDualProcess D0 ![x] ![y] := by
  obtain ⟨N, X, Y, hP⟩ := h x y hxy
  exact ⟨LΩ Unit, inferInstance, L𝓖 (Measure.dirac ()), LP (Measure.dirac ()), N, X, Y, hP⟩

end BlockBand.Transmission.DualLift
