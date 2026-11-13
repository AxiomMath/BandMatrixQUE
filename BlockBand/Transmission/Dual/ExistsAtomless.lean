module

public import BlockBand.Transmission.Dual.ExistsOne

/-!
# Atomlessness of the level-one lifetime, as a statement

States `DualLifetimeAtomlessOne`: for `p = 1`, the extinction time of every dual deletion
process has no atoms.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

/-- For `p = 1` and `D₀ > 0`, the extinction time of every dual deletion process is atomless:
`P(ζ = u) = 0` for every `u ≥ 0`. -/
def DualLifetimeAtomlessOne : Prop :=
  ∀ D0 : ℝ, 0 < D0 → ∀ (x y : Fin 1 → ℝ), IsRatioParameter x y →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsDualDeletionProcess P 𝓖 D0 x y N X Y →
      ∀ u : ℝ≥0, P {ω | dualExtinction N ω = (u : ℝ≥0∞)} = 0

end BlockBand.Transmission.Dual.Exists
