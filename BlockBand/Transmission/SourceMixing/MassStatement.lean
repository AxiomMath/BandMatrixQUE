module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The mass moment bound along the unabsorbed path (statement only)

`MassMomentBound b E`: for every `p ≥ 1` there is `K ≥ 0` (chosen before the total length `T`)
such that for every `T` there is `W₀` with `‖q_r‖_{L^p} ≤ K(1 + W/r)` for `W ≥ W₀` and
`1 ≤ r ≤ TW`, where `q_r = Tr Q_r = passiveMass b E (pathX b E W r)` under `growthPathLaw W b`.
Since `g_r = 4η q_r`, this is the `T`-free master bound `E g_r^p ≤ C(1 + (W/r)^p)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- **The `T`-free mass moment bound** at fixed `b, E`. -/
def MassMomentBound (b E : ℝ) : Prop :=
  ∀ p : ℝ, 1 ≤ p → ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ r : ℕ, 1 ≤ r →
    (r : ℝ) ≤ T * W →
      eLpNorm (fun ω => passiveMass b E (pathX b E W r ω)) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal (K * (1 + W / r))

end BlockBand.Transmission.SourceMixing
