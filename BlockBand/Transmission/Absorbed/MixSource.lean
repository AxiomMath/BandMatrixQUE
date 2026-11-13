module

public import BlockBand.Transmission.Absorbed.DeltaUniform

/-!
# Absorbed source mixing

**`AbsorbedSourceMixingBulk`**: the absorbed analogue of `Generator.PassiveSourceMixingBulk`
(proved at `κ ≡ 0` as `SourceMixingBulk.passiveSourceMixingBulk_holds`), along the absorbed path
`pathNearSchur b E κ W r`: `‖Tr(Q f)‖_p + ‖hs(Q,f)‖_p ≤ C/√W` on `εW ≤ r ≤ TW`, uniformly on
the bulk, for every admissible profile `κ`.

Why it is needed: the `κ ≠ 0` one-layer drift of `F_z` contains the source atoms
`τ = ‖Tr(Tf)‖ + √g·hs(T,f)` at the absorbed input (`wmErr`'s `e‖Tr(Gf)‖`, the `σff` terms of
the passive covariance bound). The crude bound `|Tr(Gf)| ≤ Cq` gives `O(g/W)` per step, which
sums to `O(T)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers

/-- **Absorbed source mixing** (`PassiveSourceMixingBulk` along the absorbed path). -/
def AbsorbedSourceMixingBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI ε T p : ℝ, 0 < κI → 0 < ε → ε < T → 1 ≤ p →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => (passiveQ b E (pathNearSchur b E κ W r ω) *
            passiveF b E (pathNearSchur b E κ W r ω)).trace) (ENNReal.ofReal p)
            (growthPathLaw W b) +
          eLpNorm (fun ω => hsSandwich (passiveQ b E (pathNearSchur b E κ W r ω))
            (passiveF b E (pathNearSchur b E κ W r ω))) (ENNReal.ofReal p) (growthPathLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W)

end BlockBand.Transmission.Absorbed
