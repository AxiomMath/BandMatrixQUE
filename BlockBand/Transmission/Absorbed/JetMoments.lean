module

public import BlockBand.Transmission.Absorbed.DeltaUniform

/-!
# Absorbed jet-distance moments

`AbsorbedJetMoments`: length-uniform `L^p` bounds on the jet distances `δ₀`, `δ₁` along the
absorbed path, with the constant chosen before the total length.

Why it is needed: the `κ ≠ 0` one-layer drift of `F_z` uses the passive covariance bound and
`ubarMean_bulk` at the absorbed input; their errors contain `δ₀` and `δ₁`
(through `ε = C(W⁻² + W⁻¹(δ₀ + δ₁ + q/W))` and `wmErr`). A crude bound gives `O(1/W)` per step,
which does not sum. `absorbedDeltaUniform_holds` covers only `δ₀`, in its own form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.PassiveCovariance

/-- **Absorbed jet-distance moments** (the `.jet` bound along the absorbed path). -/
def AbsorbedJetMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI ε p : ℝ, 0 < κI → 0 < ε → 1 ≤ p →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => jetDistance0 b E (pathNearSchur b E κ W r ω)) (ENNReal.ofReal p)
            (growthPathLaw W b) +
          eLpNorm (fun ω => jetDistance1 b E s (pathNearSchur b E κ W r ω)) (ENNReal.ofReal p)
            (growthPathLaw W b) ≤
          ENNReal.ofReal (C / W)

end BlockBand.Transmission.Absorbed
