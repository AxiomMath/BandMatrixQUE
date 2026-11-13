module

public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The fractional transmission bound, uniformly on a compact bulk set

`FractionalTransmissionUniform` is the form of the fractional transmission bound used for
`CurrentNuclearTail`: the exponent `p = 1/2` only, the time `j₀ = ⌊εW⌋` only, and the `limsup` in
`W` of the supremum over `E ∈ bulkInterval κI` (the maximal inequality bounds
`sup_E P{sup_j Tr H_j > K}` by `(c/K) sup_E E Tr H_{j₀}` plus an exit probability that tends to
zero, so a `limsup` of `sup_E` suffices; no bound at every large `W` is needed).

The fixed-energy bound `TransmissionLawContract.fractional` does not give this form: its constant
`C_p = C_p(b, E)` is chosen after `E`, and the `limsup` is taken at that fixed `E`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open scoped ENNReal

/-- **The fractional transmission bound at `p = 1/2`, uniformly on a compact bulk set.**
`b`, the bulk margin `κI` and the time `ε > 0` first, then `C`:
`limsup_W sup_{E ∈ bulkInterval κI} E Tr T_{⌊εW⌋}^{1/2} ≤ C`, for the unabsorbed (`κ ≡ 0`)
near-end-grown path `growthPathLaw W b`, `T_r = pathTransmission b E 0 W r`, `Tr T^{1/2} =
fracTrace (1/2) T`. -/
def FractionalTransmissionUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, limsup (fun W : ℕ => ⨆ (E : ℝ) (_ : E ∈ bulkInterval κI),
        ∫⁻ ω, ENNReal.ofReal
          (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * ε⌋₊ ω))
          ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal C

end BlockBand.SourceProcess.FullSourceStops
