module

public import BlockBand.Transmission.PathScalar.Exit

/-!
# `PassiveInitialScalarContract` from the matched traces and the absorbed clause

`passiveInitialScalar_of_absorbed`: the `moment` and `exit` fields follow from
`MatchedTracesContract`; the `absorbedMoment` field is the hypothesis `AbsorbedMomentClause`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- The `absorbedMoment` field of `PassiveInitialScalarContract`: deterministic absorptions
`ε_i ∈ [0, K/W²]` on the path positions give `‖δ₀‖_p ≤ C/W` for the absorbed path of length
`r ≤ TW`, uniformly for `E ∈ bulkInterval κ`. -/
def AbsorbedMomentClause : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T K p : ℝ, 0 < κ → 0 ≤ K → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ T * W → ∀ ε : Fin r → ℝ, (∀ i, 0 ≤ ε i ∧ ε i ≤ K / (W : ℝ) ^ 2) →
        eLpNorm (fun ω => jetDistance0 b E
            (nearSchur (boundaryZ b E) (absorbedPathSchur E ε (pathAt W r ω))))
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal (C / W)

/-- **`PassiveInitialScalarContract`, conditional assembly**: `moment` and `exit` from
`MatchedTracesContract`, and `absorbedMoment` from the hypothesis `AbsorbedMomentClause`. -/
theorem passiveInitialScalar_of_absorbed (hMT : MatchedTracesContract)
    (habs : AbsorbedMomentClause) : PassiveInitialScalarContract where
  moment := passiveInitialScalar_moment hMT
  exit := passiveInitialScalar_exit hMT
  absorbedMoment := habs

end BlockBand.Transmission.PathScalar
