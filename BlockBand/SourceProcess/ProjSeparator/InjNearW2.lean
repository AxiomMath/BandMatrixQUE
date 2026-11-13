module

public import BlockBand.SourceProcess.ContractingWords.SlotPins

/-!
# The near injected trace with its `W⁻²` term

`InjNearMeanW2` is `ContractingWords.InjNearMean` with an added `W⁻²` term in the error;
`injNearMeanW2_of_injNearMean` shows that it is weaker.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.ContractingWords
open scoped ENNReal Matrix.Norms.L2Operator

/-- **The near injected trace**, with the `W⁻²` term:
`|W⁻¹E Tr(D*DP) − d_*| ≤ C(δ₀ + g/W + W⁻²)`. This is `ContractingWords.InjNearMean` with the added
`W⁻²`. -/
def InjNearMeanW2 : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        let X := nearSchur (boundaryZ b E) XX
        ‖(W : ℂ)⁻¹ * ∫ y, ((freshD b E XX y)ᴴ * freshD b E XX y * nearProjection W).trace
            ∂freshLaw W b - (dStar b : ℂ)‖ ≤
          C * (jetDistance0 b E X + conductanceOf (passiveTransmission b E X) / W + (W : ℝ)⁻¹ ^ 2)

/-- `InjNearMean` implies `InjNearMeanW2` (it is stronger). -/
theorem injNearMeanW2_of_injNearMean (h : InjNearMean) : InjNearMeanW2 := by
  intro b hb0 hb κ hκ
  obtain ⟨C, W₀, hC, hW⟩ := h b hb0 hb κ hκ
  refine ⟨C, W₀, hC, fun W hW' E hE XX hXX => ?_⟩
  refine (hW W hW' E hE XX hXX).trans ?_
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hC

end BlockBand.SourceProcess.ProjSeparator
