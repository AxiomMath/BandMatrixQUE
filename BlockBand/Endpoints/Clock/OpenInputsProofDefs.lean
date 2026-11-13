module

public import BlockBand.Endpoints.Clock.OpenInputsPath

/-!
# The open-inputs lemma: intermediate statements of the clock steps

This file defines two intermediate statements of the clock-moment part of the proof of the
open-inputs lemma; both are proved (`onePortWeighted_of`, `clockStep_of`) and neither is a
hypothesis of `openInputsMoments_of`.
* `clockT b E X Y ω = W⁻¹ Re Tr(L*YL)`, `L = freshL b E X ω` (one fresh one-port layer);
  `clockU Y = W⁻¹ Re Tr Y`; `nextClockU b E w X Y ω = W⁻¹ Re Tr(w C₊ + L*YL)` is the next
  normalized clock `u₊` with injection weight `w = q((j+1)/W)` (`oneEndedY`).
* `OnePortWeighted`: the clauses `clockMean`, `clockNoise`, `unrestricted` of
  `WeightedLayerContract` (the weighted-layer lemma), read for one block with one port, with the
  one-block scalar distance `δ₀(X) = jetDistance0 b E X` in place of `d(X)`.
* `ClockStepBound`: the conditional moment step at integer order `P ≥ 2`: the crude unrestricted
  bound `E(u₊^P | X, Y) ≤ C(u^P + 1)` (every Hermitian `X`) and, on the scalar domain
  `δ₀(X) ≤ r₁`, the weighted bound
  `E((1 + Kδ₀(X₊)) u₊^P | X, Y) ≤ (1 + C/W)(1 + Kδ₀(X)) u^P + C(u^{P-1} + 1)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix ComplexOrder

namespace OpenInputsProof

/-- `W⁻¹ Re Tr(L*YL)` for one fresh one-port layer, `L = (z - X)𝒢₁₂`. -/
def clockT (b E : ℝ) {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) : ℝ :=
  (W : ℝ)⁻¹ * ((freshL b E X ω)ᴴ * Y * freshL b E X ω).trace.re

/-- The normalized clock `u = W⁻¹ Re Tr Y`. -/
def clockU {W : ℕ} (Y : Matrix (Fin W) (Fin W) ℂ) : ℝ := (W : ℝ)⁻¹ * Y.trace.re

/-- The next normalized clock `u₊ = W⁻¹ Re Tr(w C₊ + L*YL)` (`oneEndedY`, weight `w`). -/
def nextClockU (b E w : ℝ) {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    ℝ :=
  (W : ℝ)⁻¹ * (((w : ℂ) • freshC b E X ω) + (freshL b E X ω)ᴴ * Y * freshL b E X ω).trace.re

/-- **The weighted-layer lemma for one block with one port** (`clockMean`, `clockNoise`,
`unrestricted`); proved as `onePortWeighted_of` from `WeightedLayerContract` and
`GaussianAbsorptionContract`.
-/
def OnePortWeighted : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    (∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
        jetDistance0 b E X ≤ dstar → ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef →
          Integrable (clockT b E X Y) (freshLaw W b) ∧
          ∫ ω, clockT b E X Y ω ∂freshLaw W b ≤
            (1 + C * jetDistance0 b E X + C / (W : ℝ) ^ 2) * clockU Y) ∧
    ∀ p : ℝ, 1 ≤ p → ∃ (Cp : ℝ) (W₀ : ℕ), ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
        ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef →
          eLpNorm (fun ω => clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b)
              (ENNReal.ofReal p) (freshLaw W b) ≤
            ENNReal.ofReal (Cp * clockU Y / Real.sqrt W) ∧
          eLpNorm (clockT b E X Y) (ENNReal.ofReal p) (freshLaw W b) ≤
            ENNReal.ofReal (Cp * clockU Y)

/-- **The conditional clock-moment step** of the open-inputs lemma at integer order `P ≥ 2`, for
injection weights `0 ≤ w ≤ K_q`; proved as `clockStep_of`. -/
def ClockStepBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ Kq : ℝ, 0 ≤ Kq →
    ∀ P : ℕ, 2 ≤ P →
      (∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, 0 < W → W₀ ≤ W →
        ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
        ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
          ∫⁻ ω, ENNReal.ofReal (nextClockU b E w X Y ω ^ P) ∂freshLaw W b ≤
            ENNReal.ofReal (C * (clockU Y ^ P + 1))) ∧
      ∃ (r₁ K C : ℝ) (W₀ : ℕ), 0 < r₁ ∧ 0 ≤ K ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
        ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → jetDistance0 b E X ≤ r₁ →
        ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
          ∫⁻ ω, ENNReal.ofReal ((1 + K * jetDistance0 b E (freshSchur E X ω)) *
              nextClockU b E w X Y ω ^ P) ∂freshLaw W b ≤
            ENNReal.ofReal ((1 + C / W) * (1 + K * jetDistance0 b E X) * clockU Y ^ P +
              C * (clockU Y ^ (P - 1) + 1))

end OpenInputsProof

end BlockBand.Endpoints.Clock
