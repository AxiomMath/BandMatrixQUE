module

public import BlockBand.Internal.Contracts.TransmissionUniform2

/-!
# The full-source covariance lemma, energy-uniform: reduction to `Δ`-covariances

By the almost-sure Ward identity `𝓔 = ι(ΔF) + (ΔF)*ι*` (`FullSource.ward_full`), with
`ι* = nearSel W`, `F = ι*(ℝ - c₀)` (`FullSource.wardF`) and `Δ = K𝒢₁₁K - K` the one-port
`freshDelta` at the far-eliminated `X = nearSchur z 𝕏`, one has, for the centered parts,
`v*𝓔⁰w = (ι*v)*Δ⁰(Fw) + conj((ι*w)*Δ⁰(Fv))`. The covariance of `𝓔` is therefore a sum of four
`Δ`-covariances: two of equal sign (`E[ΔΔ]`, `conj E[ΔΔ]`) and two of opposite sign
(`E[ΔΔ̄]`). They are computed through the weighted resolvent tensor with the outside weights
`U_± = V_± = K, K*`, then `KM = I + O(δ₀)`, `σ₊₊ = σ₋ + O(δ₀+δ₁+g/W)`,
`σ₋₊ = σ₊ + O(δ₀+g/W)`. The assembly uses `ιF = -c₀ P𝕊`, `F*F = P'/(4η²)`, `c₀² = -1/(4η²)` and
`σ₊ = 2η²D₀`.

The two one-port statements below are stated for **every passive** `X` (`Y = -Im X ⪰ 0`; the
far-eliminated input is passive by `FullSource.nearSchur_passive`), uniformly on `bulkInterval κI`,
with the error `C[W⁻² + W⁻¹(δ₀ + δ₁ + g/W)]‖x‖‖y‖‖x'‖‖y'‖`, `g = Tr T(X)`. (The opposite-sign
clause also holds without `δ₁`; the weaker form stated here suffices.)

* `DeltaCovarianceSame`: `E[(x*Δ⁰y)(x'*Δ⁰y')] = (σ₋/W)(x*y')(x'*y) + error`.
* `DeltaCovarianceOpposite`: `E[(x*Δ⁰y)·conj(x'*Δ⁰y')] = (σ₊/W)(x*x')(y'*y) + error`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexConjugate ComplexOrder

/-- The opposite-sign bilinear covariance `E[(x*U⁰y)·conj(x'*U⁰y')]`, `U⁰ = U - EU`. -/
def bilinearCrossCovariance {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] (μ : Measure Ω)
    (U : Ω → Matrix n n ℂ) (x y x' y' : n → ℂ) : ℂ :=
  ∫ ω, bilinear x (U ω - matrixExpect μ U) y *
    star (bilinear x' (U ω - matrixExpect μ U) y') ∂μ

/-- The error scale `W⁻² + W⁻¹(δ₀ + δ₁ + g/W)` of the full-source covariance lemma at `X`. -/
def covErr {W : ℕ} (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X +
    conductanceOf (passiveTransmission b E X) / W)

/-- **Equal-sign `Δ`-covariance** (`β = α = +`: the weighted resolvent tensor with
`U₊ = V₊ = K`, then `KM² K = I + O(δ₀)` and
`σ₊₊ = σ₋ + O(δ₀ + δ₁ + g/W)`). `b`, the bulk margin `κI`, then `C, W₀`; for `W ≥ W₀`, every
`E ∈ bulkInterval κI`, every stationary jet `s` at `E`, every passive `X` and all vectors:
`|E[(x*Δ⁰y)(x'*Δ⁰y')] - (σ₋/W)(x*y')(x'*y)| ≤ C[W⁻² + W⁻¹(δ₀+δ₁+g/W)]‖x‖‖y‖‖x'‖‖y'‖`. -/
def DeltaCovarianceSame : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ x y x' y' : Fin W → ℂ,
        ‖bilinearCovariance (freshLaw W b) (freshDelta b E X) x y x' y' -
            sigmaMinus b E s / W * crossedTensor x y x' y' 1 1‖ ≤
          C * covErr b E s X * fourNorm x y x' y'

/-- **Opposite-sign `Δ`-covariance** (`β = -`, `α = +`; outside
weights `KMM*K* = I + O(δ₀)`, `σ₋₊ = σ₊ + O(δ₀ + g/W)`). Same quantifiers as
`DeltaCovarianceSame`:
`|E[(x*Δ⁰y)·conj(x'*Δ⁰y')] - (σ₊/W)(x*x')(y'*y)| ≤ C[W⁻² + W⁻¹(δ₀+δ₁+g/W)]‖x‖‖y‖‖x'‖‖y'‖`. -/
def DeltaCovarianceOpposite : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ x y x' y' : Fin W → ℂ,
        ‖bilinearCrossCovariance (freshLaw W b) (freshDelta b E X) x y x' y' -
            ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear x 1 x' * bilinear y' 1 y)‖ ≤
          C * covErr b E s X * fourNorm x y x' y'

end BlockBand.SourceProcess.FullSourceCovariance
