module

public import BlockBand.SourceProcess.ContractingWords.SlotMom

/-!
# The projected separator and the injection at one fresh layer

Each is a statement at one fresh layer (`freshLaw W b`),
deterministic Hermitian old two-port `𝕏`, `X = nearSchur z 𝕏`, `δ₀ = jetDistance0`,
`δ₁ = jetDistance1` (stationary jet `s`), `g = conductanceOf T(X)`, bulk-uniform: `C, W₀` from
`b, κ` only, for `W ≥ W₀`, `E ∈ bulkInterval κ`, every Hermitian `𝕏` and all vectors.

`projGamma = P(NN*)P - NPN*`. From the block form `N = [[L, C_N],[0, I]]`, `C_N = Δℝ₁₂`, this is
`diag(C_NC_N*, 0)` (so `NPN* = P + P𝓔P - diag(C_NC_N*, 0)`); it is defined here
through `transportedSep` only.
* `ProjGammaMean`: `‖E projGamma - (D₀g/2W)P‖ ≤ C{δ₀² + gW⁻² + (g/W)(δ₀+δ₁+g/W)}`;
* `ProjGammaFluct` (`p = 2`): `E|u*(projGamma)⁰v|² ≤ (C(g/W + δ₀√(g/W))‖u‖‖v‖)²`;
* `InjNearMean`: `|W⁻¹E Tr(D₊*D₊P) - d_*| ≤ C(δ₀ + g/W)` (`t₂ = W⁻¹E Tr𝒢₁₂*𝒢₁₂`);
* `InjFarTrace`: `|E Tr(D₊*D₊(I - P))| ≤ Cg` (the far part of `C_+`).

`ProjGammaMean`, `ProjGammaFluct` and `InjFarTrace` are proved as
`ProjSeparator.projGammaMean_holds`, `ProjSeparator.projGammaFluct_holds` and
`ProjSeparator.injFarTrace_holds`; `InjNearMean` is a hypothesis here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.Bridge
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `P(NN*)P - NPN* = diag(C_NC_N*, 0)`. -/
def projGamma (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (y : LayerSample W .oneBlockOnePort) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  nearProjection W * transportedSep b E XX .id y * nearProjection W - transportedSep b E XX .proj y

/-- `E C_NC_N* = (D₀g/2W)I + R` (proved as `ProjSeparator.projGammaMean_holds`). -/
def ProjGammaMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s →
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        let X := nearSchur (boundaryZ b E) XX
        let g := conductanceOf (passiveTransmission b E X)
        ‖matrixExpect (freshLaw W b) (projGamma b E XX) -
            ((transportD0 b E * g / (2 * W) : ℝ) : ℂ) • nearProjection W‖ ≤
          C * (jetDistance0 b E X ^ 2 + g * ((W : ℝ)⁻¹) ^ 2 +
            g / W * (jetDistance0 b E X + jetDistance1 b E s X + g / W))

/-- The centered quadratic expression, at `p = 2` (proved as
`ProjSeparator.projGammaFluct_holds`). -/
def ProjGammaFluct : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ u v : Fin 2 × Fin W → ℂ,
        let X := nearSchur (boundaryZ b E) XX
        let g := conductanceOf (passiveTransmission b E X)
        ∫ y, ‖bilinear u (projGamma b E XX y -
            matrixExpect (freshLaw W b) (projGamma b E XX)) v‖ ^ 2 ∂freshLaw W b ≤
          (C * (g / W + jetDistance0 b E X * Real.sqrt (g / W)) * vecNorm u * vecNorm v) ^ 2

/-- **Hypothesis**: the near injected trace `t₂ = d_* + O(δ₀ + g/W)`. -/
def InjNearMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        let X := nearSchur (boundaryZ b E) XX
        ‖(W : ℂ)⁻¹ * ∫ y, ((freshD b E XX y)ᴴ * freshD b E XX y * nearProjection W).trace
            ∂freshLaw W b - (dStar b : ℂ)‖ ≤
          C * (jetDistance0 b E X + conductanceOf (passiveTransmission b E X) / W)

/-- The far injected trace is `O(g)` (proved as `ProjSeparator.injFarTrace_holds`). -/
def InjFarTrace : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        ‖∫ y, ((freshD b E XX y)ᴴ * freshD b E XX y * (1 - nearProjection W)).trace
            ∂freshLaw W b‖ ≤
          C * conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))

end BlockBand.SourceProcess.ContractingWords
