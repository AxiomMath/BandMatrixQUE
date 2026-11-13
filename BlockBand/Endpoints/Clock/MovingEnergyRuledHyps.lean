module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# Hypotheses of the moving-energy clock chain

The moving-energy chain takes two statements as explicit hypotheses.

## `PassiveCovarianceEnergyUniformHyp`

The conclusion of `TransmissionStatements.PassiveCovarianceContract` with `κ` before `∃ C W₀` and
`∀ E ∈ bulkInterval κ, ∀ s` after them. Jet existence (the first conjunct of the contract) is not
restated.

## `LayersBUniformHyp`

Each field is the corresponding contract field with `b` replaced by `∀ β, 0 < β → β < 1/4 → …`
before the constants, and `∀ b ∈ Set.Icc β (1/2 - β)` right after them; the body after the
constants is unchanged.
* `gaussianAbsorption`: `GaussianAbsorptionContract`.
* `traceMatrixFluctuation`: `TraceMatrixContract.fluctuation`.
* `weightedLayerClockMean`: `WeightedLayerContract.clockMean`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock.MovingEnergy

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

/-- **The passive covariance bound, uniformly in `E ∈ bulkInterval κ`**: the conclusion of
`PassiveCovarianceContract` with `κ` before the constants (a hypothesis of the moving-energy
chain). -/
def PassiveCovarianceEnergyUniformHyp : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ s : ℂ, IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        let T := passiveTransmission b E X
        let f := passiveF b E X
        let I : Matrix (Fin W) (Fin W) ℂ := 1
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
                (crossedTensor v₁ v₂ v₃ v₄ I (I - T) + crossedTensor v₁ v₂ v₃ v₄ (I - T) I) +
              sigmaMinus b E s / W * crossedTensor v₁ v₂ v₃ v₄ f f +
              conj (sigmaMinus b E s) / W * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
            fourNorm v₁ v₂ v₃ v₄

/-- **Layer bounds uniform in `b`**: the three layer contract fields (`GaussianAbsorptionContract`,
`TraceMatrixContract.fluctuation`, `WeightedLayerContract.clockMean`) with constants uniform for
`b ∈ Set.Icc β (1/2 - β)` (a hypothesis of the moving-energy chain).
-/
structure LayersBUniformHyp : Prop where
  gaussianAbsorption : ∀ β : ℝ, 0 < β → β < 1 / 4 → ∀ η₀ M : ℝ, 0 < η₀ →
    ∃ ε₁ C : ℝ, 0 < ε₁ ∧ 0 < C ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ (W : ℕ), 0 < W → ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ),
        X.IsHermitian → ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
          (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
          ∀ p : ℝ, 1 ≤ p → p ≤ ε₁ * W →
            eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal p) (layerLaw W b σ) ≤
              ENNReal.ofReal C
  traceMatrixFluctuation : ∀ β : ℝ, 0 < β → β < 1 / 4 → ∀ η₀ M : ℝ, 0 < η₀ → ∀ K : ℝ,
    ∃ ε₃ C : ℝ, 0 < ε₃ ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ (W : ℕ), 0 < W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
      ∀ D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖D‖ ≤ K →
      ∀ p : ℝ, 2 ≤ p → p ≤ ε₃ * W →
        let μ := layerLaw W b σ
        let f : LayerSample W σ → ℂ := fun ω =>
          (W : ℂ)⁻¹ * (D * layerResolvent σ E z X ω).trace
        eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂μ) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (C * Real.sqrt p / W)
  weightedLayerClockMean : ∀ β : ℝ, 0 < β → β < 1 / 4 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
    ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      matchedDistance b E X ≤ dstar → ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      Y.PosSemidef →
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Lm := fun ω => K * (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂
      let u := (W : ℝ)⁻¹ * Y.trace.re
      Integrable (fun ω => (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re) μ ∧
      (∫ ω, (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re ∂μ) ≤
        (1 + C * matchedDistance b E X + C / (W : ℝ) ^ 2) * u

end BlockBand.Endpoints.Clock.MovingEnergy
