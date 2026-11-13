module

public import BlockBand.Internal.Contracts.Layers

/-!
# `b`-uniform clauses of three layer estimates

Versions of the Gaussian absorption moments, the trace fluctuation bound and the clock mean
bound with constants uniform over bonds `b ∈ [β, 1/2 - β]`, for fixed `β ∈ (0, 1/4)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.LayersBUniform

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-- **Gaussian absorption, `b`-uniform.** `GaussianAbsorptionContract` with
`β ∈ (0,1/4)`, `η₀, M` first; then `ε₁, C > 0`; then uniformly in `b ∈ [β, 1/2 - β]` and in
everything the fixed-`b` statement quantifies after its constants.
-/
def GaussianAbsorptionUniformContract : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 / 4 → ∀ η₀ M : ℝ, 0 < η₀ →
    ∃ ε₁ C : ℝ, 0 < ε₁ ∧ 0 < C ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ (W : ℕ), 0 < W → ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ),
        X.IsHermitian → ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
          (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
          ∀ p : ℝ, 1 ≤ p → p ≤ ε₁ * W →
            eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal p) (layerLaw W b σ) ≤
              ENNReal.ofReal C

/-- **Trace fluctuation, `b`-uniform.** `TraceMatrixContract.fluctuation`
with `β ∈ (0,1/4)`, `η₀, M, K` first; then `ε₃ > 0`, `C`; then uniformly in `b ∈ [β, 1/2 - β]`.
-/
def TraceFluctuationUniformContract : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 / 4 → ∀ η₀ M : ℝ, 0 < η₀ → ∀ K : ℝ,
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

/-- **Clock mean, `b`-uniform.** `WeightedLayerContract.clockMean` with
`β ∈ (0,1/4)`, `κ > 0` first; then `d_* > 0`, `C`, `W₀`; then uniformly in `b ∈ [β, 1/2 - β]`,
`W ≥ W₀`, Hermitian `X`, `E ∈ bulkInterval κ` with `d(X) ≤ d_*` and `Y ⪰ 0`.
-/
def ClockMeanUniformContract : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 / 4 → ∀ κ : ℝ, 0 < κ →
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

end BlockBand.Internal.Contracts.LayersBUniform
