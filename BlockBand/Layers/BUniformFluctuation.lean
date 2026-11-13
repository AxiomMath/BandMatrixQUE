module

public import BlockBand.Layers.BUniformAbsorption
public import BlockBand.Layers.TraceFluctuation

/-!
# The fresh trace fluctuation bound, uniformly in `b`

This file proves `TraceFluctuationUniformContract` (`traceFluctuationUniform_holds`): the proof of
`traceFluctuation_holds`, with the absorption constants taken from the uniform clause at `β`.
The core estimate `tfl_fluctuation_core` uses `b` only through `0 < b < 1/2`, so with `ε₁, C_A`
fixed before `b` the constants `ε₃ = ε₁/2`, `C = 16 C_g K C_A²` are uniform in `b ∈ [β, 1/2-β]`.

* **Law**: `layerLaw W b σ` (blocks `GUE_W((1-2b)/W)`, bonds `Gin(b/W)`).
* **Domain**: `W ≥ 1`, every shape, Hermitian `X`, real `E`, `Im z ≥ η₀`, `‖z‖ ≤ M`,
  deterministic `D` with `‖D‖ ≤ K`, `2 ≤ p ≤ ε₃ W`; `f = W⁻¹ Tr(D 𝒢)`.
* **Norms**: `ℓ²` operator norm on matrices; `L^p(layerLaw)` norm of `f - Ef`.
* **Quantifier order**: `β ∈ (0,1/4)`, `η₀ > 0`, `M`, `K`; then `ε₃ = ε₁/2 > 0`,
  `C = 16 C_g K C_A²`; then uniformly in `b ∈ [β, 1/2-β]` and everything else.
* **Inputs**: `Inputs.GaussianLpGradient` (constant `C_g`, `b`-free) and the uniform absorption
  clause `GaussianAbsorptionUniformContract` (`ε₁, C_A` depending only on `β, η₀, M`), which is
  in turn proved from `Inputs.ConditionalBlockGUECount` (`gaussianAbsorptionUniform_holds`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.LayersBUniform
open BlockBand.Internal.Contracts.Inputs (ConditionalBlockGUECount GaussianLpGradient)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- **The fresh trace fluctuation bound, `b`-uniform, from the uniform absorption clause**
(adapted from `traceFluctuation_holds`).
With `ε₁, C_A` from `GaussianAbsorptionUniformContract β η₀ M` and `C_g` from
`GaussianLpGradient`: `ε₃ = ε₁/2`, `C = 16 C_g K C_A²`, uniformly in `b ∈ [β, 1/2-β]`. -/
theorem bu_traceFluctuationUniform_of (hgrad : GaussianLpGradient)
    (habsU : GaussianAbsorptionUniformContract) : TraceFluctuationUniformContract := by
  intro β hβ hβ4 η₀ M hη K
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  obtain ⟨ε₁, CA, hε₁, hCA, habs'⟩ := habsU β hβ hβ4 η₀ M hη
  refine ⟨ε₁ / 2, 16 * Cg * K * CA ^ 2, by positivity, ?_⟩
  intro b hb W hW σ X hX E z hz hzM D hD p hp2 hpε μ f
  obtain ⟨hb0, hb1⟩ := bu_mem_bounds hβ hb
  obtain ⟨hinv, hmom⟩ := habs' b hb W hW σ X hX E z hz hzM
  have hz0 : 0 ≤ z.im := le_trans hη.le hz
  have h2p1 : 1 ≤ 2 * p := by linarith
  have h2pε : 2 * p ≤ ε₁ * W := by linarith
  have hcore := tfl_fluctuation_core hCg.le hgr hW hb0 hb1 σ hX E hz0 D
    (by linarith : (1 : ℝ) ≤ p) hCA.le hinv (hmom (2 * p) h2p1 h2pε)
  refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hD
  have hsp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  calc Cg * Real.sqrt p * (16 * ‖D‖ / W) * CA ^ 2
      = 16 * Cg * ‖D‖ * CA ^ 2 * Real.sqrt p / W := by ring
    _ ≤ 16 * Cg * K * CA ^ 2 * Real.sqrt p / W := by gcongr

/-- **The fresh trace fluctuation bound, uniformly in `b`**, from `ConditionalBlockGUECount` and
`GaussianLpGradient`. -/
theorem traceFluctuationUniform_holds (hcount : ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : TraceFluctuationUniformContract :=
  bu_traceFluctuationUniform_of hgrad (gaussianAbsorptionUniform_holds hcount)

/-- The uniform clause implies the fixed-`b` clause `TraceMatrixContract.fluctuation`
(with `β = min b (1/2-b) / 2`). -/
theorem bu_traceFluctuation_of_uniform (hU : TraceFluctuationUniformContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ η₀ M : ℝ, 0 < η₀ → ∀ K : ℝ,
    ∃ ε₃ C : ℝ, 0 < ε₃ ∧ ∀ (W : ℕ), 0 < W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
      ∀ D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖D‖ ≤ K →
      ∀ p : ℝ, 2 ≤ p → p ≤ ε₃ * W →
        let μ := layerLaw W b σ
        let f : LayerSample W σ → ℂ := fun ω =>
          (W : ℂ)⁻¹ * (D * layerResolvent σ E z X ω).trace
        eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂μ) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (C * Real.sqrt p / W) := by
  intro b hb0 hb1 η₀ M hη K
  obtain ⟨hβ0, hβ1, hbI⟩ := bu_beta_of_mem hb0 hb1
  obtain ⟨ε₃, C, hε₃, h⟩ := hU _ hβ0 hβ1 η₀ M hη K
  exact ⟨ε₃, C, hε₃, h b hbI⟩

/-- `bu_traceFluctuation_of_uniform` has exactly the type of `TraceMatrixContract.fluctuation`. -/
example (hU : TraceFluctuationUniformContract) (hT : TraceMatrixContract) :
    hT.fluctuation = bu_traceFluctuation_of_uniform hU := rfl

end BlockBand.Layers
