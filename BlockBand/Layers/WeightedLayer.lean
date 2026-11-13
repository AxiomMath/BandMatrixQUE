module

public import BlockBand.Layers.WeightedLayerWard

/-!
# The weighted-layer lemma: the weighted Ward identity and the clock bounds

The weighted-layer lemma, stated as `Layers.WeightedLayerContract`, from
`ConditionalBlockGUECount` and `GaussianLpGradient` (`weightedLayer_holds`).

Setting (that of `WeightedLayerContract`): one separate-port step, `𝒢` of `layerLaw W b .separate`
(`A_a ~ GUE_W(c/W)`, `c = 1 - 2b`, bonds `Gin(b/W)`) at `z = z_∂(E)`, `E ∈ bulkInterval κ`, a
deterministic Hermitian two-port `X` (the independent old input; expectations conditional on
`X` by Fubini), `K = z - X`, `L = K 𝒢₁₂`, deterministic `Y ⪰ 0`, `u = W⁻¹ Tr Y`. Norms: `ℓ²`
operator norm; `L^p` norms under `layerLaw`.

Fields and where they are proved:
* moments: `wl_moments` (`WeightedLayerNoise`, §5).
* the weighted Ward identity: `wl_ward` below, from `wl_ward_core` (`WeightedLayerWard`).
* the clock-mean identity: `wl_clockMean` below — trace pairing of the weighted
  Ward identity with `Y ⪰ 0` (`wl_norm_trace_weight_le`).
* the clock-noise bound: `wl_clockNoise` (`WeightedLayerNoise`, §9).
* the unrestricted bound: `wl_unrestricted` (`WeightedLayerNoise`, §5).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-- **`ward`** (the weighted Ward identity): on `d(X) ≤ d_*`, `W ≥ W₀`,
`‖E LL* - I‖ ≤ C(d(X) + W⁻²)`, with integrable entries. -/
theorem wl_ward (hcount : ConditionalBlockGUECount) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      matchedDistance b E X ≤ dstar →
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Lm := fun ω => K * (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂
      (∀ x y, Integrable (fun ω => (Lm ω * (Lm ω)ᴴ) x y) μ) ∧
      ‖matrixExpect μ (fun ω => Lm ω * (Lm ω)ᴴ) - 1‖ ≤
        C * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) := by
  intro b hb0 hb1 κ hκ
  obtain ⟨dstar, C, W₀, hd, -, h⟩ := wl_ward_core hcount b hb0 hb1 κ hκ
  refine ⟨dstar, C, W₀, hd, ?_⟩
  intro W hW hWW X hX E hE hdd μ K Lm
  obtain ⟨hint, hb⟩ := h W hW hWW X hX E hE hdd
  refine ⟨fun x y => ?_, ?_⟩
  · exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ x y :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →ₗ[ℂ] ℂ)).integrable_comp hint
  · change ‖matrixExpect (layerLaw W b .separate) (wlLL b E X) - 1‖ ≤ _
    rw [meq_matrixExpect_eq hint]
    exact hb

/-- The trace pairing `N ↦ W⁻¹ Re Tr(Y N)` as a real continuous linear map. -/
def wlPairing {W : ℕ} (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun N => (W : ℝ)⁻¹ * (Y * N).trace.re
      map_add' := fun N N' => by simp [Matrix.trace_add, mul_add]
      map_smul' := fun r N => by
        simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul,
          RingHom.id_apply, smul_eq_mul]
        ring }

theorem wlPairing_apply {W : ℕ} (Y N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    wlPairing Y N = (W : ℝ)⁻¹ * (Y * N).trace.re := rfl

/-- **`clockMean`** (the clock-mean identity): on `d(X) ≤ d_*`,
`W ≥ W₀`, for `Y ⪰ 0`: `E W⁻¹ Tr L*YL ≤ (1 + C d(X) + C W⁻²) u`. -/
theorem wl_clockMean (hcount : ConditionalBlockGUECount) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      matchedDistance b E X ≤ dstar → ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      Y.PosSemidef →
      let μ := layerLaw W b .separate
      let K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Lm := fun ω => K * (layerResolvent .separate E (boundaryZ b E) X ω).toBlocks₁₂
      let u := (W : ℝ)⁻¹ * Y.trace.re
      Integrable (fun ω => (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re) μ ∧
      (∫ ω, (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re ∂μ) ≤
        (1 + C * matchedDistance b E X + C / (W : ℝ) ^ 2) * u := by
  intro b hb0 hb1 κ hκ
  obtain ⟨dstar, C, W₀, hd, hC, h⟩ := wl_ward_core hcount b hb0 hb1 κ hκ
  refine ⟨dstar, C, W₀, hd, ?_⟩
  intro W hW hWW X hX E hE hdd Y hY μ K Lm u
  obtain ⟨hint, hb⟩ := h W hW hWW X hX E hE hdd
  have hpt : ∀ ω, (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re = wlPairing Y (wlLL b E X ω) := by
    intro ω
    rw [wlPairing_apply]
    congr 2
    change ((Lm ω)ᴴ * Y * Lm ω).trace = (Y * (Lm ω * (Lm ω)ᴴ)).trace
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have hfun : (fun ω => (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re) =
      fun ω => wlPairing Y (wlLL b E X ω) := funext hpt
  rw [hfun]
  refine ⟨(wlPairing Y).integrable_comp hint, ?_⟩
  rw [(wlPairing Y).integral_comp_comm hint, wlPairing_apply]
  set N := ∫ ω, wlLL b E X ω ∂layerLaw W b .separate with hN
  have hTY := wl_trace_re_nonneg hY
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hΔ := wl_norm_trace_weight_le hY (N - 1)
  have e : (Y * N).trace = Y.trace + (Y * (N - 1)).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]; ring
  have hre : (Y * N).trace.re ≤ (1 + ‖N - 1‖) * Y.trace.re := by
    rw [e, Complex.add_re]
    have := Complex.re_le_norm (Y * (N - 1)).trace
    nlinarith
  have hbd : (1 + ‖N - 1‖) ≤ 1 + C * matchedDistance b E X + C / (W : ℝ) ^ 2 := by
    have := hb
    have e2 : C * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) =
        C * matchedDistance b E X + C / (W : ℝ) ^ 2 := by ring
    linarith
  calc (W : ℝ)⁻¹ * (Y * N).trace.re ≤ (W : ℝ)⁻¹ * ((1 + ‖N - 1‖) * Y.trace.re) :=
        mul_le_mul_of_nonneg_left hre (by positivity)
    _ ≤ (W : ℝ)⁻¹ * ((1 + C * matchedDistance b E X + C / (W : ℝ) ^ 2) * Y.trace.re) := by
        gcongr
    _ = (1 + C * matchedDistance b E X + C / (W : ℝ) ^ 2) * u := by ring

/-- **The weighted-layer lemma** (`WeightedLayerContract`), from `ConditionalBlockGUECount`
(through `gaussianAbsorption_holds` and `layerComparison_holds`) and `GaussianLpGradient`. All
constants depend only on `b`, the bulk interval `bulkInterval κ` and the moment order `p`;
uniform in `W ≥ W₀`, Hermitian `X`, `E ∈ I` and `Y ⪰ 0`. -/
theorem weightedLayer_holds (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    WeightedLayerContract where
  moments := wl_moments hcount
  ward := wl_ward hcount
  clockMean := wl_clockMean hcount
  clockNoise := wl_clockNoise hcount hgrad
  unrestricted := wl_unrestricted hcount

end BlockBand.Layers
