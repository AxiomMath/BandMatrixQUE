module

public import BlockBand.Transmission.PathScalar.AbsorbedPath

/-!
# The passive one-port scalar step (statements) and its absorbed form

For a deterministic passive input `X` (the old path integrated out, `Layers` convention) and
one fresh one-port layer `freshLaw W b`, `freshPortTrace b E X = W⁻¹ Tr (z - X₊)⁻¹`,
`X₊ = B*(A - E - X)⁻¹B`; so `δ₀(X₊) = |freshPortTrace - a|` (`jetDistance0_freshSchur`).

**Inputs (named `Prop`s):**
* `PassiveMeanStep`: on the scalar domain `δ₀(X) ≤ d₀`, `|E freshPortTrace - a| ≤ ρδ₀(X) + C/W²`
  with `ρ < 1` (the stable branch of the scalar mean map);
* `PassiveFluctuationStep`: `‖freshPortTrace - E freshPortTrace‖_p ≤ C_p/W` for every passive
  `X` (Gaussian `L^p` Poincaré).

Both are about the **unabsorbed** fresh layer with an arbitrary passive input: the absorption
`iε` of the fresh block moves into the input `X - iε` (`Bridge.pathNearSchur_succ_eq_freshSchur`),
which stays passive and moves `δ₀` by at most `ε/η²` (`Dissipative`). Hence no absorbed IBP
equations are needed. `absorbedMeanStep` is the resulting absorbed one-step bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open scoped ENNReal NNReal Matrix ComplexOrder

variable {W : ℕ}

/-- The fresh near-port trace `W⁻¹ Tr (z - X₊)⁻¹`, `X₊ = B*(A - E - X)⁻¹B`. -/
def freshPortTrace (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ℂ :=
  (W : ℂ)⁻¹ * (passiveResolvent b E (freshSchur E X ω)).trace

theorem jetDistance0_freshSchur (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    jetDistance0 b E (freshSchur E X ω) = ‖freshPortTrace b E X ω - matchedA E‖ := rfl

/-- **Passive mean step** (proved by `passiveMeanStep_holds`): `b, κ` first; then
the domain
radius `d₀ > 0`, the contraction `0 ≤ ρ < 1`, `C ≥ 0` and `W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ`
and every deterministic passive `X` with `δ₀(X) ≤ d₀`,
`|E_{freshLaw} W⁻¹Tr R₊ - a| ≤ ρ δ₀(X) + C/W²`. -/
def PassiveMeanStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (d₀ ρ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → jetDistance0 b E X ≤ d₀ →
          ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) - matchedA E‖ ≤
            ρ * jetDistance0 b E X + C / (W : ℝ) ^ 2

/-- **Passive fluctuation step** (proved by `PassiveLayer.passiveFluctuationStep_holds`): for
every `p ≥ 1` there are `C, W₀`;
for `W ≥ W₀`, `E ∈ bulkInterval κ` and every deterministic passive `X`,
`‖W⁻¹Tr R₊ - E W⁻¹Tr R₊‖_{L^p(freshLaw)} ≤ C/W`. -/
def PassiveFluctuationStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        eLpNorm (fun ω => ‖freshPortTrace b E X ω - ∫ ω', freshPortTrace b E X ω' ∂freshLaw W b‖)
          (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (C / W)

/-!
## A uniform lower bound for `η` on the bulk interval
-/

/-- `η_κ = (1-b)√(2 min(κ,2))/2`, a lower bound for `η = Im z_∂` on `bulkInterval κ`. -/
def etaLow (b κ : ℝ) : ℝ := (1 - b) * Real.sqrt (2 * min κ 2) / 2

theorem etaLow_pos {b κ : ℝ} (hb : b < 1) (hκ : 0 < κ) : 0 < etaLow b κ := by
  unfold etaLow
  have : 0 < min κ 2 := lt_min hκ (by norm_num)
  have := Real.sqrt_pos.2 (by linarith : (0 : ℝ) < 2 * min κ 2)
  have : 0 < 1 - b := by linarith
  positivity

theorem etaLow_le {b κ E : ℝ} (hb : b < 1) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    etaLow b κ ≤ etaZ b E := by
  have hE1 : -2 + κ ≤ E := hE.1
  have hE2 : E ≤ 2 - κ := hE.2
  have hm1 : min κ 2 ≤ κ := min_le_left _ _
  have hm2 : min κ 2 ≤ 2 := min_le_right _ _
  have hm0 : 0 < min κ 2 := lt_min hκ (by norm_num)
  have hsq : 2 * min κ 2 ≤ 4 - E ^ 2 := by nlinarith
  rw [etaZ, boundaryZ_im b E (by nlinarith), etaLow]
  have : 0 < 1 - b := by linarith
  gcongr

/-!
## The absorbed one-step mean bound
-/

/-- **Absorbed mean step**: with the mean step at radius `d₀`, for `ε ∈ [0, K/W²]`, a passive
`X` with `δ₀(X) ≤ d₀/2` and `K/(η_κ² W²) ≤ d₀/2`,
`|E freshPortTrace(X - iε) - a| ≤ ρ δ₀(X) + (C + K/η_κ²)/W²`. -/
theorem absorbedMeanStep {b κ d₀ ρ C K : ℝ} {W₀ : ℕ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : 0 ≤ K)
    (hmean : ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → jetDistance0 b E X ≤ d₀ →
          ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) - matchedA E‖ ≤
            ρ * jetDistance0 b E X + C / (W : ℝ) ^ 2)
    {W : ℕ} (hW : W₀ ≤ W) (hW0 : 0 < W) (hWK : K / (etaLow b κ ^ 2 * (W : ℝ) ^ 2) ≤ d₀ / 2)
    {E : ℝ} (hE : E ∈ bulkInterval κ) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hX : jetDistance0 b E X ≤ d₀ / 2) {ε : ℝ} (hε0 : 0 ≤ ε) (hεK : ε ≤ K / (W : ℝ) ^ 2) :
    ‖(∫ ω, freshPortTrace b E (X - (((ε : ℂ) * Complex.I)) • 1) ω ∂freshLaw W b) - matchedA E‖ ≤
      ρ * jetDistance0 b E X + (C + K / etaLow b κ ^ 2) / (W : ℝ) ^ 2 := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hηl := etaLow_pos (by linarith : b < 1) hκ
  have hηle := etaLow_le (by linarith : b < 1) hκ hE
  have hW2 : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  have hshift := jetDistance0_absorb_le hb0 hb h1 h2 hY hε0
  have hε' : ε / etaZ b E ^ 2 ≤ K / (etaLow b κ ^ 2 * (W : ℝ) ^ 2) := by
    calc ε / etaZ b E ^ 2 ≤ (K / (W : ℝ) ^ 2) / etaLow b κ ^ 2 := by
          gcongr
      _ = K / (etaLow b κ ^ 2 * (W : ℝ) ^ 2) := by field_simp
  have hdom : jetDistance0 b E (X - (((ε : ℂ) * Complex.I)) • 1) ≤ d₀ := by linarith
  refine (hmean W hW E hE _ (passiveY_absorb hY hε0) hdom).trans ?_
  have hKe : K / (etaLow b κ ^ 2 * (W : ℝ) ^ 2) = K / etaLow b κ ^ 2 / (W : ℝ) ^ 2 := by
    field_simp
  have : ρ * (ε / etaZ b E ^ 2) ≤ K / etaLow b κ ^ 2 / (W : ℝ) ^ 2 := by
    rw [← hKe]
    have h0 : 0 ≤ ε / etaZ b E ^ 2 := div_nonneg hε0 (sq_nonneg _)
    nlinarith
  calc ρ * jetDistance0 b E (X - (((ε : ℂ) * Complex.I)) • 1) + C / (W : ℝ) ^ 2
      ≤ ρ * (jetDistance0 b E X + ε / etaZ b E ^ 2) + C / (W : ℝ) ^ 2 := by gcongr
    _ ≤ ρ * jetDistance0 b E X + (C + K / etaLow b κ ^ 2) / (W : ℝ) ^ 2 := by
        rw [add_div]; nlinarith

end BlockBand.Transmission.PathScalar
