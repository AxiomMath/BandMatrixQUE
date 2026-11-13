module

public import BlockBand.Transmission.PathScalar.AbsorbedStep
public import BlockBand.Transmission.PathScalar.StoppedRecursion

/-!
# The absorbed near-end scalar recursion, almost surely

With `δ_j = δ₀(X_j)` along the near-end growth with a profile `κ ≥ 0` whose absorptions are at
most `K/W²`, and `ξ_{j+1} = stepFluct κ j`:
* `ae_absorbed_step`: from the (absorbed) mean step, almost surely for all `j ≥ 1`,
  `δ_j ≤ d₀/2 → δ_{j+1} ≤ ρδ_j + (C + K/η_κ²)/W² + ξ_{j+1}`;
* `ae_absorbed_bound`: almost surely `δ_j ≤ η_κ⁻¹ + 1` (the deterministic port bound);
* `measurable_absorbedDelta`.
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

/-- `δ_j = δ₀(X_j)` along the near-end growth with absorption profile `κ`. -/
def absorbedDelta (b E : ℝ) (κ : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  jetDistance0 b E (pathNearSchur b E κ W j ω)

theorem measurable_jetDistance0 (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => jetDistance0 b E X := by
  have hR : Measurable fun X : Matrix (Fin W) (Fin W) ℂ => passiveResolvent b E X := by
    refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
    simp only [Matrix.sub_apply]
    exact measurable_const.sub measurable_id.eval_matrix
  simp only [jetDistance0, Matrix.trace, Matrix.diag]
  exact ((measurable_const.mul (Finset.measurable_sum _ fun i _ => hR.eval_matrix)).sub
    measurable_const).norm

theorem measurable_absorbedDelta (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) :
    Measurable (absorbedDelta b E κ W j) := by
  have : absorbedDelta b E κ W j = (fun X => jetDistance0 b E X) ∘ pastX b E κ W j ∘
      pastCoords W j := by
    funext ω; simp only [absorbedDelta, Function.comp, pathNearSchur_eq_past]
  rw [this]
  exact (measurable_jetDistance0 b E).comp ((measurable_pastX b E κ j).comp
    (measurable_pastCoords W j))

theorem absorbedDelta_nonneg (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) (ω : GrowthPath W) :
    0 ≤ absorbedDelta b E κ W j ω := norm_nonneg _

/-- **The deterministic port bound, almost surely**: `δ_j ≤ η_κ⁻¹ + 1`. -/
theorem ae_absorbed_bound {b E κ' : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ' : 0 < κ')
    (hE : E ∈ bulkInterval κ') {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (j : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, absorbedDelta b E κ W j ω ≤ (etaLow b κ')⁻¹ + 1 := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ' hE
  filter_upwards [ae_passiveSample W hκ (by linarith) h1 h2] with ω hP
  refine (jetDistance0_le_bound hb0 hb h1 h2 (pathNearSchur_passive hP j)).trans ?_
  have := etaLow_le (by linarith : b < 1) hκ' hE
  have := etaLow_pos (by linarith : b < 1) hκ'
  gcongr

/-- **The absorbed scalar step, almost surely.** -/
theorem ae_absorbed_step {b κ' d₀ ρ C K : ℝ} {W₀ : ℕ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ' : 0 < κ') (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : 0 ≤ K)
    (hmean : ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ', ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → jetDistance0 b E X ≤ d₀ →
          ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) - matchedA E‖ ≤
            ρ * jetDistance0 b E X + C / (W : ℝ) ^ 2)
    {W : ℕ} (hW : W₀ ≤ W) (hW1 : 1 ≤ W) (hWK : K / (etaLow b κ' ^ 2 * (W : ℝ) ^ 2) ≤ d₀ / 2)
    {E : ℝ} (hE : E ∈ bulkInterval κ') {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s)
    (hκK : ∀ (m : ℕ) (i : Fin m), layerAbsorption W κ m i ≤ K / (W : ℝ) ^ 2) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → absorbedDelta b E κ W j ω ≤ d₀ / 2 →
      absorbedDelta b E κ W (j + 1) ω ≤ ρ * absorbedDelta b E κ W j ω +
        (C + K / etaLow b κ' ^ 2) / (W : ℝ) ^ 2 + stepFluct b E κ W j ω := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ' hE
  filter_upwards [ae_pathNearSchur_succ_abs hb h1 h2 hW1 hκ,
    ae_passiveSample W hκ (by linarith) h1 h2] with ω hrec hP j hj hd
  have hε0 : 0 ≤ layerAbsorption W κ (j + 1) 0 := div_nonneg (hκ _) (sq_nonneg _)
  have hm := absorbedMeanStep hb0 hb hκ' hρ0 hρ1 hK hmean hW (by omega) hWK hE
    (pathNearSchur_passive hP j) hd hε0 (hκK _ _)
  have hin : stepInput b E κ W j (pastCoords W j ω) = pathNearSchur b E κ W j ω -
      (((layerAbsorption W κ (j + 1) 0 : ℝ) : ℂ) * Complex.I) • 1 := by
    rw [stepInput, pathNearSchur_eq_past]
  have hfl : stepFluct b E κ W j ω = ‖freshPortTrace b E (pathNearSchur b E κ W j ω -
      (((layerAbsorption W κ (j + 1) 0 : ℝ) : ℂ) * Complex.I) • 1) (freshSample W j ω) -
        ∫ f, freshPortTrace b E (pathNearSchur b E κ W j ω -
          (((layerAbsorption W κ (j + 1) 0 : ℝ) : ℂ) * Complex.I) • 1) f ∂freshLaw W b‖ := by
    rw [stepFluct, stepPhi, hin]
  rw [absorbedDelta, hrec j hj, jetDistance0_freshSchur, hfl]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (∫ f, freshPortTrace b E
    (pathNearSchur b E κ W j ω - (((layerAbsorption W κ (j + 1) 0 : ℝ) : ℂ) * Complex.I) • 1) f
      ∂freshLaw W b) _).trans ?_
  rw [absorbedDelta]
  linarith

end BlockBand.Transmission.PathScalar
