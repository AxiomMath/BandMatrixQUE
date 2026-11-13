module

public import BlockBand.Transmission.PathJet.JetMeanStep
public import BlockBand.Transmission.PathJet.JetFlucMain

/-!
# `PassiveJetMeanStep`: the jet mean step for every passive input

`passiveJetMeanStep_holds (hA : PassiveBoundsStatement) : PassiveJetMeanStep`: `b, κ` first;
then `d₀ > 0`, `0 ≤ ρ₁ < 1`, `C₂, C ≥ 0`, `W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ`, every
stationary jet `s` and every passive `X` with `δ₀(X) ≤ d₀`,
`|E freshJet - s| ≤ ρ₁δ₁(X) + C₂δ₀(X) + C/W²`.

`Y ≻ 0` holds only almost surely along the path, so the strict step (`jetMean_strict`, inputs
`Y = Y₀ + ε`) is extended by the regularization `X - i/(n+1)`: `δ₀, δ₁` converge
(`tendsto_jet0_regX`, `tendsto_jet1_regX`) and `E freshJet` converges by dominated convergence
(`|freshJet| ≤ η⁻²`, and `freshJet = -τ₂(𝒢)` a.s. with the continuity along `regX`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The passive jet mean step.** -/
def PassiveJetMeanStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (d₀ ρ₁ C₂ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ ρ₁ ∧ ρ₁ < 1 ∧ 0 ≤ C₂ ∧ 0 ≤ C ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDistance0 b E X ≤ d₀ →
        ‖(∫ ω, freshJet b E X ω ∂freshLaw W b) - s‖ ≤
          ρ₁ * jetDistance1 b E s X + C₂ * jetDistance0 b E X + C / (W : ℝ) ^ 2

theorem regX_eq_layer (X : Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    PassiveCovariance.regX X n = PassiveLayer.regX X (epsN n) := by
  rw [PassiveCovariance.regX, PassiveLayer.regX, epsN, one_div, mul_comm]

theorem tendsto_integral_freshJet_regX {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W)
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    Tendsto (fun n => ∫ ω, freshJet b E (PassiveCovariance.regX X n) ω ∂freshLaw W b) atTop
      (𝓝 (∫ ω, freshJet b E X ω ∂freshLaw W b)) := by
  have hYn := fun n => passiveY_regX_posSemidef hY n
  have hzim : 0 < (boundaryZ b E).im := Bridge.boundaryZ_im_pos (by linarith) h1 h2
  have hmeas : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      AEStronglyMeasurable (freshJet b E X') (freshLaw W b) := fun X' hX' =>
    (measurable_jetFun_comp b E measurable_const measurable_id).aestronglyMeasurable.congr
      ((ae_layer_herm b).mono fun ω hA => (freshJet_eq_jetFun (by linarith) h1 h2 hX' hA).symm)
  refine tendsto_integral_of_dominated_convergence (fun _ => (etaZ b E)⁻¹ ^ 2)
    (fun n => hmeas _ (hYn n)) (integrable_const _) (fun n => (ae_layer_herm b).mono fun ω hA => by
      rw [freshJet_eq_jetFun (by linarith) h1 h2 (hYn n) hA]
      exact norm_jetFun_le (by linarith) h1 h2 (hYn n) hA) ?_
  filter_upwards [ae_all_iff.2 fun n => freshJet_ae_eq hb0 hb hW h1 h2 (hYn n),
    freshJet_ae_eq hb0 hb hW h1 h2 hY, ae_good W hb0 hW] with ω hn h0 hω
  have hn' : ∀ n, -tau2Layer E (boundaryZ b E) (PassiveLayer.regX X (epsN n)) ω =
      freshJet b E (PassiveCovariance.regX X n) ω := fun n => by rw [hn n, regX_eq_layer]
  rw [h0]
  exact (tendsto_tau2Layer_reg E (boundaryZ b E) X ω ((isUnit_iff_isUnit_det _).mpr
    (layer_schur E hzim hY hω.1 hω.2).1)).neg.congr hn'

theorem passiveJetMeanStep_holds (hA : PassiveBoundsStatement) : PassiveJetMeanStep := by
  intro b hb0 hb κ hκ
  obtain ⟨d₀, C₂, C, W₀, hd₀, hC₂, hC, hstrict⟩ := jetMean_strict hA hb0 hb hκ
  have hg := kGap_pos hb0 hb hκ
  refine ⟨d₀ / 2, rhoJ b (kGap b κ), C₂, C, max W₀ 1, by positivity, rhoJ_nonneg hb0 hg,
    rhoJ_lt_one hb0 hg, hC₂, hC, ?_⟩
  intro W hW E hE s hs X hY hδ
  have hW0 : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hj0 := tendsto_jet0_regX hb0 hb h1 h2 hY
  have hj1 := tendsto_jet1_regX hb0 hb h1 h2 hY s
  have hev : ∀ᶠ n in atTop, jetDistance0 b E (PassiveCovariance.regX X n) ≤ d₀ :=
    hj0.eventually (ge_mem_nhds (by linarith))
  have hL := ((tendsto_integral_freshJet_regX hb0 hb hW1 h1 h2 hY).sub_const s).norm
  have hR := (((hj1.const_mul (rhoJ b (kGap b κ))).add (hj0.const_mul C₂)).add_const
    (C / (W : ℝ) ^ 2))
  refine le_of_tendsto_of_tendsto hL hR (hev.mono fun n hn => ?_)
  have hε : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  exact hstrict W hW0 E hE s hs (PassiveCovariance.regX X n) (passiveY X) _ hε hY
    (passiveY_regX X n) hn

end BlockBand.Transmission.PathJet
