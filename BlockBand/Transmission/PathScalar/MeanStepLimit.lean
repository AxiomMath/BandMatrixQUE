module

public import BlockBand.Transmission.PathScalar.MeanEqStrict
public import BlockBand.Transmission.PassiveCovariance.Continuity

/-!
# `PassiveMeanStep` from the passive bounds

* `passiveMeanStep_holds (hA : PassiveBoundsStatement) : PassiveMeanStep`: for strictly passive
  inputs from `passiveMeanEquationsStrict_holds` and the deterministic `passiveMean_stability`;
  for general passive inputs by the regularization `X - i/(n+1)` (`Regularization`,
  `tendsto_jet0_regX`), with dominated convergence of `E W⁻¹Tr R₊`
  (`tendsto_integral_freshPortTrace_regX`, bound `|W⁻¹Tr R₊| ≤ η⁻¹` from
  `passiveY_freshSchur`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem layerSample_eta (ω : LayerSample W .oneBlockOnePort) :
    ω = ((fun _ => ω.1 0), (fun _ _ => ω.2 0 0)) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
  · fin_cases i; rfl
  · fin_cases i; fin_cases j; rfl

theorem passiveY_freshSchur (E : ℝ) {Y : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY Y).PosSemidef)
    (ω : LayerSample W .oneBlockOnePort) (hA : (ω.1 0).IsHermitian) :
    (passiveY (freshSchur E Y ω)).PosSemidef := by
  rw [layerSample_eta ω, freshSchur_eq]
  have hF : (matrixImaginaryPart (ω.1 0 - (E : ℂ) • 1 - Y)).PosSemidef := by
    have hA0 : matrixImaginaryPart (ω.1 0) = 0 := by rw [matrixImaginaryPart, hA.eq, sub_self, smul_zero]
    have hE0 : matrixImaginaryPart ((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) = 0 := by
      rw [matrixImaginaryPart, (isHermitian_one.smul (Complex.conj_ofReal E)).eq, sub_self, smul_zero]
    rw [matrixImaginaryPart_sub, matrixImaginaryPart_sub, hA0, hE0, sub_zero, zero_sub]
    exact hY
  rw [passiveY, matrixImaginaryPart_congruence, neg_congruence]
  exact (neg_im_inv_posSemidef _ hF).conjTranspose_mul_mul_same _

theorem norm_freshPortTrace_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {Y : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY Y).PosSemidef) (ω : LayerSample W .oneBlockOnePort)
    (hA : (ω.1 0).IsHermitian) : ‖freshPortTrace b E Y ω‖ ≤ (etaZ b E)⁻¹ :=
  (norm_normTrace_le _).trans (norm_passiveResolvent_le hb0 hb h1 h2 (passiveY_freshSchur E hY ω hA))

/-- `E W⁻¹Tr R₊` is continuous along the regularization `X - i/(n+1)`. -/
theorem tendsto_integral_freshPortTrace_regX (hA : PassiveBoundsStatement) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
        Tendsto (fun n => ∫ ω, freshPortTrace b E (regX X n) ω ∂freshLaw W b) atTop
          (𝓝 (∫ ω, freshPortTrace b E X ω ∂freshLaw W b)) := by
  obtain ⟨C, W₀, hm⟩ := hA.moments b hb0 hb κ hκ 1 le_rfl
  refine ⟨max W₀ 1, fun W hW E hE X hY => ?_⟩
  have hW1 : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW0 : 1 ≤ W := le_trans (le_max_right _ _) hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hdet := (hm W hW1 E hE _ (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hY).1
  refine tendsto_integral_of_dominated_convergence (fun _ => (etaZ b E)⁻¹)
    (fun n => (measurable_freshPortTrace_comp b E measurable_const measurable_id).aestronglyMeasurable)
    (integrable_const _) (fun n => (ae_layer_herm b).mono fun ω hA =>
      norm_freshPortTrace_le hb0 hb h1 h2 (passiveY_regX_posSemidef hY n) ω hA) ?_
  filter_upwards [ae_all_iff.2 fun n => ae_isUnit_layerF hb hW0 E (regX X n),
    ae_isUnit_layerF hb hW0 E X, hdet] with ω hn h0 hd
  have e : ∀ Y : Matrix (Fin W) (Fin W) ℂ, IsUnit (layerF E Y ω) →
      freshPortTrace b E Y ω = (W : ℂ)⁻¹ * ∑ x, gRes b E Y ω (port x) (port x) :=
    fun Y hF => freshPortTrace_eq_layer b E Y ω hF
  simp only [e _ (hn _), e _ h0]
  have hM := ((continuous_layerMatrix_X E (boundaryZ b E) ω).tendsto X).comp (tendsto_regX X)
  have hG := tendsto_matrix_inv hM hd
  have hc : Continuous fun M : LayerMat W => (W : ℂ)⁻¹ * ∑ x, M (port x) (port x) :=
    continuous_const.mul (continuous_finsetSum _ fun x _ =>
      (continuous_apply _).comp (continuous_apply _))
  exact (hc.tendsto _).comp hG

/-- **`PassiveMeanStep` from `PassiveBoundsStatement`.** Strictly passive inputs:
`passiveMeanEquationsStrict_holds` and `passiveMean_stability`; general passive inputs: the
regularization `X - i/(n+1)` (`tendsto_jet0_regX`, `tendsto_integral_freshPortTrace_regX`). -/
theorem passiveMeanStep_holds (hA : PassiveBoundsStatement) : PassiveMeanStep := by
  intro b hb0 hb κ hκ
  obtain ⟨Cv, C, W₀, hCv, hC, hEq⟩ := passiveMeanEquationsStrict_holds hA b hb0 hb κ hκ
  obtain ⟨d₀, ρ, C', ε₀, hd₀, hρ0, hρ1, hC', hε₀, hst⟩ := passiveMean_stability hb0 hb hκ hCv
  obtain ⟨W₂, hlim⟩ := tendsto_integral_freshPortTrace_regX hA hb0 hb hκ
  refine ⟨d₀ / 2, ρ, C' * C, max (max W₀ W₂) (⌈C / ε₀⌉₊ + 1), by positivity, hρ0, hρ1,
    mul_nonneg hC' hC, ?_⟩
  intro W hW E hE X hY hX
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW2⟩, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hε : C / (W : ℝ) ^ 2 ≤ ε₀ := by
    have hc := Nat.le_ceil (C / ε₀)
    have hc' : ((⌈C / ε₀⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈C / ε₀⌉₊ ≤ W)
    have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
    have h1' : C / ε₀ ≤ (W : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε₀] at h1'
    linarith
  -- strictly passive inputs
  have hstrict : ∀ Z : Matrix (Fin W) (Fin W) ℂ, (passiveY Z).PosDef → jetDistance0 b E Z ≤ d₀ →
      ‖(∫ ω, freshPortTrace b E Z ω ∂freshLaw W b) - matchedA E‖ ≤
        ρ * jetDistance0 b E Z + C' * C / (W : ℝ) ^ 2 := by
    intro Z hZ hdZ
    obtain ⟨v, hv0, hvC, hs, hr⟩ := hEq W hW0 E hE Z hZ
    have := hst W E hE Z hZ.posSemidef v _ (C / (W : ℝ) ^ 2) hv0 hvC hs hr (by positivity) hε hdZ
    calc _ ≤ ρ * jetDistance0 b E Z + C' * (C / (W : ℝ) ^ 2) := this
      _ = ρ * jetDistance0 b E Z + C' * C / (W : ℝ) ^ 2 := by ring
  -- the limit along `X - i/(n+1)`
  have hj := tendsto_jet0_regX hb0 hb h1 h2 hY
  have hev : ∀ᶠ n in atTop, jetDistance0 b E (regX X n) ≤ d₀ :=
    hj.eventually (ge_mem_nhds (by linarith))
  have hL := ((hlim W hW2 E hE X hY).sub_const (matchedA E)).norm
  have hR := (hj.const_mul ρ).add_const (C' * C / (W : ℝ) ^ 2)
  exact le_of_tendsto_of_tendsto hL hR (hev.mono fun n hn =>
    hstrict _ (passiveY_regX_posDef hY n) hn)

/-- **The passive initial scalar lemma** from the passive bounds and the fluctuation step. -/
theorem passiveInitialScalar_holds_of_fluctuation (hMT : MatchedTracesContract)
    (hPB : PassiveBoundsStatement) (hFl : PassiveFluctuationStep) :
    PassiveInitialScalarContract :=
  passiveInitialScalar_holds hMT hPB (passiveMeanStep_holds hPB) hFl

end BlockBand.Transmission.PathScalar
