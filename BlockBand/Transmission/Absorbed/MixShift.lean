module

public import BlockBand.Transmission.Absorbed.MixPath
public import BlockBand.Transmission.LawFinite.InjectionMean

/-!
# Moments at the absorbed input of the source-mixing recursion

At a passive `X`, `X' = X − iε`, `0 ≤ ε ≤ K/W²`, `E ∈ bulkInterval κI`, `W ≥ K/η_L`
(so `s = ε/η ≤ 1`), `η_L = etaLow b κI` (`abs_shift_facts`):
* `q(X') ≤ 4q(X) + K/η_L²` (`passiveMass_absorb_le`);
* `δ₀(X') ≤ δ₀(X) + (K/η_L²)/W` (`jetDistance0_absorb_le`);
* `δ₁(X') ≤ δ₁(X) + (2K/η_L³)/W` (`jetDistance1_absorb_le`);
* `mixErr(ε, q(X)) ≤ cMix(η_L⁻¹, K)(q(X) + 1)/√W` (`sqrtW_mixErr_le`).
`abs_input_moments` transfers `L^{2p}` moments of `q, δ₀, δ₁` at `X_j` to the fresh-layer input
`absIn j = X_j − iε_j` along `growthPathLaw W b`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LawFinite
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- **The deterministic input shifts** at `ε ≤ K/W²`, `W ≥ K/η_L`. -/
theorem abs_shift_facts {b κI E K ε : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI)
    (hE : E ∈ bulkInterval κI) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (s : ℂ) (hK : 0 ≤ K) (hW1 : 1 ≤ W) (hWK : K / etaLow b κI ≤ W) (hε : 0 ≤ ε)
    (hεK : ε ≤ K / (W : ℝ) ^ 2) :
    passiveMass b E (absorbedInput X ε) ≤ 4 * passiveMass b E X + K / etaLow b κI ^ 2 ∧
    jetDistance0 b E (absorbedInput X ε) ≤ jetDistance0 b E X + K / etaLow b κI ^ 2 / W ∧
    mx_jet1 b E s (absorbedInput X ε) ≤ mx_jet1 b E s X + 2 * K / etaLow b κI ^ 3 / W ∧
    mixErr b E ε (passiveMass b E X) W ≤
      cMix (etaLow b κI)⁻¹ K * (passiveMass b E X + 1) / Real.sqrt W := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκI hE
  have hb1 : b < 1 := by linarith
  have hηL := etaLow_pos hb1 hκI
  have hηLe : etaLow b κI ≤ etaZ b E := etaLow_le hb1 hκI hE
  have hη := etaZ_pos b E hb1 h1 h2
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hY' := passiveY_absorbedInput hY hε
  have hq0 := passiveMass_nonneg b E hY
  have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
  -- `s = ε/η ≤ 1`
  have hs1 : ε / etaZ b E ≤ 1 := by
    rw [div_le_one hη]
    have h3 : K / (W : ℝ) ^ 2 ≤ etaLow b κI := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hηL] at hWK
      nlinarith
    linarith
  have hs0 : 0 ≤ ε / etaZ b E := div_nonneg hε hη.le
  -- `δ₀`, `δ₁` shifts at `/W²`, then `≤ /W`
  have hdW : ∀ a : ℝ, 0 ≤ a → a / (W : ℝ) ^ 2 ≤ a / W := fun a ha =>
    div_le_div_of_nonneg_left ha hW0 hWW
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm := passiveMass_absorb_le hb0 hb h1 h2 hY hε
    have hsq : (1 + ε / etaZ b E) ^ 2 ≤ 4 := by nlinarith
    have hεW : ε * W / etaZ b E ^ 2 ≤ K / etaLow b κI ^ 2 := by
      have h3 : ε * W ≤ K := by
        have h5 := mul_le_mul_of_nonneg_right hεK hW0.le
        have h6 : K / (W : ℝ) ^ 2 * W ≤ K := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
        linarith
      calc ε * W / etaZ b E ^ 2 ≤ K / etaZ b E ^ 2 :=
            div_le_div_of_nonneg_right h3 (by positivity)
        _ ≤ K / etaLow b κI ^ 2 :=
            div_le_div_of_nonneg_left hK (by positivity) (pow_le_pow_left₀ hηL.le hηLe 2)
    have := mul_le_mul_of_nonneg_right hsq hq0
    linarith
  · have h0 : jetDistance0 b E (absorbedInput X ε) ≤ jetDistance0 b E X + ε / etaZ b E ^ 2 :=
      jetDistance0_absorb_le hb0 hb h1 h2 hY hε
    linarith [eps_div_pow_le (n := 2) hε hεK hηL hηLe, hdW (K / etaLow b κI ^ 2) (by positivity)]
  · rw [← mx_jet1_eq hb1 h1 h2 s hY, ← mx_jet1_eq hb1 h1 h2 s hY']
    have h0 := jetDistance1_absorb_le hb0 hb h1 h2 hY hε s
    have h3 := eps_div_pow_le (n := 3) (mul_nonneg zero_le_two hε)
      (by have := mul_le_mul_of_nonneg_left hεK zero_le_two; rwa [← mul_div_assoc] at this)
      hηL hηLe
    have h4 := hdW (2 * K / etaLow b κI ^ 3) (by positivity)
    linarith
  · have h := sqrtW_mixErr_le (W := W) hη (inv_anti₀ hηL hηLe) hK hW1 hε hεK hs1 hq0
    have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
    rw [le_div_iff₀ hsW, mul_comm]; exact h

/-- `‖k·f + c‖_p ≤ k a + c` on a probability space. -/
theorem eLpNorm_affine_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : Ω → ℝ} {k a c : ℝ} (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hf : eLpNorm f p μ ≤ ENNReal.ofReal a) (ha : 0 ≤ a) :
    eLpNorm (fun ω => k * f ω + c) p μ ≤ ENNReal.ofReal (k * a + c) := by
  have hc' : eLpNorm (fun _ : Ω => c) p μ ≤ ENNReal.ofReal c := by
    refine (eLpNorm_le_of_ae_bound (C := c) aestronglyMeasurable_const (ae_of_all _ fun _ => by
      rw [Real.norm_of_nonneg hc])).trans (le_of_eq ?_)
    simp
  exact mx_add_le hp (mul_nonneg hk ha) hc (mx_const_mul_le hk hf) hc'

/-- **Moments at the fresh-layer input `absIn j = X_j − iε_j`** from moments at `X_j`. -/
theorem abs_input_moments {b κI E K : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI)
    (hE : E ∈ bulkInterval κI) {κ : ℝ → ℝ} (hκ : ∀ t, 0 ≤ κ t ∧ κ t ≤ K) (s : ℂ)
    (hW1 : 1 ≤ W) (hWK : K / etaLow b κI ≤ W) (j : ℕ) {p Kq D : ℝ} (hp : 1 ≤ p) (hKq : 0 ≤ Kq)
    (hD : 0 ≤ D)
    (hq : eLpNorm (fun ω => passiveMass b E (pathNearSchur b E κ W j ω)) (ENNReal.ofReal p)
      (growthPathLaw W b) ≤ ENNReal.ofReal Kq)
    (hδ0 : eLpNorm (fun ω => jetDistance0 b E (pathNearSchur b E κ W j ω)) (ENNReal.ofReal p)
      (growthPathLaw W b) ≤ ENNReal.ofReal (D / W))
    (hδ1 : eLpNorm (fun ω => mx_jet1 b E s (pathNearSchur b E κ W j ω)) (ENNReal.ofReal p)
      (growthPathLaw W b) ≤ ENNReal.ofReal (D / W)) :
    eLpNorm (fun ω => passiveMass b E (absIn b E κ W j ω)) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤ ENNReal.ofReal (4 * Kq + K / etaLow b κI ^ 2) ∧
      eLpNorm (fun ω => jetDistance0 b E (absIn b E κ W j ω)) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤ ENNReal.ofReal ((D + K / etaLow b κI ^ 2 + 2 * K / etaLow b κI ^ 3) / W) ∧
      eLpNorm (fun ω => mx_jet1 b E s (absIn b E κ W j ω)) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤ ENNReal.ofReal ((D + K / etaLow b κI ^ 2 + 2 * K / etaLow b κI ^ 3) / W) := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκI hE
  have hb1 : b < 1 := by linarith
  have hηL := etaLow_pos hb1 hκI
  have hκ0 : ∀ t, 0 ≤ κ t := fun t => (hκ t).1
  have hK : 0 ≤ K := (hκ 0).1.trans (hκ 0).2
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨hε0, hεK⟩ := layerAbsorption_succ_bounds (W := W) hκ j
  have hfacts : ∀ᵐ ω ∂growthPathLaw W b,
      passiveMass b E (absIn b E κ W j ω) ≤
          4 * passiveMass b E (pathNearSchur b E κ W j ω) + K / etaLow b κI ^ 2 ∧
        jetDistance0 b E (absIn b E κ W j ω) ≤
          jetDistance0 b E (pathNearSchur b E κ W j ω) + K / etaLow b κI ^ 2 / W ∧
        mx_jet1 b E s (absIn b E κ W j ω) ≤
          mx_jet1 b E s (pathNearSchur b E κ W j ω) + 2 * K / etaLow b κI ^ 3 / W := by
    filter_upwards [ae_passiveSample W hκ0 hb1 h1 h2] with ω hP
    have hf := abs_shift_facts hb0 hb hκI hE (pathNearSchur_passive hP j) s hK hW1 hWK hε0 hεK
    rw [absIn, stepInput_eq_absorbedInput]
    exact ⟨hf.1, hf.2.1, hf.2.2.1⟩
  have hY' : ∀ᵐ ω ∂growthPathLaw W b, (passiveY (absIn b E κ W j ω)).PosSemidef := by
    filter_upwards [ae_passiveSample W hκ0 hb1 h1 h2] with ω hP
    rw [absIn, stepInput_eq_absorbedInput]
    exact passiveY_absorbedInput (pathNearSchur_passive hP j) hε0
  have hm := measurable_absIn b E κ (W := W) j
  refine ⟨?_, ?_, ?_⟩
  · refine (eLpNorm_mono_ae_real ((measurable_passiveMass b E).comp hm).aestronglyMeasurable ?_).trans
      (eLpNorm_affine_le hp1 (by norm_num) (by positivity) hq hKq)
    filter_upwards [hfacts, hY'] with ω hω hY
    change ‖passiveMass b E (absIn b E κ W j ω)‖ ≤ _
    rw [Real.norm_of_nonneg (passiveMass_nonneg b E hY)]; exact hω.1
  · refine (eLpNorm_mono_ae_real ((measurable_jetDistance0 b E).comp hm).aestronglyMeasurable
      (g := fun ω => 1 * jetDistance0 b E (pathNearSchur b E κ W j ω) +
        (K / etaLow b κI ^ 2 / W + 2 * K / etaLow b κI ^ 3 / W)) ?_).trans
      ((eLpNorm_affine_le hp1 zero_le_one (by positivity) hδ0 (by positivity)).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by ring))))
    filter_upwards [hfacts] with ω hω
    change ‖jetDistance0 b E (absIn b E κ W j ω)‖ ≤ _
    rw [Real.norm_of_nonneg (by unfold jetDistance0; exact norm_nonneg _)]
    have : 0 ≤ 2 * K / etaLow b κI ^ 3 / W := by positivity
    linarith [hω.2.1]
  · refine (eLpNorm_mono_ae_real ((measurable_mx_jet1 b E s).comp hm).aestronglyMeasurable
      (g := fun ω => 1 * mx_jet1 b E s (pathNearSchur b E κ W j ω) +
        (K / etaLow b κI ^ 2 / W + 2 * K / etaLow b κI ^ 3 / W)) ?_).trans
      ((eLpNorm_affine_le hp1 zero_le_one (by positivity) hδ1 (by positivity)).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by ring))))
    filter_upwards [hfacts] with ω hω
    change ‖mx_jet1 b E s (absIn b E κ W j ω)‖ ≤ _
    rw [Real.norm_of_nonneg (by unfold mx_jet1; exact norm_nonneg _)]
    have : 0 ≤ K / etaLow b κI ^ 2 / W := by positivity
    linarith [hω.2.2]

end BlockBand.Transmission.Absorbed
