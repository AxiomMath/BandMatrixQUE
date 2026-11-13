module

public import BlockBand.Transmission.Absorbed.JetStep
public import BlockBand.Transmission.Absorbed.JetMoments
public import BlockBand.Transmission.LengthUniform.Jet

/-!
# Absorbed jet-distance moments hold

`absorbedJetMoments_holds`: `AbsorbedJetMoments` from the matched-traces and Gaussian layer
hypotheses.

Proof: `LengthUniform.passiveJetMomentsUniform_of` + `lengthUniform_jet_of` along the
absorbed path, profile bound `K` (from `IsAbsorptionProfile κ`):
* `δ₀`: `absorbedDeltaUniform_holds` (`C₀` before `T`, uniform in `0 ≤ κ ≤ K`);
* `δ₁`: `eLpNorm_linrec` with the absorbed step `ae_abs_jet_step` (`JetStep`): ratio
  `ρ = max ρ₁ ½`, forcing `(C₂ + M/d₀)δ₀ + jetC/W² + ξ^κ`, `‖ξ^κ‖_p ≤ C_f/W` by
  `eLpNorm_stepFluctOf_le` (valid for any `κ ≥ 0`) and `jetFun_fluct`;
* start `δ₁(X_1) ≤ M`, `ρ^{r-1}M ≤ 2M/W` once `r ≥ εW ≥ log W/log(1/ρ)`.
Constant `C = C₀ + 2M + ((C₂ + M/d₀)C₀ + jetC + C_f)/(1-ρ)`, chosen before `T`; `T` enters
`W₀` only. So the quantifier order `∃ C, ∀ T, ∃ W₀` of the statement holds: the absorption adds only
`O(K/W²)` per step to a contracting recursion and does not accumulate over the length.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PathJet BlockBand.Transmission.LengthUniform
open scoped ENNReal ComplexOrder

/-- The final scalar step: `C₀/W + ρ^{r-1}M + B/W/(1-ρ) ≤ (C₀ + 2M + B/(1-ρ))/W`. -/
theorem jet_final_arith {C₀ M B ρ x P : ℝ} (hM : 0 ≤ M) (hx : 0 < x)
    (hP : P ≤ 2 / x) :
    C₀ / x + (P * M + B / x / (1 - ρ)) ≤ (C₀ + 2 * M + B / (1 - ρ)) / x := by
  have h1 : P * M ≤ 2 / x * M := mul_le_mul_of_nonneg_right hP hM
  have e : (C₀ + 2 * M + B / (1 - ρ)) / x = C₀ / x + 2 / x * M + B / x / (1 - ρ) := by
    field_simp
  rw [e]; linarith

/-- `AbsorbedJetMoments` from `MatchedTracesContract`, `GaussianAbsorptionContract`,
`GaussianLpGradient`. -/
theorem absorbedJetMoments_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : AbsorbedJetMoments := by
  intro b hb0 hb κI ε p hκI hε hp κ hκ
  obtain ⟨-, hκ0, K, hKb⟩ := hκ
  have hκK : ∀ t, 0 ≤ κ t ∧ κ t ≤ K := fun t => ⟨hκ0 t, hKb t⟩
  have hK : 0 ≤ K := (hκ0 0).trans (hKb 0)
  obtain ⟨d₀, ρ₁, C₂, Cm, W₀m, hd₀, hρ₁0, hρ₁1, hC₂, hCm, hmean⟩ :=
    passiveJetMeanStep_holds (PassiveLayer.passiveBounds_holds hGA hLp) b hb0 hb κI hκI
  obtain ⟨Cf, W₀f, hCf, hfl⟩ := passiveJetFluctuationStep_holds hGA hLp b hb0 hb κI hκI p hp
  obtain ⟨C₀, hC₀0, hδT⟩ := absorbedDeltaUniform_holds hMT hGA hLp b hb0 hb κI K p hκI hK hp
  have hb1 : b < 1 := by linarith
  have hρh : (1 : ℝ) / 2 ≤ max ρ₁ (1 / 2) := le_max_right _ _
  have hρ1 : max ρ₁ (1 / 2) < 1 := max_lt hρ₁1 (by norm_num)
  have hρ0 : 0 ≤ max ρ₁ (1 / 2) := by linarith
  have hM : 0 ≤ jetM b κI := by
    unfold jetM; have := etaLow_pos hb1 hκI; positivity
  have hC₃ : 0 ≤ C₂ + jetM b κI / d₀ := by positivity
  have hCj := jetC_nonneg hb1 hκI hd₀ hρ₁0 hC₂ hCm hK
  set Cj := jetC b κI d₀ ρ₁ C₂ Cm K
  set B := (C₂ + jetM b κI / d₀) * C₀ + Cj + Cf
  refine ⟨C₀ + 2 * jetM b κI + B / (1 - max ρ₁ (1 / 2)), fun T => ?_⟩
  obtain ⟨W₀p, hPIS⟩ := hδT T
  obtain ⟨W₁, hlog⟩ := log_le_eps_mul (1 / Real.log (1 / max ρ₁ (1 / 2))) hε
  refine ⟨max (max W₀m W₀f) (max W₀p (max W₁ 1)), ?_⟩
  intro W hW E hE s hs r hεr hrT
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWm, hWf⟩, hWp, hW₁, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκI hE
  have hx : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) < r := lt_of_lt_of_le (mul_pos hε hx) hεr
    exact_mod_cast this
  have hrlog := (hlog W hW₁).trans hεr
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hp0 : 0 < p := by linarith
  -- `δ₀` along the absorbed path 
  have hδ0 : ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ T * W →
      eLpNorm (fun ω => jetDistance0 b E (pathNearSchur b E κ W j ω)) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤ ENNReal.ofReal (C₀ / W) :=
    fun j hj hjT => hPIS W hWp E hE κ hκK j hj hjT
  -- the absorbed recursion for `δ₁`
  have hΦ : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      jetFun b E q.1 q.2 := measurable_jetFun_comp b E measurable_fst measurable_snd
  have hae := ae_abs_jet_step hb0 hb hκI hE hs hd₀ hρ₁0 hC₂ hCm hW1 hκK (hmean W hWm E hE s hs)
  have hstep : ∀ j, 1 ≤ j → j < r → ∀ᵐ ω ∂growthPathLaw W b,
      absJetV b E κ s W (j + 1) ω ≤ max ρ₁ (1 / 2) * absJetV b E κ s W j ω +
        ((C₂ + jetM b κI / d₀) * jetDistance0 b E (pathNearSchur b E κ W j ω) +
          Cj / (W : ℝ) ^ 2 + stepFluctOf (jetFun b E) b E κ j ω) := by
    intro j hj _
    filter_upwards [hae] with ω hω
    have h := hω j hj
    have := mul_le_mul_of_nonneg_right (le_max_left ρ₁ (1 / 2))
      (norm_nonneg (-crossTr (pathNearSchur b E κ W j ω) (boundaryZ b E) (boundaryZ b E) - s))
    change _ ≤ ρ₁ * ‖_‖ + _ at h
    change _ ≤ max ρ₁ (1 / 2) * ‖_‖ + _
    linarith
  have hy1 : eLpNorm (absJetV b E κ s W 1) (ENNReal.ofReal p) (growthPathLaw W b) ≤
      ENNReal.ofReal (jetM b κI) := by
    refine (eLpNorm_le_of_ae_bound (C := jetM b κI)
      (measurable_absJetV b E κ s 1).aestronglyMeasurable
      ((ae_absJetV_le hb0 hb hκI hE hs hκ0 1).mono fun ω hω => by
        rwa [Real.norm_of_nonneg (by unfold absJetV; exact norm_nonneg _)])).trans (le_of_eq ?_)
    simp
  have hBc : 0 ≤ B / W := by positivity
  have he : ∀ j, 1 ≤ j → j < r →
      eLpNorm (fun ω => (C₂ + jetM b κI / d₀) * jetDistance0 b E (pathNearSchur b E κ W j ω) +
        Cj / (W : ℝ) ^ 2 + stepFluctOf (jetFun b E) b E κ j ω) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤ ENNReal.ofReal (B / W) := by
    intro j hj hjr
    have hjT : (j : ℝ) ≤ T * W := le_trans (by exact_mod_cast hjr.le) hrT
    have hξ := eLpNorm_stepFluctOf_le hΦ hb1 h1 h2 hp0 (κ := κ) hκ0 j (C := Cf / W)
      (jetFun_fluct hb0 hb hκI hfl hWf hE)
    refine (eLpNorm_err_le hp hC₃ (by positivity) (hδ0 j hj hjT) hξ (by positivity)
      (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    have : Cj / (W : ℝ) ^ 2 ≤ Cj / W :=
      div_le_div_of_nonneg_left hCj hx (by nlinarith)
    simp only [B, add_div, mul_div_assoc]
    linarith
  have hrec := eLpNorm_linrec (growthPathLaw W b) (y := absJetV b E κ s W)
    (e := fun j ω => (C₂ + jetM b κI / d₀) * jetDistance0 b E (pathNearSchur b E κ W j ω) +
      Cj / (W : ℝ) ^ 2 + stepFluctOf (jetFun b E) b E κ j ω)
    hp1 hρ0 hρ1 hM hBc (fun j ω => norm_nonneg _)
    (fun j => (measurable_absJetV b E κ s j).aestronglyMeasurable) hstep hy1 he r hr1 le_rfl
  have hJ : eLpNorm (fun ω => jetDistance1 b E s (pathNearSchur b E κ W r ω)) (ENNReal.ofReal p)
      (growthPathLaw W b) = eLpNorm (absJetV b E κ s W r) (ENNReal.ofReal p) (growthPathLaw W b) :=
    eLpNorm_congr_ae (absJet1_ae_eq hb1 h1 h2 hκ0 s r)
  have hpow := pow_le_two_div hρh hρ1 hW1 hr1 hrlog
  rw [hJ]
  refine (add_le_add (hδ0 r hr1 hrT) hrec).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (jet_final_arith (ρ := max ρ₁ (1 / 2)) hM hx hpow)

end BlockBand.Transmission.Absorbed
