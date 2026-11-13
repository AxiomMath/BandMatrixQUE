module

public import BlockBand.Transmission.Absorbed.ShiftJet
public import BlockBand.Transmission.Absorbed.Conductance
public import BlockBand.Transmission.PathJet.JetMomentsMain

/-!
# One jet step along the absorbed path, almost surely

Path `X_j = pathNearSchur b E κ W j`, profile `0 ≤ κ ≤ K`. The absorbed step
(`ae_pathNearSchur_succ_abs`) is `X_{j+1} = freshSchur E X'_j (fresh_j)` with
`X'_j = X_j − iε_j`, `0 ≤ ε_j ≤ K/W²`. The jet mean step holds at every passive input, so at
`X'_j`; `jetDistance1_absorb_le` (`δ₁(X') ≤ δ₁(X) + 2ε/η³`) and
`jetDistance0_absorb_le` (`δ₀(X') ≤ δ₀(X) + ε/η²`) move back to `X_j` at a cost `O(K/W²)`:

**`ae_abs_jet_step`**: a.s., for every `j ≥ 1`,
`δ₁(X_{j+1}) ≤ ρ₁δ₁(X_j) + (C₂ + M/d₀)δ₀(X_j) + jetC/W² + ξ^κ_{j+1}`,
`jetC = C + ρ₁·2K/η_L³ + (C₂ + M/d₀)K/η_L²`, `ξ^κ = stepFluctOf (jetFun b E) b E κ j`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PathJet BlockBand.Transmission.LawFinite
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- A measurable version of `δ₁(X^κ_j)` along the absorbed path. -/
def absJetV (b E : ℝ) (κ : ℝ → ℝ) (s : ℂ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  ‖-crossTr (pathNearSchur b E κ W j ω) (boundaryZ b E) (boundaryZ b E) - s‖

theorem measurable_absJetV (b E : ℝ) (κ : ℝ → ℝ) (s : ℂ) (j : ℕ) :
    Measurable (absJetV b E κ s W j) :=
  (((measurable_crossTr_mat _).comp (measurable_pathNearSchur' b E κ j)).neg.sub
    measurable_const).norm

theorem absJet1_ae_eq {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) {κ : ℝ → ℝ}
    (hκ : ∀ t, 0 ≤ κ t) (s : ℂ) (j : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b,
      jetDistance1 b E s (pathNearSchur b E κ W j ω) = absJetV b E κ s W j ω := by
  filter_upwards [ae_passiveSample W hκ hb h1 h2] with ω hP
  exact jetDistance1_eq_crossTr hb h1 h2 s (pathNearSchur_passive hP j)

theorem ae_absJetV_le {b κI E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI)
    (hE : E ∈ bulkInterval κI) {s : ℂ} (hs : IsStationaryJet b E s) {κ : ℝ → ℝ}
    (hκ : ∀ t, 0 ≤ κ t) (j : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, absJetV b E κ s W j ω ≤ jetM b κI := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκI hE
  filter_upwards [ae_passiveSample W hκ (by linarith) h1 h2] with ω hP
  exact crossTr_jet_le hb0 hb hκI hE hs (pathNearSchur_passive hP j)

/-- The constant of the absorbed jet step. -/
def jetC (b κI d₀ ρ₁ C₂ C K : ℝ) : ℝ :=
  C + ρ₁ * (2 * K / etaLow b κI ^ 3) + (C₂ + jetM b κI / d₀) * (K / etaLow b κI ^ 2)

theorem jetC_nonneg {b κI d₀ ρ₁ C₂ C K : ℝ} (hb : b < 1) (hκI : 0 < κI) (hd₀ : 0 < d₀)
    (hρ₁ : 0 ≤ ρ₁) (hC₂ : 0 ≤ C₂) (hC : 0 ≤ C) (hK : 0 ≤ K) : 0 ≤ jetC b κI d₀ ρ₁ C₂ C K := by
  have := etaLow_pos hb hκI
  have hM : 0 ≤ jetM b κI := by unfold jetM; positivity
  unfold jetC; positivity

/-- `ε/η^n ≤ (K/η_L^n)/W²` for `0 ≤ ε ≤ K/W²`, `η_L ≤ η`. -/
theorem eps_div_pow_le {ε K ηL η : ℝ} {n : ℕ} (hε : 0 ≤ ε) (hεK : ε ≤ K / (W : ℝ) ^ 2)
    (hηL : 0 < ηL) (hη : ηL ≤ η) : ε / η ^ n ≤ K / ηL ^ n / (W : ℝ) ^ 2 := by
  have h1 : ε / η ^ n ≤ ε / ηL ^ n :=
    div_le_div_of_nonneg_left hε (pow_pos hηL n) (pow_le_pow_left₀ hηL.le hη n)
  have h2 : ε / ηL ^ n ≤ K / (W : ℝ) ^ 2 / ηL ^ n :=
    div_le_div_of_nonneg_right hεK (pow_pos hηL n).le
  rw [div_right_comm] at h2
  linarith

/-- The absorption of step `j → j+1` lies in `[0, K/W²]`. -/
theorem layerAbsorption_succ_bounds {κ : ℝ → ℝ} {K : ℝ} (hκ : ∀ t, 0 ≤ κ t ∧ κ t ≤ K) (j : ℕ) :
    0 ≤ layerAbsorption W κ (j + 1) 0 ∧ layerAbsorption W κ (j + 1) 0 ≤ K / (W : ℝ) ^ 2 := by
  unfold layerAbsorption
  exact ⟨div_nonneg (hκ _).1 (sq_nonneg _), div_le_div_of_nonneg_right (hκ _).2 (sq_nonneg _)⟩

/-- The step input `stepInput κ j` is `X_j − iε_j`. -/
theorem stepInput_eq_absorbedInput (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) (ω : GrowthPath W) :
    stepInput b E κ W j (pastCoords W j ω) =
      absorbedInput (pathNearSchur b E κ W j ω) (layerAbsorption W κ (j + 1) 0) := by
  rw [stepInput, ← pathNearSchur_eq_past, absorbedInput]

/-- **One jet step along the absorbed path, almost surely.** -/
theorem ae_abs_jet_step {b κI E d₀ ρ₁ C₂ C K : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI)
    (hE : E ∈ bulkInterval κI) {s : ℂ} (hs : IsStationaryJet b E s) (hd₀ : 0 < d₀)
    (hρ₁ : 0 ≤ ρ₁) (hC₂ : 0 ≤ C₂) (hC : 0 ≤ C) (hW1 : 1 ≤ W) {κ : ℝ → ℝ}
    (hκ : ∀ t, 0 ≤ κ t ∧ κ t ≤ K)
    (hmean : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDistance0 b E X ≤ d₀ →
      ‖(∫ ω, freshJet b E X ω ∂freshLaw W b) - s‖ ≤
        ρ₁ * jetDistance1 b E s X + C₂ * jetDistance0 b E X + C / (W : ℝ) ^ 2) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      absJetV b E κ s W (j + 1) ω ≤ ρ₁ * absJetV b E κ s W j ω +
        ((C₂ + jetM b κI / d₀) * jetDistance0 b E (pathNearSchur b E κ W j ω) +
          jetC b κI d₀ ρ₁ C₂ C K / (W : ℝ) ^ 2 + stepFluctOf (jetFun b E) b E κ j ω) := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκI hE
  have hκ0 : ∀ t, 0 ≤ κ t := fun t => (hκ t).1
  have hb1 : b < 1 := by linarith
  have hηL := etaLow_pos hb1 hκI
  have hηLe : etaLow b κI ≤ etaZ b E := etaLow_le hb1 hκI hE
  filter_upwards [ae_pathNearSchur_succ_abs hb h1 h2 hW1 hκ0,
    ae_passiveSample W hκ0 hb1 h1 h2] with ω hrec hP j hj
  set X := pathNearSchur b E κ W j ω
  set ε := layerAbsorption W κ (j + 1) 0
  obtain ⟨hε0, hεK⟩ := layerAbsorption_succ_bounds (W := W) hκ j
  set X' := absorbedInput X ε
  have hY : (passiveY X).PosSemidef := pathNearSchur_passive hP j
  have hY' : (passiveY X').PosSemidef := passiveY_absorbedInput hY hε0
  have hrec' : pathNearSchur b E κ W (j + 1) ω = freshSchur E X' (freshSample W j ω) := hrec j hj
  have hy1 : absJetV b E κ s W (j + 1) ω = ‖jetFun b E X' (freshSample W j ω) - s‖ := by
    rw [absJetV, hrec']; rfl
  have hξ : stepFluctOf (jetFun b E) b E κ j ω =
      ‖jetFun b E X' (freshSample W j ω) - ∫ f, jetFun b E X' f ∂freshLaw W b‖ := by
    rw [stepFluctOf, stepPhiOf, stepInput_eq_absorbedInput]
  have hyj : absJetV b E κ s W j ω = jetDistance1 b E s X :=
    (jetDistance1_eq_crossTr hb1 h1 h2 s hY).symm
  -- the deterministic shifts, `O(K/W²)`
  have hd0s : jetDistance0 b E X' ≤ jetDistance0 b E X + K / etaLow b κI ^ 2 / (W : ℝ) ^ 2 := by
    have h0 : jetDistance0 b E X' ≤ jetDistance0 b E X + ε / etaZ b E ^ 2 :=
      jetDistance0_absorb_le hb0 hb h1 h2 hY hε0
    linarith [eps_div_pow_le (n := 2) hε0 hεK hηL hηLe]
  have hd1s : jetDistance1 b E s X' ≤
      jetDistance1 b E s X + 2 * K / etaLow b κI ^ 3 / (W : ℝ) ^ 2 := by
    have h0 := jetDistance1_absorb_le hb0 hb h1 h2 hY hε0 s
    suffices hh : 2 * ε / etaZ b E ^ 3 ≤ 2 * K / etaLow b κI ^ 3 / (W : ℝ) ^ 2 by linarith
    have := eps_div_pow_le (n := 3) (mul_nonneg zero_le_two hε0)
      (by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hεK zero_le_two) hηL hηLe
    simpa [mul_div_assoc] using this
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hM0 : 0 ≤ jetM b κI := by unfold jetM; positivity
  have hξ0 : 0 ≤ stepFluctOf (jetFun b E) b E κ j ω := norm_nonneg _
  have hy0 : 0 ≤ absJetV b E κ s W j ω := norm_nonneg _
  have hCW : 0 ≤ C / (W : ℝ) ^ 2 := by positivity
  have hMd : 0 ≤ jetM b κI / d₀ * jetDistance0 b E X := by positivity
  have hK0 : 0 ≤ K := (hκ 0).1.trans (hκ 0).2
  have ha0 : 0 ≤ K / etaLow b κI ^ 2 / (W : ℝ) ^ 2 := by positivity
  have hjc : jetC b κI d₀ ρ₁ C₂ C K / (W : ℝ) ^ 2 = C / (W : ℝ) ^ 2 +
      ρ₁ * (2 * K / etaLow b κI ^ 3 / (W : ℝ) ^ 2) +
      (C₂ + jetM b κI / d₀) * (K / etaLow b κI ^ 2 / (W : ℝ) ^ 2) := by
    unfold jetC; ring
  rw [hjc]
  set a₀ := K / etaLow b κI ^ 2 / (W : ℝ) ^ 2
  set a₁ := 2 * K / etaLow b κI ^ 3 / (W : ℝ) ^ 2
  have hMa : 0 ≤ jetM b κI / d₀ * a₀ := by positivity
  have hC2a : C₂ * jetDistance0 b E X' ≤ C₂ * jetDistance0 b E X + C₂ * a₀ := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hd0s hC₂
  by_cases hd : jetDistance0 b E X' ≤ d₀
  · have hm := hmean X' hY' hd
    rw [← integral_jetFun_eq hb1 h1 h2 hY'] at hm
    have htri : absJetV b E κ s W (j + 1) ω ≤
        ‖(∫ f, jetFun b E X' f ∂freshLaw W b) - s‖ + stepFluctOf (jetFun b E) b E κ j ω := by
      rw [hy1, hξ]
      have := norm_add_le (jetFun b E X' (freshSample W j ω) - ∫ f, jetFun b E X' f ∂freshLaw W b)
        ((∫ f, jetFun b E X' f ∂freshLaw W b) - s)
      rw [show jetFun b E X' (freshSample W j ω) - ∫ f, jetFun b E X' f ∂freshLaw W b +
        ((∫ f, jetFun b E X' f ∂freshLaw W b) - s) = jetFun b E X' (freshSample W j ω) - s by ring]
        at this
      linarith
    have hρa : ρ₁ * jetDistance1 b E s X' ≤ ρ₁ * absJetV b E κ s W j ω + ρ₁ * a₁ := by
      rw [← mul_add, hyj]; exact mul_le_mul_of_nonneg_left hd1s hρ₁
    nlinarith [add_mul C₂ (jetM b κI / d₀) (jetDistance0 b E X), add_mul C₂ (jetM b κI / d₀) a₀,
      mul_nonneg hC₂ ha0]
  · push Not at hd
    have hbd : absJetV b E κ s W (j + 1) ω ≤ jetM b κI := by
      rw [absJetV, hrec']
      exact crossTr_jet_le hb0 hb hκI hE hs (PathScalar.passiveY_freshSchur E hY' _
        (by
          have := hP.herm j
          simpa [freshSample] using this))
    have hMX : jetM b κI ≤ jetM b κI / d₀ * jetDistance0 b E X' := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd₀]
      exact mul_le_mul_of_nonneg_left hd.le hM0
    have hMX' : jetM b κI / d₀ * jetDistance0 b E X' ≤
        jetM b κI / d₀ * jetDistance0 b E X + jetM b κI / d₀ * a₀ := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left hd0s (by positivity)
    have : 0 ≤ ρ₁ * absJetV b E κ s W j ω := mul_nonneg hρ₁ hy0
    have : 0 ≤ ρ₁ * a₁ := mul_nonneg hρ₁ (by positivity)
    nlinarith [add_mul C₂ (jetM b κI / d₀) (jetDistance0 b E X), add_mul C₂ (jetM b κI / d₀) a₀,
      mul_nonneg hC₂ hδ0, mul_nonneg hC₂ ha0]

end BlockBand.Transmission.Absorbed
