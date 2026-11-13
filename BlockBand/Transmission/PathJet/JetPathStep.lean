module

public import BlockBand.Transmission.PathJet.PathRec

/-!
# The jet recursion along the unabsorbed near-end-grown path (one step, almost surely)

`pathJetV b E s W j ω = ‖-W⁻¹Tr R_j² - s‖` is a measurable version of `δ_{1,j}`
(`pathJet1_ae_eq`, `measurable_pathJetV`); `pathJetV ≤ M = η_κ⁻² + 2` (`ae_pathJetV_le`).

`ae_jet_step`: with the jet mean step (`ρ₁, C₂, C, d₀`) at width `W`, almost surely for every
`j ≥ 1`,
`δ_{1,j+1} ≤ ρ₁δ_{1,j} + (C₂ + M/d₀)δ_{0,j} + C/W² + ξ_{j+1}`,
`ξ_{j+1} = stepFluctOf (jetFun b E) b E 0 j` the centred fresh jet. Off the domain
`δ_{0,j} ≤ d₀` the bound `δ_{1,j+1} ≤ M ≤ (M/d₀)δ_{0,j}` is used, so the recursion needs no
stopping. The recursion starts at `j = 1` (`pathX 0 = 0` is not a step of the recursion); the
start term is paid by `δ_{1,1} ≤ M`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- A measurable version of `δ_{1,j}`. -/
def pathJetV (b E : ℝ) (s : ℂ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  ‖-crossTr (pathX b E W j ω) (boundaryZ b E) (boundaryZ b E) - s‖

/-- The deterministic jet bound `M = η_κ⁻² + 2`. -/
def jetM (b κ : ℝ) : ℝ := (etaLow b κ)⁻¹ ^ 2 + 2

theorem measurable_crossTr_mat (ζ : ℂ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => crossTr X ζ ζ := by
  have hR : Measurable fun X : Matrix (Fin W) (Fin W) ℂ => (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ := by
    refine Bridge.measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
    simp only [Matrix.sub_apply]
    exact measurable_const.sub measurable_id.eval_matrix
  simp only [crossTr_self_eq, Matrix.trace, Matrix.diag]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (measurable_matrix_mul' hR hR).eval_matrix)

theorem measurable_pathX (b E : ℝ) (j : ℕ) : Measurable (pathX b E W j) := by
  have : pathX b E W j = pastX b E (fun _ => 0) W j ∘ pastCoords W j := by
    funext ω; simp only [Function.comp, pathX, pathNearSchur_eq_past]
  rw [this]; exact (measurable_pastX b E _ j).comp (measurable_pastCoords W j)

theorem measurable_pathJetV (b E : ℝ) (s : ℂ) (j : ℕ) : Measurable (pathJetV b E s W j) :=
  (((measurable_crossTr_mat _).comp (measurable_pathX b E j)).neg.sub measurable_const).norm

theorem jetDistance1_eq_crossTr {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (s : ℂ)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    jetDistance1 b E s X = ‖-crossTr X (boundaryZ b E) (boundaryZ b E) - s‖ := by
  rw [jetDistance1]
  change ‖deriv (stieltjes X) (boundaryZ b E) - s‖ = _
  rw [deriv_stieltjes hY (Bridge.boundaryZ_im_pos hb h1 h2)]

theorem pathJet1_ae_eq {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (j : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, pathJet1 b E s W j ω = pathJetV b E s W j ω := by
  filter_upwards [ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb h1 h2] with ω hP
  exact jetDistance1_eq_crossTr hb h1 h2 s (pathNearSchur_passive hP j)

theorem crossTr_jet_le {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ‖-crossTr X (boundaryZ b E) (boundaryZ b E) - s‖ ≤ jetM b κ := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hz := Bridge.boundaryZ_im_pos (by linarith : b < 1) h1 h2
  have hc := norm_crossTr_le_sq hY hz
  have hηl := etaLow_pos (by linarith : b < 1) hκ
  have hη : etaLow b κ ≤ (boundaryZ b E).im := etaLow_le (by linarith) hκ hE
  have hs2 : ‖s‖ ≤ 2 := hs.2.trans (by rw [dStar, div_le_iff₀ (by linarith)]; linarith)
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, jetM]
  have : (boundaryZ b E).im⁻¹ ^ 2 ≤ (etaLow b κ)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ hηl hη) 2
  linarith

theorem ae_pathJetV_le {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s) (j : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, pathJetV b E s W j ω ≤ jetM b κ := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  filter_upwards [ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) (by linarith) h1 h2]
    with ω hP
  exact crossTr_jet_le hb0 hb hκ hE hs (pathNearSchur_passive hP j)

theorem stepInput_zero (b E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    stepInput b E (fun _ => 0) W j (pastCoords W j ω) = pathX b E W j ω := by
  rw [stepInput, ← pathNearSchur_eq_past]
  simp [layerAbsorption]

theorem integral_jetFun_eq {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ∫ ω, jetFun b E X ω ∂freshLaw W b = ∫ ω, freshJet b E X ω ∂freshLaw W b :=
  integral_congr_ae ((ae_layer_herm b).mono fun _ hA => (freshJet_eq_jetFun hb h1 h2 hY hA).symm)

/-- **One jet step, almost surely.** -/
theorem ae_jet_step {b κ E d₀ ρ₁ C₂ C : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s) (hd₀ : 0 < d₀)
    (hρ₁ : 0 ≤ ρ₁) (hC₂ : 0 ≤ C₂) (hC : 0 ≤ C) (hW1 : 1 ≤ W)
    (hmean : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDistance0 b E X ≤ d₀ →
      ‖(∫ ω, freshJet b E X ω ∂freshLaw W b) - s‖ ≤
        ρ₁ * jetDistance1 b E s X + C₂ * jetDistance0 b E X + C / (W : ℝ) ^ 2) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      pathJetV b E s W (j + 1) ω ≤ ρ₁ * pathJetV b E s W j ω +
        ((C₂ + jetM b κ / d₀) * jetDistance0 b E (pathX b E W j ω) + C / (W : ℝ) ^ 2 +
          stepFluctOf (jetFun b E) b E (fun _ => 0) j ω) := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  filter_upwards [ae_pathNearSchur_succ_abs hb h1 h2 hW1 (κ := fun _ => 0) (fun _ => le_rfl),
    ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) (by linarith) h1 h2] with ω hrec hP j hj
  set Xj := pathX b E W j ω
  have hYj : (passiveY Xj).PosSemidef := pathNearSchur_passive hP j
  have hrec' : pathX b E W (j + 1) ω = freshSchur E Xj (freshSample W j ω) := by
    have := hrec j hj
    simp only [layerAbsorption, zero_div, Complex.ofReal_zero, zero_mul, zero_smul, sub_zero] at this
    exact this
  have hy1 : pathJetV b E s W (j + 1) ω = ‖jetFun b E Xj (freshSample W j ω) - s‖ := by
    rw [pathJetV, hrec']; rfl
  have hξ : stepFluctOf (jetFun b E) b E (fun _ => 0) j ω =
      ‖jetFun b E Xj (freshSample W j ω) - ∫ f, jetFun b E Xj f ∂freshLaw W b‖ := by
    rw [stepFluctOf, stepPhiOf, stepInput_zero]
  have hyj : pathJetV b E s W j ω = jetDistance1 b E s Xj :=
    (jetDistance1_eq_crossTr (by linarith) h1 h2 s hYj).symm
  have hδ0 : 0 ≤ jetDistance0 b E Xj := norm_nonneg _
  have hM0 : 0 ≤ jetM b κ := by unfold jetM; positivity
  have hξ0 : 0 ≤ stepFluctOf (jetFun b E) b E (fun _ => 0) j ω := norm_nonneg _
  have hy0 : 0 ≤ pathJetV b E s W j ω := norm_nonneg _
  have hCW : 0 ≤ C / (W : ℝ) ^ 2 := by positivity
  have hMd : 0 ≤ jetM b κ / d₀ * jetDistance0 b E Xj := by positivity
  by_cases hd : jetDistance0 b E Xj ≤ d₀
  · have hm := hmean Xj hYj hd
    rw [← integral_jetFun_eq (by linarith) h1 h2 hYj] at hm
    have htri : pathJetV b E s W (j + 1) ω ≤
        ‖(∫ f, jetFun b E Xj f ∂freshLaw W b) - s‖ + stepFluctOf (jetFun b E) b E (fun _ => 0) j ω := by
      rw [hy1, hξ]
      have := norm_add_le (jetFun b E Xj (freshSample W j ω) - ∫ f, jetFun b E Xj f ∂freshLaw W b)
        ((∫ f, jetFun b E Xj f ∂freshLaw W b) - s)
      rw [show jetFun b E Xj (freshSample W j ω) - ∫ f, jetFun b E Xj f ∂freshLaw W b +
        ((∫ f, jetFun b E Xj f ∂freshLaw W b) - s) = jetFun b E Xj (freshSample W j ω) - s by ring]
        at this
      linarith
    rw [hyj]
    nlinarith [add_mul C₂ (jetM b κ / d₀) (jetDistance0 b E Xj)]
  · push Not at hd
    have hbd : pathJetV b E s W (j + 1) ω ≤ jetM b κ := by
      rw [pathJetV, hrec']
      exact crossTr_jet_le hb0 hb hκ hE hs (PathScalar.passiveY_freshSchur E hYj _
        (by
          have := hP.herm j
          simpa [freshSample] using this))
    have : jetM b κ ≤ jetM b κ / d₀ * jetDistance0 b E Xj := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd₀]
      exact mul_le_mul_of_nonneg_left hd.le hM0
    have : 0 ≤ ρ₁ * pathJetV b E s W j ω := mul_nonneg hρ₁ hy0
    nlinarith [add_mul C₂ (jetM b κ / d₀) (jetDistance0 b E Xj), mul_nonneg hC₂ hδ0]

end BlockBand.Transmission.PathJet
