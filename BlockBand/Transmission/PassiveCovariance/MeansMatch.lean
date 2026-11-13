module

public import BlockBand.Transmission.PassiveCovariance.MeansTransfer

/-!
# `MeansMatchMain` from `TauNear` and the three `MeanNear` statements

* **`meansMatchMain_of_near (hA) (hT) (hG) (hP) (hQ) : MeansMatchMain`**.

Error budget: each factor of the Level-0 products is within `c·ε` of its leading value
(`ε = δ + W⁻¹`, `δ = δ₀ + δ₁ + q/W`), so each product is within `c'ε`, each source within
`4c'ε/W`, and `τ̄·conj X₂ + X₁ - mainTensor` within `Cε/W = C(W⁻² + W⁻¹δ)`; the exact sum of the
leading values is `lead_eq_main`.

**`passiveCovariance_holds_of_near hGA hLp hP hT hG hα hQ : PassiveCovarianceContract`**: the
contract from the contract hypotheses and the four mean statements (`MeansNear`), which are
hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

theorem leadConst_nonneg (b E : ℝ) (s : ℂ) : 0 ≤ leadConst b E s := by
  have := leadCoef_nonneg b E s 0; have := leadCoef_nonneg b E s 1
  unfold leadConst; positivity

/-- `|ab - a'b'| ≤ c'ε` from `|a - a'| ≤ c₁ε`, `|b - b'| ≤ c₂ε`, `|a'|, |b'| ≤ Λ`, `ε ≤ d + 1`. -/
theorem prod_near {m₁ m₂ l₁ l₂ : ℂ} {c₁ c₂ ε Λ d : ℝ} (h₁ : ‖m₁ - l₁‖ ≤ c₁ * ε)
    (h₂ : ‖m₂ - l₂‖ ≤ c₂ * ε) (hl₁ : ‖l₁‖ ≤ Λ) (hl₂ : ‖l₂‖ ≤ Λ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hε : 0 ≤ ε) (hε1 : ε ≤ d + 1) :
    ‖m₁ * m₂ - l₁ * l₂‖ ≤ (c₁ * c₂ * (d + 1) + (c₁ + c₂) * Λ) * ε := by
  refine (norm_mul_sub_mul_le' h₁ h₂).trans ?_
  have a1 : c₁ * ε * (c₂ * ε) ≤ c₁ * c₂ * (d + 1) * ε := by
    have : c₁ * ε * (c₂ * ε) = c₁ * c₂ * ε * ε := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hε1 (by positivity) |>.trans_eq' rfl |>.trans
      (by nlinarith [mul_nonneg (mul_nonneg hc₁ hc₂) hε])
  have a2 : c₁ * ε * ‖l₂‖ ≤ c₁ * ε * Λ := mul_le_mul_of_nonneg_left hl₂ (by positivity)
  have a3 : ‖l₁‖ * (c₂ * ε) ≤ Λ * (c₂ * ε) := mul_le_mul_of_nonneg_right hl₁ (by positivity)
  nlinarith

theorem norm_bilinear_le_of {W : ℕ} {L : Matrix (Fin W) (Fin W) ℂ} {Λ : ℝ} (hL : ‖L‖ ≤ Λ)
    {x y : Fin W → ℂ} (hx : vecNorm x ≤ 1) (hy : vecNorm y ≤ 1) : ‖bilinear x L y‖ ≤ Λ := by
  refine (norm_bilinear_le x L y).trans ?_
  have := vecNorm_nonneg x; have := vecNorm_nonneg y
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hL
  calc vecNorm x * ‖L‖ * vecNorm y ≤ 1 * Λ * 1 :=
        mul_le_mul (mul_le_mul hx hL (norm_nonneg _) zero_le_one) hy (vecNorm_nonneg _)
          (by positivity)
    _ = Λ := by ring

/-- **`MeansMatchMain` from the single-mean statements.** -/
theorem meansMatchMain_of_near (hA : PassiveLayer.PassiveBoundsStatement) (hT : TauNear)
    (hG : MeanNear gamFam leadGam) (hP : MeanNear alpFam leadAlp)
    (hQ : MeanNear alpFamI leadAlpI) : MeansMatchMain := by
  intro b hb0 hb E h1 h2 s hs
  obtain ⟨dG, CG, WG, hdG, hCG, hGm⟩ := hG b hb0 hb E h1 h2 s hs
  obtain ⟨dP, CP, WP, hdP, hCP, hPm⟩ := hP b hb0 hb E h1 h2 s hs
  obtain ⟨dQ, CQ, WQ, hdQ, hCQ, hQm⟩ := hQ b hb0 hb E h1 h2 s hs
  obtain ⟨dT, CT, WT, hdT, hCT, hTm⟩ := hT b hb0 hb E h1 h2 s hs
  obtain ⟨d₀, C₀, W₀, hd₀, hC₀, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨CK, WK, -, hK⟩ := SourceMixing.norm_kHat_dressedInv hA hb0 hb h1 h2
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hu : 1 + kMinus b E * s ≠ 0 := fun h => by
    have := jet_denom_pos hb0 hb h1 h2 s hs.2; rw [h, norm_zero] at this; linarith
  set Λ := leadConst b E s
  have hΛ : 0 ≤ Λ := leadConst_nonneg b E s
  set d := min (min dG dP) (min (min dQ dT) d₀)
  have hd : 0 < d := lt_min (lt_min hdG hdP) (lt_min (lt_min hdQ hdT) hd₀)
  set K₁ := 1 + C₀ * (d + 1)
  have hK₁ : 0 ≤ K₁ := by positivity
  set cG := CG * K₁ + C₀ * Λ
  set cQ := CQ * K₁ + C₀ * Λ
  have hcG : 0 ≤ cG := by positivity
  have hcQ : 0 ≤ cQ := by positivity
  set c₁ := cG * CP * (d + 1) + (cG + CP) * Λ
  set c₂ := cG * cQ * (d + 1) + (cG + cQ) * Λ
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  refine ⟨1, d, CT * (4 * c₂ * (d + 1) + 4 * Λ ^ 2) + 4 * c₂ + 4 * c₁,
    max (max (max WG WP) (max WQ WT)) (max (max W₀ WK) 1), one_pos, hd, by positivity, ?_⟩
  intro W hW X hX hδ v₁ v₂ v₃ v₄ hv₁ _ hv₃ hv₄
  have hv₂ : vecNorm v₂ ≤ 1 := by assumption
  have hWG : WG ≤ W := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hW
  have hWP : WP ≤ W := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hW
  have hWQ : WQ ≤ W := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _)) hW
  have hWT : WT ≤ W := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _)) hW
  have hW₀ : W₀ ≤ W := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hW
  have hWK : WK ≤ W := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hW
  have hW1 : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW0 : W ≠ 0 := by omega
  have hWi1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW1)
  change jetDelta b E s X ≤ d at hδ
  have hδ0 := jetDelta_nonneg b E s hX.posSemidef
  -- the error parameter `ε = δ + W⁻¹`
  have hε0 : 0 ≤ jetDelta b E s X + (W : ℝ)⁻¹ := by positivity
  have hε1 : jetDelta b E s X + (W : ℝ)⁻¹ ≤ d + 1 := add_le_add hδ hWi1
  have hδG : jetDelta b E s X ≤ dG := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδP : jetDelta b E s X ≤ dP := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδQ : jetDelta b E s X ≤ dQ :=
    hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδT : jetDelta b E s X ≤ dT :=
    hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδ₀ : jetDistance0 b E X ≤ d₀ := by
    have h0 := (SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef).2.1
    have h0' : 0 ≤ passiveMass b E X / W := (SourceMixing.epsOf_ge (b := b) (E := E) s
      hX.posSemidef).2.2.1
    have : jetDistance0 b E X ≤ jetDelta b E s X := by unfold jetDelta; linarith
    exact this.trans (hδ.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨-, -, hR, hKM1, -⟩ := hmb W hW₀ X hX hδ₀
  have heps : SourceMixing.epsOf b E s X ≤ jetDelta b E s X + (W : ℝ)⁻¹ := by
    have : (W : ℝ)⁻¹ ^ 2 ≤ (W : ℝ)⁻¹ := by
      rw [pow_two]; exact mul_le_of_le_one_left (by positivity) hWi1
    unfold SourceMixing.epsOf jetDelta; linarith
  set ε := jetDelta b E s X + (W : ℝ)⁻¹
  set KM := SourceMixing.kmOf b E X
  have hK1 : ‖KM - 1‖ ≤ C₀ * ε := hKM1.trans (mul_le_mul_of_nonneg_left heps hC₀)
  have hKM : ‖KM‖ ≤ K₁ := by
    have : ‖KM‖ ≤ ‖KM - 1‖ + ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ := by
      have := norm_add_le (KM - 1) 1; rwa [sub_add_cancel] at this
    have := norm_one_matrix_le (n := Fin W)
    have := mul_le_mul_of_nonneg_left hε1 hC₀
    linarith
  -- the left vectors `x̌ = ι₁(KMᴴv)`
  have hblk := kHat_mbar_blk b E X hW1 (hK W hWK X hX).1
  have hx : ∀ v : Fin W → ℂ, (kHat b E X * mbarSide b E X false)ᴴ *ᵥ physVec v =
      physVec (KMᴴ *ᵥ v) := fun v => conjT_mulVec_physVec hblk v
  -- the factor errors
  have eG1 : ∀ k : Fin 2, ‖(∫ ω, star (physVec (KMᴴ *ᵥ v₁)) ⬝ᵥ (gamFam k b E W X ω *ᵥ physVec v₄)
      ∂layerLaw W b .oneBlockOnePort) - bilinear v₁ (leadGam k b E s W X) v₄‖ ≤ cG * ε :=
    fun k => near_left rfl (hGm W hWG X hX hδG k _ v₄) hv₁ hv₄ hKM hK1
      (norm_leadGam_le hη hR k) hCG hε0
  have eG2 : ∀ k : Fin 2, ‖(∫ ω, star (physVec (KMᴴ *ᵥ v₂)) ⬝ᵥ (gamFam k b E W X ω *ᵥ physVec v₃)
      ∂layerLaw W b .oneBlockOnePort) - bilinear v₂ (leadGam k b E s W X) v₃‖ ≤ cG * ε :=
    fun k => near_left rfl (hGm W hWG X hX hδG k _ v₃) hv₂ hv₃ hKM hK1
      (norm_leadGam_le hη hR k) hCG hε0
  have eP : ∀ k p : Fin 2, ‖(∫ ω, star (physVec v₃) ⬝ᵥ (alpFam (k, p) b E W X ω *ᵥ physVec v₂)
      ∂layerLaw W b .oneBlockOnePort) - bilinear v₃ (leadAlp (k, p) b E s W X) v₂‖ ≤ CP * ε := by
    intro k p
    refine (hPm W hWP X hX hδP (k, p) v₃ v₂).trans ?_
    have := vecNorm_nonneg v₂; have := vecNorm_nonneg v₃
    calc CP * ε * (vecNorm v₃ * vecNorm v₂) ≤ CP * ε * (1 * 1) := by gcongr
      _ = CP * ε := by ring
  have eQ : ∀ k p : Fin 2, ‖(∫ ω, star (physVec v₄) ⬝ᵥ (alpFamI (k, p) b E W X ω *ᵥ
      physVec (KMᴴ *ᵥ v₁)) ∂layerLaw W b .oneBlockOnePort) -
        bilinear v₄ (leadAlpI (k, p) b E s W X) v₁‖ ≤ cQ * ε :=
    fun k p => near_right rfl (hQm W hWQ X hX hδQ (k, p) v₄ _) hv₁ hv₄ hKM hK1
      (norm_leadAlpI_le hη hR (k, p)) hCQ hε0 hΛ
  -- the sources
  have S1 : ‖srcX1 b E X v₁ v₂ v₃ v₄ - leadX1 b E s X v₁ v₂ v₃ v₄‖ ≤ 4 * (c₁ * ε) / W := by
    rw [srcX1_eq hb0 hb X v₁ v₂ v₃ v₄ _ (hx v₁), leadX1_eq']
    exact norm_wsum_sub_le hb0 hb _ _ fun k p => prod_near (eG1 k) (eP k p)
      (norm_bilinear_le_of (norm_leadGam_le hη hR k) hv₁ hv₄)
      (norm_bilinear_le_of (norm_leadAlp_le hη hR (k, p)) hv₃ hv₂) hcG hCP hε0 hε1
  have S2 : ‖srcX2 b E X v₁ v₂ v₃ v₄ - leadX2 b E s X v₁ v₂ v₃ v₄‖ ≤ 4 * (c₂ * ε) / W := by
    rw [srcX2_eq hb0 hb X v₁ v₂ v₃ v₄ _ _ (hx v₁) (hx v₂), leadX2_eq']
    exact norm_wsum_sub_le hb0 hb _ _ fun k p => prod_near (eG2 k) (eQ k p)
      (norm_bilinear_le_of (norm_leadGam_le hη hR k) hv₂ hv₃)
      (norm_bilinear_le_of (norm_leadAlpI_le hη hR (k, p)) hv₄ hv₁) hcG hcQ hε0 hε1
  have L2 : ‖leadX2 b E s X v₁ v₂ v₃ v₄‖ ≤ 4 * (Λ * Λ) / W := by
    rw [leadX2_eq']
    refine norm_wsum_le hb0 hb _ fun k p => ?_
    rw [norm_mul]
    exact mul_le_mul (norm_bilinear_le_of (norm_leadGam_le hη hR k) hv₂ hv₃)
      (norm_bilinear_le_of (norm_leadAlpI_le hη hR (k, p)) hv₄ hv₁) (norm_nonneg _) hΛ
  have X2 : ‖srcX2 b E X v₁ v₂ v₃ v₄‖ ≤ (4 * c₂ * (d + 1) + 4 * Λ ^ 2) / W := by
    have := norm_add_le (srcX2 b E X v₁ v₂ v₃ v₄ - leadX2 b E s X v₁ v₂ v₃ v₄)
      (leadX2 b E s X v₁ v₂ v₃ v₄)
    rw [sub_add_cancel] at this
    have h4 : 4 * (c₂ * ε) / W ≤ 4 * (c₂ * (d + 1)) / W := by
      gcongr
    have : 4 * (c₂ * (d + 1)) / W + 4 * (Λ * Λ) / W = (4 * c₂ * (d + 1) + 4 * Λ ^ 2) / W := by ring
    linarith
  have hτ : ‖tauBar b E X - 1‖ ≤ CT * ε := hTm W hWT X hX hδT
  -- assembly
  rw [← lead_eq_main hb0 hb h1 h2 hu hW0 X v₁ v₂ v₃ v₄]
  have e : tauBar b E X * conj (srcX2 b E X v₁ v₂ v₃ v₄) + srcX1 b E X v₁ v₂ v₃ v₄ -
      (conj (leadX2 b E s X v₁ v₂ v₃ v₄) + leadX1 b E s X v₁ v₂ v₃ v₄) =
      (tauBar b E X - 1) * conj (srcX2 b E X v₁ v₂ v₃ v₄) +
        conj (srcX2 b E X v₁ v₂ v₃ v₄ - leadX2 b E s X v₁ v₂ v₃ v₄) +
        (srcX1 b E X v₁ v₂ v₃ v₄ - leadX1 b E s X v₁ v₂ v₃ v₄) := by
    rw [map_sub]; ring
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  rw [norm_mul, Complex.norm_conj, Complex.norm_conj]
  have t1 : ‖tauBar b E X - 1‖ * ‖srcX2 b E X v₁ v₂ v₃ v₄‖ ≤
      CT * ε * ((4 * c₂ * (d + 1) + 4 * Λ ^ 2) / W) :=
    mul_le_mul hτ X2 (norm_nonneg _) (by positivity)
  have hfin : CT * ε * ((4 * c₂ * (d + 1) + 4 * Λ ^ 2) / W) + 4 * (c₂ * ε) / W +
      4 * (c₁ * ε) / W = (CT * (4 * c₂ * (d + 1) + 4 * Λ ^ 2) + 4 * c₂ + 4 * c₁) *
        ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDelta b E s X) := by
    simp only [ε]; field_simp; ring
  change _ ≤ _ * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDelta b E s X)
  linarith

/-- **`PassiveCovarianceContract` from the contract hypotheses and the four mean statements.** -/
theorem passiveCovariance_holds_of_near (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hT : TauNear)
    (hG : MeanNear gamFam leadGam) (hα : MeanNear alpFam leadAlp)
    (hQ : MeanNear alpFamI leadAlpI) : PassiveCovarianceContract :=
  passiveCovariance_holds_of_match hGA hLp hP
    (meansMatchMain_of_near (PassiveLayer.passiveBounds_holds hGA hLp) hT hG hα hQ)

end BlockBand.Transmission.PassiveCovariance
