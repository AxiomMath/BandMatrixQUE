module

public import BlockBand.Transmission.PassiveCovarianceBulk.GamNear
public import BlockBand.Transmission.PassiveCovarianceBulk.CovLevel0
public import BlockBand.Transmission.PassiveCovariance.AlpReduction

/-!
# Bulk-uniform `MeansMatchMain` and the normalized bound

`MeansMatchMainBulk` from the single-mean statements, and the normalized near-domain bound,
with constants and `W₀` uniform in `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.PathScalar (etaLow etaLow_pos etaLow_le bulk_bounds bulk_eta_le_one bulk_norm_z)
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **`MeansMatchMainBulk` from the single-mean statements.**
Bulk-uniform copy of `meansMatchMain_of_near` (constants uniform on `bulkInterval κ`). -/
theorem meansMatchMain_of_near_bulk (hA : PassiveLayer.PassiveBoundsStatement) (hT : TauNearBulk)
    (hG : MeanNearBulk gamFam leadGam) (hP : MeanNearBulk alpFam leadAlp)
    (hQ : MeanNearBulk alpFamI leadAlpI) : MeansMatchMainBulk := by
  intro b hb0 hb κ hκ
  obtain ⟨dG, CG, WG, hdG, hCG, hGm⟩ := hG b hb0 hb κ hκ
  obtain ⟨dP, CP, WP, hdP, hCP, hPm⟩ := hP b hb0 hb κ hκ
  obtain ⟨dQ, CQ, WQ, hdQ, hCQ, hQm⟩ := hQ b hb0 hb κ hκ
  obtain ⟨dT, CT, WT, hdT, hCT, hTm⟩ := hT b hb0 hb κ hκ
  obtain ⟨d₀, C₀, W₀, hd₀, hC₀, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨CK, WK, -, hK⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  set Λ := leadConstL b κ
  have hΛ : 0 ≤ Λ := leadConstL_nonneg b κ
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
  intro W hW E hEκ s hs X hX hδ v₁ v₂ v₃ v₄ hv₁ _ hv₃ hv₄
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hu : 1 + kMinus b E * s ≠ 0 := fun h => by
    have := jet_denom_pos hb0 hb h1 h2 s hs.2; rw [h, norm_zero] at this; linarith
  have hΛle : leadConst b E s ≤ Λ := leadConst_le_bulk hb0 hb hκ hEκ hs
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
  obtain ⟨-, -, hR, hKM1, -⟩ := hmb W hW₀ E hEκ s X hX hδ₀
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
  have hblk := kHat_mbar_blk b E X hW1 (hK W hWK E hEκ X hX).1
  have hx : ∀ v : Fin W → ℂ, (kHat b E X * mbarSide b E X false)ᴴ *ᵥ physVec v =
      physVec (KMᴴ *ᵥ v) := fun v => conjT_mulVec_physVec hblk v
  -- the factor errors
  have eG1 : ∀ k : Fin 2, ‖(∫ ω, star (physVec (KMᴴ *ᵥ v₁)) ⬝ᵥ (gamFam k b E W X ω *ᵥ physVec v₄)
      ∂layerLaw W b .oneBlockOnePort) - bilinear v₁ (leadGam k b E s W X) v₄‖ ≤ cG * ε :=
    fun k => near_left rfl (hGm W hWG E hEκ s hs X hX hδG k _ v₄) hv₁ hv₄ hKM hK1
      ((norm_leadGam_le hη hR k).trans hΛle) hCG hε0
  have eG2 : ∀ k : Fin 2, ‖(∫ ω, star (physVec (KMᴴ *ᵥ v₂)) ⬝ᵥ (gamFam k b E W X ω *ᵥ physVec v₃)
      ∂layerLaw W b .oneBlockOnePort) - bilinear v₂ (leadGam k b E s W X) v₃‖ ≤ cG * ε :=
    fun k => near_left rfl (hGm W hWG E hEκ s hs X hX hδG k _ v₃) hv₂ hv₃ hKM hK1
      ((norm_leadGam_le hη hR k).trans hΛle) hCG hε0
  have eP : ∀ k p : Fin 2, ‖(∫ ω, star (physVec v₃) ⬝ᵥ (alpFam (k, p) b E W X ω *ᵥ physVec v₂)
      ∂layerLaw W b .oneBlockOnePort) - bilinear v₃ (leadAlp (k, p) b E s W X) v₂‖ ≤ CP * ε := by
    intro k p
    refine (hPm W hWP E hEκ s hs X hX hδP (k, p) v₃ v₂).trans ?_
    have := vecNorm_nonneg v₂; have := vecNorm_nonneg v₃
    calc CP * ε * (vecNorm v₃ * vecNorm v₂) ≤ CP * ε * (1 * 1) := by gcongr
      _ = CP * ε := by ring
  have eQ : ∀ k p : Fin 2, ‖(∫ ω, star (physVec v₄) ⬝ᵥ (alpFamI (k, p) b E W X ω *ᵥ
      physVec (KMᴴ *ᵥ v₁)) ∂layerLaw W b .oneBlockOnePort) -
        bilinear v₄ (leadAlpI (k, p) b E s W X) v₁‖ ≤ cQ * ε :=
    fun k p => near_right rfl (hQm W hWQ E hEκ s hs X hX hδQ (k, p) v₄ _) hv₁ hv₄ hKM hK1
      ((norm_leadAlpI_le hη hR (k, p)).trans hΛle) hCQ hε0 hΛ
  -- the sources
  have S1 : ‖srcX1 b E X v₁ v₂ v₃ v₄ - leadX1 b E s X v₁ v₂ v₃ v₄‖ ≤ 4 * (c₁ * ε) / W := by
    rw [srcX1_eq hb0 hb X v₁ v₂ v₃ v₄ _ (hx v₁), leadX1_eq']
    exact norm_wsum_sub_le hb0 hb _ _ fun k p => prod_near (eG1 k) (eP k p)
      (norm_bilinear_le_of ((norm_leadGam_le hη hR k).trans hΛle) hv₁ hv₄)
      (norm_bilinear_le_of ((norm_leadAlp_le hη hR (k, p)).trans hΛle) hv₃ hv₂) hcG hCP hε0 hε1
  have S2 : ‖srcX2 b E X v₁ v₂ v₃ v₄ - leadX2 b E s X v₁ v₂ v₃ v₄‖ ≤ 4 * (c₂ * ε) / W := by
    rw [srcX2_eq hb0 hb X v₁ v₂ v₃ v₄ _ _ (hx v₁) (hx v₂), leadX2_eq']
    exact norm_wsum_sub_le hb0 hb _ _ fun k p => prod_near (eG2 k) (eQ k p)
      (norm_bilinear_le_of ((norm_leadGam_le hη hR k).trans hΛle) hv₂ hv₃)
      (norm_bilinear_le_of ((norm_leadAlpI_le hη hR (k, p)).trans hΛle) hv₄ hv₁) hcG hcQ hε0 hε1
  have L2 : ‖leadX2 b E s X v₁ v₂ v₃ v₄‖ ≤ 4 * (Λ * Λ) / W := by
    rw [leadX2_eq']
    refine norm_wsum_le hb0 hb _ fun k p => ?_
    rw [norm_mul]
    exact mul_le_mul (norm_bilinear_le_of ((norm_leadGam_le hη hR k).trans hΛle) hv₂ hv₃)
      (norm_bilinear_le_of ((norm_leadAlpI_le hη hR (k, p)).trans hΛle) hv₄ hv₁) (norm_nonneg _) hΛ
  have X2 : ‖srcX2 b E X v₁ v₂ v₃ v₄‖ ≤ (4 * c₂ * (d + 1) + 4 * Λ ^ 2) / W := by
    have := norm_add_le (srcX2 b E X v₁ v₂ v₃ v₄ - leadX2 b E s X v₁ v₂ v₃ v₄)
      (leadX2 b E s X v₁ v₂ v₃ v₄)
    rw [sub_add_cancel] at this
    have h4 : 4 * (c₂ * ε) / W ≤ 4 * (c₂ * (d + 1)) / W := by
      gcongr
    have : 4 * (c₂ * (d + 1)) / W + 4 * (Λ * Λ) / W = (4 * c₂ * (d + 1) + 4 * Λ ^ 2) / W := by ring
    linarith
  have hτ : ‖tauBar b E X - 1‖ ≤ CT * ε := hTm W hWT E hEκ s hs X hX hδT
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

theorem meansMatchMain_of_alp_bulk (hA : PassiveLayer.PassiveBoundsStatement)
    (hα : MeanNearBulk alpFam leadAlp) (hQ : MeanNearBulk alpFamI leadAlpI) : MeansMatchMainBulk :=
  meansMatchMain_of_near_bulk hA (tauNear_holds_bulk hA) (gamNear_holds_bulk hA) hα hQ

/-- `cov_level0` and `MeansMatchMainBulk` give the normalized near-domain bound.
Bulk-uniform copy of `normalized_of_match` (constants uniform on `bulkInterval κ`). -/
theorem normalized_of_match_bulk (hP : GaussianPoincare) (hA : PassiveLayer.PassiveBoundsStatement)
    (hM : MeansMatchMainBulk) : PassiveCovarianceNormalizedBulk := by
  intro b hb0 hb κ hκ
  obtain ⟨ρ₁, d, C₁, W₁, hρ₁, hd, hC₁, hM'⟩ := hM b hb0 hb κ hκ
  obtain ⟨ρ₀, C₀, W₀, hρ₀, hC₀, hL⟩ := cov_level0_bulk hP hA hb0 hb hκ
  refine ⟨min ρ₀ ρ₁, d, C₀ + C₁, max W₀ W₁, lt_min hρ₀ hρ₁, hd,
    fun W hW E hEκ s hs X hX hδ v₁ v₂ v₃ v₄ hv₁ hv₂ hv₃ hv₄ => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hL' : ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
      tauBar b E X * conj (srcX2 b E X v₁ v₂ v₃ v₄) - srcX1 b E X v₁ v₂ v₃ v₄‖ ≤ C₀ / (W : ℝ) ^ 2 :=
    hL W (le_trans (le_max_left _ _) hW) E hEκ X hX v₁ v₂ v₃ v₄ (hv₁.trans (min_le_left _ _)) hv₂ hv₃ hv₄
  have hm := hM' W (le_trans (le_max_right _ _) hW) E hEκ s hs X hX hδ v₁ v₂ v₃ v₄
    (hv₁.trans (min_le_right _ _)) hv₂ hv₃ hv₄
  set δ := jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W
  have hδ0 : 0 ≤ δ := by
    have := passiveMass_nonneg b E hX.posSemidef
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    positivity
  have hW2 : C₀ / (W : ℝ) ^ 2 = C₀ * (W : ℝ)⁻¹ ^ 2 := by rw [inv_pow, div_eq_mul_inv]
  have e : bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ - mainTensor b E s X v₁ v₂ v₃ v₄ =
      (bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
        tauBar b E X * conj (srcX2 b E X v₁ v₂ v₃ v₄) - srcX1 b E X v₁ v₂ v₃ v₄) +
      (tauBar b E X * conj (srcX2 b E X v₁ v₂ v₃ v₄) + srcX1 b E X v₁ v₂ v₃ v₄ -
        mainTensor b E s X v₁ v₂ v₃ v₄) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1' : 0 ≤ (W : ℝ)⁻¹ * δ := by positivity
  calc _ ≤ C₀ * (W : ℝ)⁻¹ ^ 2 + C₁ * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ) := by
        rw [← hW2]; exact add_le_add hL' hm
    _ ≤ (C₀ + C₁) * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ) := by nlinarith

end BlockBand.Transmission.CovarianceBulk
