module

public import BlockBand.Transmission.PathJet.JetMeanU

/-!
# The jet mean step (strictly passive inputs of the form `Y = Y₀ + ε`)

`jetMean_strict (hA : PassiveBoundsStatement)`: `b, κ` first; then `d₀ > 0`, `C₂, C ≥ 0`, `W₀`;
for `W ≥ W₀`, `E ∈ bulkInterval κ`, every stationary jet `s`, and every `X` with
`Y = Y₀ + ε` (`Y₀ ⪰ 0`, `ε > 0`) and `δ₀(X) ≤ d₀`,
`|E freshJet - s| ≤ ρ_J δ₁(X) + C₂δ₀(X) + C/W²`, `ρ_J = rhoJ b (kGap b κ) < 1`.

Ingredients: the disk mean equations (`diskMeanEquationsStrict_holds`), their derivatives at `z`
(`residual_derivs`, Cauchy), the stable branch at `z` (`passiveMean_stability`),
`u'(z) = E freshJet` (`deriv_uW_eq`), the old-jet bounds (`norm_oldJet_le`,
`norm_crossTr_sub_le`) and the scalar bookkeeping `jet_mean_scalar`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix Metric Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator ComplexConjugate

variable {W : ℕ}

theorem matchedA_inv_eq (E : ℝ) (h1 : -2 < E) (h2 : E < 2) :
    (matchedA E)⁻¹ = -(E : ℂ) - matchedA E := by
  rw [matchedA_inv E h1 h2]
  apply Complex.ext <;> (simp [matchedA]; try ring)

theorem zeta_sub_z (b E : ℝ) (h1 : -2 < E) (h2 : E < 2) (v u : ℂ) :
    zetaOf b E v u - boundaryZ b E =
      -(((1 - 2 * b : ℝ) : ℂ) * (v - matchedA E) + (b : ℂ) * (u - matchedA E)) := by
  rw [zetaOf, boundaryZ, matchedA_inv_eq E h1 h2]; push_cast; ring

theorem norm_kMinus_le_one {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) : ‖kMinus b E‖ ≤ 1 := by
  have h := bulk_kMinus hb0 hb hκ hE
  have hg := kGap_pos hb0 hb hκ
  have hd : 1 ≤ dStar b := by
    rw [dStar, le_div_iff₀ (by linarith)]; linarith
  have := mul_le_mul_of_nonneg_left hd (norm_nonneg (kMinus b E))
  linarith

/-- The size parameter `Λ = δ₀ + (1 + 4/η_κ)C/W²`. -/
def jetLam (b κ C δ₀ : ℝ) (W : ℕ) : ℝ := δ₀ + (1 + 4 / etaLow b κ) * C / (W : ℝ) ^ 2

theorem jetMean_strict (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (d₀ C₂ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ (X Y₀ : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ), 0 < ε → Y₀.PosSemidef →
        passiveY X = Y₀ + ε • (1 : Matrix (Fin W) (Fin W) ℂ) → jetDistance0 b E X ≤ d₀ →
        ‖(∫ ω, freshJet b E X ω ∂freshLaw W b) - s‖ ≤
          rhoJ b (kGap b κ) * jetDistance1 b E s X + C₂ * jetDistance0 b E X +
            C / (W : ℝ) ^ 2 := by
  obtain ⟨Cv, ι₀, Cb, W₁, hCv, hι₀, hCb, hbund⟩ := diskMeanEquationsStrict_holds hA b hb0 hb κ hκ
  obtain ⟨ds, ρs, Cs, εs, hds, hρs0, hρs1, hCs, hεs, hst⟩ := passiveMean_stability hb0 hb hκ hCv
  set ηl := etaLow b κ
  have hηl : 0 < ηl := etaLow_pos (by linarith) hκ
  set g := kGap b κ
  have hg : 0 < g := kGap_pos hb0 hb hκ
  set Kφ := ι₀⁻¹ ^ 2 * ηl⁻¹ + ι₀⁻¹ * ηl⁻¹ ^ 2
  have hKφ : 0 ≤ Kφ := by positivity
  set A₁ := 1 + Cs
  have hA₁ : 0 ≤ A₁ := by positivity
  set Mu := ηl⁻¹ ^ 2
  have hMu : 0 ≤ Mu := by positivity
  set Λ₀ := jetLam0 b g ηl Kφ A₁
  have hΛ₀ : 0 < Λ₀ := jetLam0_pos hb0 hg hηl hKφ hA₁
  set K := jetKc b Kφ A₁ Mu
  have hK : 0 ≤ K := by
    simp only [K, jetKc, jetA4]; positivity
  set Ce := (1 + 4 / ηl) * Cb
  have hCe : 0 ≤ Ce := by positivity
  set Wt := max (Cb / εs) (Ce / (Λ₀ / 2))
  refine ⟨min ds (Λ₀ / 2), K, K * Ce, max W₁ (⌈Wt⌉₊ + 1), lt_min hds (by positivity), hK,
    by positivity, ?_⟩
  intro W hW E hE s hs X Y₀ ε hε hY₀ hYe hδ
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hWt : (Wt : ℝ) ≤ W := by
    have h := Nat.le_ceil Wt
    have : ((⌈Wt⌉₊ : ℕ) : ℝ) + 1 ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
    linarith
  have hx1 : (1 : ℝ) ≤ W := by
    have : (0 : ℝ) ≤ Wt := le_trans (div_nonneg hCb hεs.le) (le_max_left _ _)
    have : ((⌈Wt⌉₊ : ℕ) : ℝ) + 1 ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
    linarith [(Nat.cast_nonneg ⌈Wt⌉₊ : (0 : ℝ) ≤ _)]
  have hW0 : 1 ≤ W := by exact_mod_cast hx1
  have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
  have hWpos : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  have hεW : Cb / (W : ℝ) ^ 2 ≤ εs := by
    have : Cb / εs ≤ (W : ℝ) ^ 2 := ((le_max_left _ _).trans hWt).trans hWW
    rw [div_le_iff₀ hεs] at this; rw [div_le_iff₀ hWpos]; linarith
  have hCeW : Ce / (W : ℝ) ^ 2 ≤ Λ₀ / 2 := by
    have : Ce / (Λ₀ / 2) ≤ (W : ℝ) ^ 2 := ((le_max_right _ _).trans hWt).trans hWW
    rw [div_le_iff₀ (by positivity)] at this; rw [div_le_iff₀ hWpos]; linarith
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hη := etaLow_le (by linarith : b < 1) hκ hE
  have hηE : 0 < etaZ b E := lt_of_lt_of_le hηl hη
  have hYp : (passiveY X).PosSemidef := passiveY_of_reg hε hY₀ hYe
  have hYd : (passiveY X).PosDef := by
    rw [hYe]; exact Matrix.PosDef.posSemidef_add hY₀ (Matrix.PosDef.one.smul hε)
  set z := boundaryZ b E
  set a := matchedA E
  set δ₀ := jetDistance0 b E X
  have hδ0 : 0 ≤ δ₀ := norm_nonneg _
  set ε' := Cb / (W : ℝ) ^ 2
  have hε'0 : 0 ≤ ε' := by positivity
  -- the bundle on the disk
  have hdisk : ∀ w ∈ paramDisk b E, ι₀ ≤ (zetaW b E X w).im ∧ ‖resid1 b E X w‖ ≤ ε' ∧
      ‖resid2 b E X w‖ ≤ ε' := fun w hw => by
    obtain ⟨-, -, hζ, hp, hf⟩ := hbund W hW1 E hE w hw X hYd
    exact ⟨hζ, hp, hf⟩
  obtain ⟨hr1', hr2', hd1, hd2⟩ := residual_derivs hε hY₀ hYe hb0 hb h1 h2 hι₀ hdisk
  have hzD := boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  obtain ⟨hv0, hvC, hζz, hp, hf⟩ := hbund W hW1 E hE z hzD X hYd
  -- the stable branch at `z`
  have hδs : δ₀ ≤ ds := hδ.trans (min_le_left _ _)
  have hua := hst W E hE X hYp _ _ ε' hv0 hvC hp hf hε'0 hεW hδs
  -- the derivative of `u`
  have hu'eq := (deriv_uW_eq hb0 hb hW0 h1 h2 hYp).deriv
  set u' := deriv (fun w => uW b E w X) z
  have hu' : ‖u'‖ ≤ Mu := by
    rw [hu'eq]
    refine (norm_integral_le_of_norm_le_const (C := (etaZ b E)⁻¹ ^ 2)
      ((ae_layer_herm b).mono fun ω hA => ?_)).trans ?_
    · rw [freshJet_eq_jetFun (by linarith) h1 h2 hYp hA]
      exact norm_jetFun_le (by linarith) h1 h2 hYp hA
    · simp only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one, Mu]
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hηl hη) 2
  -- the old jets
  have ht := norm_oldJet_le (by linarith : b < 1) h1 h2 hYp
  have htη : ‖-crossTr X z z‖ ≤ dStar b + δ₀ / ηl := by
    rw [norm_neg]
    exact ht.trans (by gcongr)
  have hφt : ‖-crossTr X (zetaW b E X z) (zetaW b E X z) - -crossTr X z z‖ ≤
      Kφ * ‖zetaW b E X z - z‖ := by
    rw [show -crossTr X (zetaW b E X z) (zetaW b E X z) - -crossTr X z z =
      -(crossTr X (zetaW b E X z) (zetaW b E X z) - crossTr X z z) by ring, norm_neg, mul_comm]
    exact norm_crossTr_sub_le hYp hι₀ hηl hζz hη
  have hj1 : jetDistance1 b E s X = ‖-crossTr X z z - s‖ := by
    rw [jetDistance1]
    change ‖deriv (stieltjes X) z - s‖ = _
    rw [deriv_stieltjes hYp hηE]
  -- size parameter
  set Λ := δ₀ + Ce / (W : ℝ) ^ 2
  have hε'Λ : ε' ≤ Λ := by
    have : ε' ≤ Ce / (W : ℝ) ^ 2 := by
      have h4 : 0 ≤ 4 / ηl := by positivity
      exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hCb (by linarith)) hWpos.le
    linarith
  have hε''Λ : ε' / (etaZ b E / 4) ≤ Λ := by
    have e1 : ε' / (etaZ b E / 4) ≤ ε' / (ηl / 4) :=
      div_le_div_of_nonneg_left hε'0 (by positivity) (by linarith)
    have e2 : ε' / (ηl / 4) = 4 / ηl * Cb / (W : ℝ) ^ 2 := by
      simp only [ε']; field_simp
    have e3 : 4 / ηl * Cb / (W : ℝ) ^ 2 ≤ Ce / (W : ℝ) ^ 2 := by
      simp only [Ce]; gcongr; linarith
    linarith
  have hΛ : Λ ≤ Λ₀ := by
    have := hδ.trans (min_le_right _ _); linarith
  have hx : ‖uW b E z X - a‖ ≤ A₁ * Λ := by
    have e : ρs * δ₀ + Cs * ε' ≤ A₁ * Λ := by
      simp only [A₁]
      have : ρs * δ₀ ≤ δ₀ := mul_le_of_le_one_left hδ0 hρs1.le
      have : Cs * ε' ≤ Cs * Λ := mul_le_mul_of_nonneg_left hε'Λ hCs
      have : δ₀ ≤ Λ := by have : 0 ≤ Ce / (W : ℝ) ^ 2 := by positivity
                          linarith
      nlinarith
    exact hua.trans e
  have hδΛ : δ₀ ≤ Λ := by have : 0 ≤ Ce / (W : ℝ) ^ 2 := by positivity
                          linarith
  have hDR : uW b E z X * (z - (b : ℂ) * vW b E z X) = 1 + resid1 b E X z := by
    rw [resid1]; ring
  have hmain := jet_mean_scalar (a := a) (s := s) (k := kMinus b E) (u := uW b E z X)
    (v := vW b E z X) (u' := u') (v' := deriv (fun w => vW b E w X) z)
    (D := z - (b : ℂ) * vW b E z X) (φ := -crossTr X (zetaW b E X z) (zetaW b E X z))
    (t := -crossTr X z z) (r₁ := resid1 b E X z) (r₁' := deriv (resid1 b E X) z)
    (r₂' := deriv (resid2 b E X) z) (z := z) (ζ := zetaW b E X z) (η := ηl)
    hb0 hb hg hηl hKφ hA₁ hMu (norm_matchedA E h1 h2) (by simp [kMinus, a]) hs.1 hs.2
    (bulk_kMinus hb0 hb hκ hE) (by rw [dStar, div_le_iff₀ (by linarith)]; linarith)
    (norm_kMinus_le_one hb0 hb hκ hE) rfl rfl (zeta_sub_z b E h1 h2 _ _) hDR hd1 hd2
    hx (hp.trans hε'Λ) (hr1'.trans hε''Λ) (hr2'.trans hε''Λ) hδ0 hδΛ hφt htη hu' hΛ
  rw [hu'eq] at hmain
  rw [hj1]
  calc _ ≤ rhoJ b g * ‖-crossTr X z z - s‖ + K * Λ := hmain
    _ = _ := by simp only [Λ]; ring

end BlockBand.Transmission.PathJet
