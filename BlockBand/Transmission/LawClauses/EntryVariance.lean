module

public import BlockBand.Transmission.LawClauses.EntryVarianceCore
public import BlockBand.Transmission.PassiveCovariance.CovarianceHolds

/-!
# `TransmissionLawContract.entryVariance` from the passive covariance lemma

* `stationaryJet_unique`: the stationary jet is unique (contraction of `jetMap`).
* `entryVariance_of_covBound` (deterministic, explicit constants): if the covariance bound of
  the passive covariance lemma holds with constant `C` at one `(W, X, u_i, u_j)`, then
  `E|U⁰_ij|² ≥ G/W - (|C|+1)(W⁻² + W⁻¹(2d + γ/(4η)))`, `G = (σ₊ - |σ₋|)/(4η²)`, whenever
  `δ₀, δ₁ ≤ d`, `g ≤ γW`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate ComplexOrder

/-- **Uniqueness of the stationary jet** (`jetMap` is a contraction on `|s| ≤ d_*`). -/
theorem stationaryJet_unique {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) {s t : ℂ} (hs : IsStationaryJet b E s) (ht : IsStationaryJet b E t) : s = t := by
  have hfix : ∀ r : ℂ, IsStationaryJet b E r → jetMap b E r = r := by
    intro r hr
    have hden : 1 + kMinus b E * r ≠ 0 := by
      intro h; have := jet_denom_pos hb0 hb h1 h2 r hr.2; rw [h, norm_zero] at this; linarith
    rw [jetMap, div_eq_iff hden]
    linear_combination -hr.1
  have hm := jet_margin_gt hb0 hb h1 h2
  have hmpos : 0 < 1 - ‖kMinus b E‖ * dStar b := lt_trans hb0 hm
  have hL : b ^ 2 / (1 - ‖kMinus b E‖ * dStar b) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have h := jetMap_lipschitz hb0 hb h1 h2 s t hs.2 ht.2
  rw [hfix s hs, hfix t ht] at h
  have hn : ‖s - t‖ = 0 := by
    have := norm_nonneg (s - t)
    nlinarith [mul_le_mul_of_nonneg_right hL.le this]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem vecNorm_eq_one {W : ℕ} (u : Fin W → ℂ) (hu : star u ⬝ᵥ u = 1) : vecNorm u = 1 := by
  have h := star_self_eq u
  rw [hu] at h
  have h' : vecNorm u ^ 2 = 1 := by exact_mod_cast h.symm
  have := vecNorm_nonneg u
  nlinarith

/-- `g = 4ηq`. -/
theorem conductanceOf_passiveTransmission {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    conductanceOf (passiveTransmission b E X) = 4 * etaZ b E * passiveMass b E X := by
  rw [conductanceOf, passiveTransmission, trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    passiveMass]

/-- **Deterministic core with explicit constants.** -/
theorem entryVariance_of_covBound {W : ℕ} {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) {s : ℂ} (hs : IsStationaryJet b E s) (hW : 0 < W)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {d γ C : ℝ}
    (hd0 : jetDistance0 b E X ≤ d) (hd1 : jetDistance1 b E s X ≤ d)
    (hg : conductanceOf (passiveTransmission b E X) ≤ γ * W)
    {u : Fin W → Fin W → ℂ} {t : Fin W → ℝ}
    (hu : IsOrthonormalEigenbasis (passiveTransmission b E X) u t) (i j : Fin W)
    (hti : t i ≤ 1 / 2) (htj : t j ≤ 1 / 2)
    (hcov : ‖bilinearCovariance (freshLaw W b) (freshU b E X) (u i) (u j) (u j) (u i) -
        mainTensor b E s X (u i) (u j) (u j) (u i)‖ ≤
      C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
        (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
        fourNorm (u i) (u j) (u j) (u i)) :
    (sigmaPlus b - ‖sigmaMinus b E s‖) / (4 * etaZ b E ^ 2) / W -
        (|C| + 1) * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (2 * d + γ / (4 * etaZ b E))) ≤
      ∫ ω, ‖bilinear (u i) (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)) (u j)‖ ^ 2
        ∂freshLaw W b := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hui : star (u i) ⬝ᵥ u i = 1 := by simpa using hu.1 i i
  have huj : star (u j) ⬝ᵥ u j = 1 := by simpa using hu.1 j j
  have hF : fourNorm (u i) (u j) (u j) (u i) = 1 := by
    rw [fourNorm, vecNorm_eq_one _ hui, vecNorm_eq_one _ huj]; ring
  have hgap := (norm_sigmaMinus_lt_sigmaPlus hb0 hb h1 h2 hs).le
  have hre := re_mainTensor_ge hb0 hb h1 h2 hY s (u i) (u j) (t i) (t j) hui huj (hu.2 i)
    (hu.2 j) hti htj hgap
  have hent := bilinearCovariance_entry (freshLaw W b) (freshU b E X)
    (fun ω => isHermitian_mul_conjTranspose_self _) (u i) (u j)
  set V := ∫ ω, ‖bilinear (u i) (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X))
    (u j)‖ ^ 2 ∂freshLaw W b
  rw [hent, hF, mul_one] at hcov
  -- the error is at most `(|C|+1)(W⁻² + W⁻¹(2d + γ/(4η)))`
  have hq : passiveMass b E X / W ≤ γ / (4 * etaZ b E) := by
    rw [conductanceOf_passiveTransmission] at hg
    rw [div_le_div_iff₀ hWr (by positivity)]; nlinarith
  have hδ0 : 0 ≤ jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W := by
    have := passiveMass_nonneg b E hY
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    positivity
  have hB0 : 0 ≤ (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
      (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) := by positivity
  have hBle : (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
      (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) ≤
      (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (2 * d + γ / (4 * etaZ b E)) := by
    have : jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W ≤
        2 * d + γ / (4 * etaZ b E) := by linarith
    have := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hWr.le)
    linarith
  have hCK : C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
      (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) ≤
      (|C| + 1) * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (2 * d + γ / (4 * etaZ b E))) := by
    have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
    have hK : 0 ≤ |C| + 1 := by positivity
    calc _ ≤ (|C| + 1) * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
          (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) :=
          mul_le_mul_of_nonneg_right hC hB0
      _ ≤ _ := mul_le_mul_of_nonneg_left hBle hK
  -- `Re(V - M) ≥ -‖V - M‖`
  have hRe : (mainTensor b E s X (u i) (u j) (u j) (u i)).re -
      ‖(V : ℂ) - mainTensor b E s X (u i) (u j) (u j) (u i)‖ ≤ V := by
    have := Complex.abs_re_le_norm ((V : ℂ) - mainTensor b E s X (u i) (u j) (u j) (u i))
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith [abs_le.mp this]
  linarith

/-- **`entryVariance`, pointwise in the energy** (strongest form obtained from
`PassiveCovarianceContract`): the field with `∀ κI, ∀ E ∈ bulkInterval κI` replaced by a
fixed bulk `E` chosen before `d, γ, c, W₀`.
-/
theorem entryVariance_pointwise (hPC : PassiveCovarianceContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∃ d γ c : ℝ, 0 < d ∧ 0 < γ ∧ 0 < c ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        jetDistance0 b E X ≤ d → jetDistance1 b E s X ≤ d →
        conductanceOf (passiveTransmission b E X) ≤ γ * W →
        ∀ (u : Fin W → Fin W → ℂ) (t : Fin W → ℝ),
          IsOrthonormalEigenbasis (passiveTransmission b E X) u t →
          ∀ i j, t i ≤ 1 / 2 → t j ≤ 1 / 2 →
            c / W ≤ ∫ ω, ‖star (u i) ⬝ᵥ ((freshU b E X ω -
                matrixExpect (layerLaw W b .oneBlockOnePort) (freshU b E X)) *ᵥ u j)‖ ^ 2
              ∂layerLaw W b .oneBlockOnePort := by
  intro b hb0 hb E h1 h2
  obtain ⟨⟨s₀, hs₀⟩, hall⟩ := hPC b hb0 hb E h1 h2
  obtain ⟨C, W₁, hC⟩ := hall s₀ hs₀
  have hη := etaZ_pos b E (by linarith) h1 h2
  set G := (sigmaPlus b - ‖sigmaMinus b E s₀‖) / (4 * etaZ b E ^ 2) with hGdef
  have hG : 0 < G := by
    have := norm_sigmaMinus_lt_sigmaPlus hb0 hb h1 h2 hs₀
    rw [hGdef]; exact div_pos (by linarith) (by positivity)
  set K := |C| + 1 with hKdef
  have hK : 0 < K := by positivity
  refine ⟨G / (16 * K), etaZ b E * G / (2 * K), G / 2, by positivity, by positivity,
    by positivity, max W₁ (⌈4 * K / G⌉₊ + 1), ?_⟩
  intro W hW s hs X hY hd0 hd1 hg u t hu i j hti htj
  obtain rfl : s = s₀ := stationaryJet_unique hb0 hb h1 h2 hs hs₀
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : ⌈4 * K / G⌉₊ + 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWpos : 0 < W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hWK : 4 * K / G ≤ W := by
    have := Nat.le_ceil (4 * K / G)
    have : ((⌈4 * K / G⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (Nat.le_succ _).trans hW2
    linarith
  have hcov : ‖bilinearCovariance (freshLaw W b) (freshU b E X) (u i) (u j) (u j) (u i) -
      mainTensor b E s X (u i) (u j) (u j) (u i)‖ ≤
      C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
        (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
        fourNorm (u i) (u j) (u j) (u i) := hC W hW1 X hY (u i) (u j) (u j) (u i)
  have key := entryVariance_of_covBound hb0 hb h1 h2 hs hWpos hY hd0 hd1 hg hu i j hti htj hcov
  show G / 2 / W ≤ ∫ ω, ‖bilinear (u i) (freshU b E X ω -
    matrixExpect (freshLaw W b) (freshU b E X)) (u j)‖ ^ 2 ∂freshLaw W b
  refine le_trans ?_ key
  -- `K(W⁻² + W⁻¹(2d + γ/(4η))) = K/W² + G/(4W) ≤ G/(2W)`
  have e1 : 2 * (G / (16 * K)) + etaZ b E * G / (2 * K) / (4 * etaZ b E) = G / (4 * K) := by
    field_simp; ring
  rw [e1]
  have hKW : K * (W : ℝ)⁻¹ ^ 2 ≤ G / 4 * (W : ℝ)⁻¹ := by
    rw [div_le_iff₀ hG] at hWK
    rw [pow_two, ← mul_assoc]
    have hinv : 0 < (W : ℝ)⁻¹ := inv_pos.mpr hWr
    have : K * (W : ℝ)⁻¹ ≤ G / 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hWr]; linarith
    exact mul_le_mul_of_nonneg_right this hinv.le
  have e2 : K * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (G / (4 * K))) =
      K * (W : ℝ)⁻¹ ^ 2 + G / 4 * (W : ℝ)⁻¹ := by field_simp
  rw [e2]
  have e3 : G / 2 / W = G / W - G / 4 * (W : ℝ)⁻¹ - G / 4 * (W : ℝ)⁻¹ := by ring
  rw [e3]
  linarith

/-- `entryVariance_pointwise` with `hPC` discharged by `passiveCovariance_holds` (Q7) from the
input hypotheses `GaussianAbsorptionContract`, `GaussianLpGradient`, `GaussianPoincare`.
-/
theorem entryVariance_pointwise_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∃ d γ c : ℝ, 0 < d ∧ 0 < γ ∧ 0 < c ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        jetDistance0 b E X ≤ d → jetDistance1 b E s X ≤ d →
        conductanceOf (passiveTransmission b E X) ≤ γ * W →
        ∀ (u : Fin W → Fin W → ℂ) (t : Fin W → ℝ),
          IsOrthonormalEigenbasis (passiveTransmission b E X) u t →
          ∀ i j, t i ≤ 1 / 2 → t j ≤ 1 / 2 →
            c / W ≤ ∫ ω, ‖star (u i) ⬝ᵥ ((freshU b E X ω -
                matrixExpect (layerLaw W b .oneBlockOnePort) (freshU b E X)) *ᵥ u j)‖ ^ 2
              ∂layerLaw W b .oneBlockOnePort :=
  entryVariance_pointwise (passiveCovariance_holds hGA hLp hP)

end BlockBand.Transmission.LawClauses
