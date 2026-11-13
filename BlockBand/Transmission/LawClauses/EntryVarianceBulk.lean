module

public import BlockBand.Transmission.LawClauses.EntryVariance
public import BlockBand.Transmission.PassiveCovarianceBulk.Statement
public import BlockBand.Transmission.PathScalar.MeanBulk

/-!
# `TransmissionLawContract.entryVariance`, uniformly on the bulk

`entryVariance_of_bulk`: the entry-variance lower bound from the bulk-uniform covariance bound
`CovarianceBulk.PassiveCovarianceBulk` (constants `C, W₀` uniform on `bulkInterval κI`), using
two deterministic uniform lower bounds on `bulkInterval κI` (no measure):
* `η ≥ η_L = etaLow b κI` (`etaLow_le`) and `η ≤ 1` (`bulk_eta_le_one`);
* **`gapLow_le`**: `σ₊ - |σ₋(s)| ≥ Γ_L = g(1-b)/(b(b+g))` at every stationary jet, with
  `g = kGap b κI > 0` (`bulk_kMinus`: `|k₋|d_* ≤ 1-b-g`, from `|k₋|² = k² - 4cb²(Im a)²`,
  `(Im a)² ≥ min(κI,2)/2`).
Proof of `gapLow_le`: `|σ₋| ≤ K/(1-Kd_*) ≤ K/(b+g)` (`K = |k₋|`, `jet_denom_lower`), and
`k/b - (1-b-g)/(d_*(b+g)) = g(1-b)/(b(b+g))` since `kd_* = 1-b`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PathScalar BlockBand.Transmission.CovarianceBulk
open scoped ComplexConjugate ComplexOrder

/-- The uniform lower bound `Γ_L = g(1-b)/(b(b+g))` of the jet gap on `bulkInterval κ`. -/
def gapLow (b κ : ℝ) : ℝ := kGap b κ * (1 - b) / (b * (b + kGap b κ))

theorem gapLow_pos {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) : 0 < gapLow b κ := by
  have hg := kGap_pos hb0 hb hκ
  have : 0 < 1 - b := by linarith
  unfold gapLow; positivity

/-- **Uniform jet gap**: `Γ_L ≤ σ₊ - |σ₋(s)|` for `E ∈ bulkInterval κ` and every stationary jet. -/
theorem gapLow_le {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s) :
    gapLow b κ ≤ sigmaPlus b - ‖sigmaMinus b E s‖ := by
  set K := ‖kMinus b E‖
  set g := kGap b κ
  have hg := kGap_pos hb0 hb hκ
  have hKd : K * dStar b ≤ 1 - b - g := bulk_kMinus hb0 hb hκ hE
  have hlow := jet_denom_lower (b := b) (E := E) s hs.2
  have h1b : 0 < 1 - b := by linarith
  have hd : dStar b * (1 - b) = 1 := by rw [dStar]; field_simp
  have hbg : 0 < b + g := by linarith
  have hD : b + g ≤ ‖1 + kMinus b E * s‖ := by linarith
  have hK0 : 0 ≤ K := norm_nonneg _
  -- `|σ₋| ≤ K/(b+g)`
  have hσ : ‖sigmaMinus b E s‖ ≤ K / (b + g) := by
    rw [sigmaMinus, norm_div]
    exact div_le_div_of_nonneg_left hK0 hbg hD
  -- `K ≤ (1-b)(1-b-g)`
  have hK : K ≤ (1 - b) * (1 - b - g) := by
    have := mul_le_mul_of_nonneg_left hKd h1b.le
    nlinarith
  have hσ' : ‖sigmaMinus b E s‖ ≤ (1 - b) * (1 - b - g) / (b + g) :=
    hσ.trans (div_le_div_of_nonneg_right hK hbg.le)
  have heq : sigmaPlus b - (1 - b) * (1 - b - g) / (b + g) = gapLow b κ := by
    rw [sigmaPlus, kPlus, gapLow]
    field_simp
    ring
  linarith

/-- The uniform lower bound `G_L = Γ_L/4` of `G = (σ₊-|σ₋|)/(4η²)` on `bulkInterval κ`. -/
theorem gapLow_div_le {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s) :
    gapLow b κ / 4 ≤ (sigmaPlus b - ‖sigmaMinus b E s‖) / (4 * etaZ b E ^ 2) := by
  have h1 : -2 < E := (bulk_bounds hκ hE).1
  have h2 : E < 2 := (bulk_bounds hκ hE).2
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hη1 := bulk_eta_le_one hb0 hκ hE
  have hG := gapLow_le hb0 hb hκ hE hs
  have hΓ := gapLow_pos hb0 hb hκ
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have : etaZ b E ^ 2 ≤ 1 := by nlinarith
  nlinarith

/-- The arithmetic closing step: `K/W² + G/(4W) ≤ G/(2W)` for `W ≥ 4K/G`, so
`G/W - K(W⁻² + W⁻¹·G/(4K)) ≥ G/(2W)`. -/
theorem entryVariance_arith {K G : ℝ} {W : ℕ} (hK : 0 < K) (hG : 0 < G) (hWr : (0 : ℝ) < W)
    (hWK : 4 * K / G ≤ W) :
    G / 2 / W ≤ G / W - K * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (G / (4 * K))) := by
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

/-- **`TransmissionLawContract.entryVariance`** (with exactly the field type), from the bulk-uniform
covariance bound.
-/
theorem entryVariance_of_bulk (hPCB : PassiveCovarianceBulk) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∃ d γ c : ℝ, 0 < d ∧ 0 < γ ∧ 0 < c ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        jetDistance0 b E X ≤ d → jetDistance1 b E s X ≤ d →
        conductanceOf (passiveTransmission b E X) ≤ γ * W →
        ∀ (u : Fin W → Fin W → ℂ) (t : Fin W → ℝ),
          IsOrthonormalEigenbasis (passiveTransmission b E X) u t →
          ∀ i j, t i ≤ 1 / 2 → t j ≤ 1 / 2 →
            c / W ≤ ∫ ω, ‖star (u i) ⬝ᵥ ((freshU b E X ω -
                matrixExpect (layerLaw W b .oneBlockOnePort) (freshU b E X)) *ᵥ u j)‖ ^ 2
              ∂layerLaw W b .oneBlockOnePort := by
  intro b hb0 hb κ hκ
  obtain ⟨C, W₁, hC⟩ := hPCB b hb0 hb κ hκ
  set Gl := gapLow b κ / 4 with hGldef
  have hGl : 0 < Gl := by have := gapLow_pos hb0 hb hκ; rw [hGldef]; positivity
  set ηL := etaLow b κ
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ
  set K := |C| + 1 with hKdef
  have hK : 0 < K := by positivity
  refine ⟨Gl / (16 * K), ηL * Gl / (2 * K), Gl / 2, by positivity, by positivity,
    by positivity, max W₁ (⌈4 * K / Gl⌉₊ + 1), ?_⟩
  intro W hW E hE s hs X hY hd0 hd1 hg u t hu i j hti htj
  have h1 : -2 < E := (bulk_bounds hκ hE).1
  have h2 : E < 2 := (bulk_bounds hκ hE).2
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hηle : ηL ≤ etaZ b E := etaLow_le (by linarith) hκ hE
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : ⌈4 * K / Gl⌉₊ + 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWpos : 0 < W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hWK : 4 * K / Gl ≤ W := by
    have := Nat.le_ceil (4 * K / Gl)
    have : ((⌈4 * K / Gl⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (Nat.le_succ _).trans hW2
    linarith
  have hcov : ‖bilinearCovariance (freshLaw W b) (freshU b E X) (u i) (u j) (u j) (u i) -
      mainTensor b E s X (u i) (u j) (u j) (u i)‖ ≤
      C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
        (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
        fourNorm (u i) (u j) (u j) (u i) := hC W hW1 E hE s hs X hY (u i) (u j) (u j) (u i)
  have key := entryVariance_of_covBound hb0 hb h1 h2 hs hWpos hY hd0 hd1 hg hu i j hti htj hcov
  show Gl / 2 / W ≤ ∫ ω, ‖bilinear (u i) (freshU b E X ω -
    matrixExpect (freshLaw W b) (freshU b E X)) (u j)‖ ^ 2 ∂freshLaw W b
  refine le_trans ?_ key
  set G := (sigmaPlus b - ‖sigmaMinus b E s‖) / (4 * etaZ b E ^ 2)
  have hGG : Gl ≤ G := gapLow_div_le hb0 hb hκ hE hs
  -- `2d + γ/(4η) ≤ G_L/(4K)`
  have hγη : ηL * Gl / (2 * K) / (4 * etaZ b E) ≤ Gl / (8 * K) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ Gl * (8 * K) := by positivity
    nlinarith
  have hsum : 2 * (Gl / (16 * K)) + ηL * Gl / (2 * K) / (4 * etaZ b E) ≤ Gl / (4 * K) := by
    have e : 2 * (Gl / (16 * K)) + Gl / (8 * K) = Gl / (4 * K) := by field_simp; ring
    linarith
  have hinv : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr hWr.le
  have herr : K * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
        (2 * (Gl / (16 * K)) + ηL * Gl / (2 * K) / (4 * etaZ b E))) ≤
      K * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (Gl / (4 * K))) := by
    gcongr
  have hmain : Gl / W ≤ G / W := div_le_div_of_nonneg_right hGG hWr.le
  have harith := entryVariance_arith hK hGl hWr hWK
  linarith

end BlockBand.Transmission.LawClauses
