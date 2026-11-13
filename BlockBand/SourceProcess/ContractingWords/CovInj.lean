module

public import BlockBand.SourceProcess.ContractingWords.CovL2

/-!
# The injection in the one-layer covariance is `O(W^{-3/2} + e²)`

The one-layer covariance with the injected word differs from the one without it by
`O(W^{-3/2} + e²)`. Measure `freshLaw W b`; deterministic Hermitian `𝕏`; Hermitian letters with
`Tr|A_ℓ| ≤ K`; tests `|q_a| ≤ c₀`; ordinary words `w, v` with `|w|, |v| ≤ d`.

`cov_inj hGA hLp`: with `a = new_c - old`, `a⁰ = new_0 - old`, `i = new_c - new_0`,
`a_wa_v - a⁰_wa⁰_v = a_w i_v + i_w a⁰_v`, and `|E fg| ≤ (tE|f|² + t⁻¹E|g|²)/2`, `t = W^{∓1/2}`,
`E|a|² ≤ (C(W^{-1/2} + e))²` (`new_old_L2`), `E|i|² ≤ (C/W)²` (`inj_L2`):
`|E a_wa_v - E a⁰_wa⁰_v| ≤ C layerRem W d e`; `a⁰_wa⁰_v` is integrable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.Bridge
open scoped ENNReal Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

theorem cov_inj_arith {u e Cb Cg F1 F2 G1 G2 X1 X2 Ek : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hEk : 0 ≤ Ek) (hF1 : F1 ≤ (Cb * (u + e)) ^ 2) (hF2 : F2 ≤ (Cb * (u + e)) ^ 2)
    (hG1 : G1 ≤ (Cg * u ^ 2) ^ 2) (hG2 : G2 ≤ (Cg * u ^ 2) ^ 2)
    (hX1 : X1 ≤ (u * F1 + u⁻¹ * G1) / 2) (hX2 : X2 ≤ (u⁻¹ * G2 + u * F2) / 2) :
    X1 + X2 ≤ (2 * Cb ^ 2 + Cg ^ 2) * (u ^ 3 + e ^ 2 + Ek) := by
  have hui : 0 < u⁻¹ := inv_pos.mpr hu
  have a1 : u * F1 ≤ 2 * Cb ^ 2 * u ^ 3 + 2 * Cb ^ 2 * e ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hF1 hu.le
    have : u * (Cb * (u + e)) ^ 2 ≤ 2 * Cb ^ 2 * u ^ 3 + 2 * Cb ^ 2 * e ^ 2 := by
      have h1 : u * (Cb * (u + e)) ^ 2 = Cb ^ 2 * (u * (u + e) ^ 2) := by ring
      have h2 : u * (u + e) ^ 2 ≤ 2 * u ^ 3 + 2 * e ^ 2 := by
        nlinarith [sq_nonneg (u - e), mul_nonneg hu.le (sq_nonneg (u - e)),
          mul_le_mul_of_nonneg_right hu1 (sq_nonneg e)]
      rw [h1]; nlinarith [sq_nonneg Cb]
    linarith
  have a2 : u * F2 ≤ 2 * Cb ^ 2 * u ^ 3 + 2 * Cb ^ 2 * e ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hF2 hu.le
    have : u * (Cb * (u + e)) ^ 2 ≤ 2 * Cb ^ 2 * u ^ 3 + 2 * Cb ^ 2 * e ^ 2 := by
      have h1 : u * (Cb * (u + e)) ^ 2 = Cb ^ 2 * (u * (u + e) ^ 2) := by ring
      have h2 : u * (u + e) ^ 2 ≤ 2 * u ^ 3 + 2 * e ^ 2 := by
        nlinarith [sq_nonneg (u - e), mul_nonneg hu.le (sq_nonneg (u - e)),
          mul_le_mul_of_nonneg_right hu1 (sq_nonneg e)]
      rw [h1]; nlinarith [sq_nonneg Cb]
    linarith
  have hc : u⁻¹ * (Cg * u ^ 2) ^ 2 = Cg ^ 2 * u ^ 3 := by field_simp
  have b1 : u⁻¹ * G1 ≤ Cg ^ 2 * u ^ 3 := (mul_le_mul_of_nonneg_left hG1 hui.le).trans hc.le
  have b2 : u⁻¹ * G2 ≤ Cg ^ 2 * u ^ 3 := (mul_le_mul_of_nonneg_left hG2 hui.le).trans hc.le
  have : 0 ≤ (2 * Cb ^ 2 + Cg ^ 2) * Ek := by positivity
  have : 0 ≤ Cg ^ 2 * e ^ 2 := by positivity
  nlinarith

theorem sqrt_facts (hW : 1 ≤ W) :
    0 < (Real.sqrt W)⁻¹ ∧ (Real.sqrt W)⁻¹ ≤ 1 ∧ (W : ℝ)⁻¹ = ((Real.sqrt W)⁻¹) ^ 2 ∧
      (W : ℝ)⁻¹ / Real.sqrt W = ((Real.sqrt W)⁻¹) ^ 3 ∧ 1 / Real.sqrt W = (Real.sqrt W)⁻¹ := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hs : 1 ≤ Real.sqrt W := Real.one_le_sqrt.mpr hW1
  have hs0 : 0 < Real.sqrt W := by linarith
  have hsq : Real.sqrt W ^ 2 = W := Real.sq_sqrt (by linarith)
  refine ⟨inv_pos.mpr hs0, inv_le_one_of_one_le₀ hs, ?_, ?_, one_div _⟩
  · rw [inv_pow, hsq]
  · rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, inv_pow, hsq, div_eq_mul_inv]

/-- **The injected covariance.** -/
theorem cov_inj (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (d : ℕ) {K c₀ : ℝ} (hK : 0 ≤ K)
    (hc₀ : 0 ≤ c₀) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (nT nI : ℕ) (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        (q : Fin nI → ℝ → ℝ) (j : ℕ), (∀ ℓ, (A ℓ).IsHermitian) → (∀ ℓ, nuclearNorm (A ℓ) ≤ K) →
        (∀ a x, |q a x| ≤ c₀) →
      ∀ w v : TraceWord nT nI, IsOrdinaryWord w → IsOrdinaryWord v → w.length ≤ d →
        v.length ≤ d →
        ‖∫ y, (layerNew b E A (injCoef q W j) XX w y - coreProd A (sepOf b E XX) [w]) *
              (layerNew b E A (injCoef q W j) XX v y - coreProd A (sepOf b E XX) [v])
              ∂freshLaw W b -
          ∫ y, (layerNew b E A (fun _ => 0) XX w y - coreProd A (sepOf b E XX) [w]) *
              (layerNew b E A (fun _ => 0) XX v y - coreProd A (sepOf b E XX) [v])
              ∂freshLaw W b‖ ≤ C * layerRem W d (layerErr b E s XX) := by
  obtain ⟨Cb, Wb, hCb, hL2⟩ := new_old_L2 hGA hLp hb0 hb hκ d hK hc₀
  obtain ⟨Cg, Wg, hCg, hI2⟩ := inj_L2 hGA hb0 hb hκ d hK hc₀
  refine ⟨2 * Cb ^ 2 + Cg ^ 2, max (max Wb Wg) 1, by positivity, ?_⟩
  intro W hW E hE s hs XX hXX nT nI A q j hA hAK hq w v hw hv hwd hvd
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWg⟩, hW1⟩ := hW
  have hc := fun ℓ => injCoef_le (nT := nT) (W := W) hc₀ hq j ℓ
  have hc0 : ∀ ℓ : TraceLetter nT nI, |(fun _ => (0 : ℝ)) ℓ| ≤ c₀ / (W : ℝ) ^ 2 := fun _ => by
    simp only [abs_zero]; positivity
  obtain ⟨hicw, haw2, haw⟩ := hL2 W hWb E hE s hs XX hXX nT nI A _ hA hAK hc w hw hwd
  obtain ⟨hicv, hav2, hav⟩ := hL2 W hWb E hE s hs XX hXX nT nI A _ hA hAK hc v hv hvd
  obtain ⟨hi0w, ha0w2, ha0w⟩ := hL2 W hWb E hE s hs XX hXX nT nI A _ hA hAK hc0 w hw hwd
  obtain ⟨hi0v, ha0v2, ha0v⟩ := hL2 W hWb E hE s hs XX hXX nT nI A _ hA hAK hc0 v hv hvd
  obtain ⟨hiw2, hiw⟩ := hI2 W hWg E hE XX hXX nT nI A _ hA hAK hc w hw.1 hwd hicw hi0w
  obtain ⟨hiv2, hiv⟩ := hI2 W hWg E hE XX hXX nT nI A _ hA hAK hc v hv.1 hvd hicv hi0v
  set ow := coreProd A (sepOf b E XX) [w]
  set ov := coreProd A (sepOf b E XX) [v]
  set nw := fun y => layerNew b E A (injCoef q W j) XX w y
  set nv := fun y => layerNew b E A (injCoef q W j) XX v y
  set mw := fun y => layerNew b E A (fun _ => 0) XX w y
  set mv := fun y => layerNew b E A (fun _ => 0) XX v y
  have maw : AEStronglyMeasurable (fun y => nw y - ow) (freshLaw W b) :=
    (hicw.sub (integrable_const _)).aestronglyMeasurable
  have mav : AEStronglyMeasurable (fun y => nv y - ov) (freshLaw W b) :=
    (hicv.sub (integrable_const _)).aestronglyMeasurable
  have ma0w : AEStronglyMeasurable (fun y => mw y - ow) (freshLaw W b) :=
    (hi0w.sub (integrable_const _)).aestronglyMeasurable
  have ma0v : AEStronglyMeasurable (fun y => mv y - ov) (freshLaw W b) :=
    (hi0v.sub (integrable_const _)).aestronglyMeasurable
  have miw : AEStronglyMeasurable (fun y => nw y - mw y) (freshLaw W b) :=
    (hicw.sub hi0w).aestronglyMeasurable
  have miv : AEStronglyMeasurable (fun y => nv y - mv y) (freshLaw W b) :=
    (hicv.sub hi0v).aestronglyMeasurable
  have I1 := integrable_mul_of_sq maw mav haw2 hav2
  have I0 := integrable_mul_of_sq ma0w ma0v ha0w2 ha0v2
  have I2 := integrable_mul_of_sq maw miv haw2 hiv2
  have I3 := integrable_mul_of_sq miw ma0v hiw2 ha0v2
  have e : ∫ y, (nw y - ow) * (nv y - ov) ∂freshLaw W b - ∫ y, (mw y - ow) * (mv y - ov)
      ∂freshLaw W b = ∫ y, (nw y - ow) * (nv y - mv y) ∂freshLaw W b +
        ∫ y, (nw y - mw y) * (mv y - ov) ∂freshLaw W b := by
    rw [← integral_sub I1 I0, ← integral_add I2 I3]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  rw [e]
  obtain ⟨hu0, hu1, hWu, hWu3, hdiv⟩ := sqrt_facts hW1
  obtain ⟨u, hu⟩ : ∃ u, u = (Real.sqrt W)⁻¹ := ⟨_, rfl⟩
  rw [← hu] at hu0 hu1 hWu hWu3 hdiv
  have hX1 := norm_integral_mul_le_amgm haw2 hiv2 hu0
  have hX2 := norm_integral_mul_le_amgm hiw2 ha0v2 (inv_pos.mpr hu0)
  rw [inv_inv] at hX2
  rw [hdiv] at haw ha0v
  rw [hWu] at hiw hiv
  have hR : layerRem W d (layerErr b E s XX) = u ^ 3 + layerErr b E s XX ^ 2 +
      layerErr b E s XX ^ (2 * d + 4) := by rw [layerRem, hWu3]
  rw [hR]
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  obtain ⟨-, -, -, -, he0, -⟩ := layerErr_parts b E s XX hg (W := W)
  refine (norm_add_le _ _).trans ?_
  exact cov_inj_arith hu0 hu1 (by positivity) haw ha0v hiv hiw hX1 hX2

end BlockBand.SourceProcess.ContractingWords
