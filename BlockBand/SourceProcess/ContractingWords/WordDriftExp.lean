module

public import BlockBand.SourceProcess.ContractingWords.SlotCovDelta

/-!
# The one-layer drift of an ordinary word, expanded to second order

Measure `freshLaw W b`; deterministic Hermitian `𝕏`; Hermitian letters with `Tr|A| ≤ K`; ordinary
`w` with `|w| ≤ d`; `e = layerErr`, `R = layerRem W d e`.

`word_drift_expand hGA hLp hP hΓ`: `C, W₀` from `b, κ, d, K`;
`|E posTr(σ+Δ) - posTr σ - Σ_p posTr(pw σ m {p}) - Σ_{p<q} Σ_k κ_k pairF(p,q,B_pG_kB_q,B_qH_kB_p)|
 ≤ C(1+g)²R`, with `posTr(σ+Δ) = newWord A 0 N D S w`, `posTr σ = Tr w(𝕏)` (old), `m = slotMean`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.PassiveCovariance
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

theorem drift_final_arith {Γ Kd T1 ε μ₀ r d Ms Cc Cs G R : ℝ} (hΓ0 : 0 ≤ Γ) (hΓ : Γ ≤ Kd)
    (hT1 : T1 ≤ Ms * R) (hT0 : 0 ≤ T1) (hε : ε ≤ Cc * G * R) (hε0 : 0 ≤ ε) (hμ : μ₀ ^ 2 ≤ Cs ^ 2 * R)
    (hr : r ^ 2 ≤ d ^ 2) (hG : 1 ≤ G) :
    Γ * (T1 + r ^ 2 * (ε + μ₀ ^ 2)) ≤ Kd * (Ms + d ^ 2 * (Cc + Cs ^ 2)) * G * R := by
  have h1 : r ^ 2 * (ε + μ₀ ^ 2) ≤ d ^ 2 * ((Cc + Cs ^ 2) * G * R) := by
    have : ε + μ₀ ^ 2 ≤ (Cc + Cs ^ 2) * G * R := by nlinarith [sq_nonneg Cs]
    exact mul_le_mul hr this (by positivity) (sq_nonneg d)
  have h2 : T1 ≤ Ms * G * R := by
    have : 0 ≤ Ms * R := hT0.trans hT1
    nlinarith
  have h3 : 0 ≤ T1 + r ^ 2 * (ε + μ₀ ^ 2) := by positivity
  calc Γ * (T1 + r ^ 2 * (ε + μ₀ ^ 2)) ≤ Kd * (Ms * G * R + d ^ 2 * ((Cc + Cs ^ 2) * G * R)) :=
        mul_le_mul hΓ (add_le_add h2 h1) h3 (hΓ0.trans hΓ)
    _ = _ := by ring

theorem final_arith2 {Γ Kd T1 ε μ₀ rr d Ms Cc Cs G R : ℝ} (hΓ0 : 0 ≤ Γ) (hΓ : Γ ≤ Kd)
    (hT1 : T1 ≤ Ms * R) (hT0 : 0 ≤ T1) (hε : ε ≤ Cc * G * R) (hε0 : 0 ≤ ε) (hμ : μ₀ ^ 2 ≤ Cs ^ 2 * R)
    (hr : rr ≤ d ^ 2) (hrr0 : 0 ≤ rr) (hG : 1 ≤ G) :
    Γ * (T1 + rr * (ε + μ₀ ^ 2)) ≤ Kd * (Ms + d ^ 2 * (Cc + Cs ^ 2)) * G * R := by
  have h1 : rr * (ε + μ₀ ^ 2) ≤ d ^ 2 * ((Cc + Cs ^ 2) * G * R) := by
    have : ε + μ₀ ^ 2 ≤ (Cc + Cs ^ 2) * G * R := by nlinarith [sq_nonneg Cs]
    exact mul_le_mul hr this (by positivity) (sq_nonneg d)
  have h2 : T1 ≤ Ms * G * R := by
    have : 0 ≤ Ms * R := hT0.trans hT1
    nlinarith
  have h3 : 0 ≤ T1 + rr * (ε + μ₀ ^ 2) := by positivity
  calc Γ * (T1 + rr * (ε + μ₀ ^ 2)) ≤ Kd * (Ms * G * R + d ^ 2 * ((Cc + Cs ^ 2) * G * R)) :=
        mul_le_mul hΓ (add_le_add h2 h1) h3 (hΓ0.trans hΓ)
    _ = _ := by ring

/-- **The word-level drift expansion.** -/
theorem word_drift_expand (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hΓ : ProjGammaFluct) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ}
    (hκ : 0 < κ) (d : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (nT nI : ℕ) (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
        (∀ ℓ, (A ℓ).IsHermitian) → (∀ ℓ, nuclearNorm (A ℓ) ≤ K) →
      ∀ w : TraceWord nT nI, IsOrdinaryWord w → w.length ≤ d →
        ‖∫ y, posTr (wl A w) (slotSep b E XX w + slotDelta b E XX w y) ∂freshLaw W b -
            posTr (wl A w) (slotSep b E XX w) -
            ∑ p, posTr (wl A w) (pw (slotSep b E XX w)
              (slotMean (freshLaw W b) (slotDelta b E XX w)) {p}) -
            ∑ p, ∑ q ∈ Finset.Ioi p, ∑ k, fscK b E s W k * pairF (wl A w) (slotSep b E XX w) p q
              (slotSep b E XX w p * fscG b E XX k * slotSep b E XX w q)
              (slotSep b E XX w q * fscH b E XX k * slotSep b E XX w p)‖ ≤
          C * (1 + conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))) ^ 2 *
            layerRem W d (layerErr b E s XX) := by
  obtain ⟨Cs, Ws, hCs, hsl⟩ := slot_basic hGA hLp hb0 hb hκ (d + 2) (by omega)
  obtain ⟨Cc, Wc, hCc, hcv⟩ := slot_cov_delta hGA hLp hP hΓ hb0 hb hκ
  obtain ⟨μb, W₃, -, hfb⟩ := fresh_basic hGA hb0 hb hκ
  set Ms := 2 ^ d * d * (2 * (max 1 Cs ^ (d + 3) * 2 ^ (d + 3)))
  refine ⟨max 1 K ^ d * (Ms + d ^ 2 * (Cc + Cs ^ 2)), max (max Ws Wc) (max W₃ 1),
    by positivity, ?_⟩
  intro W hW E hE s hs XX hXX nT nI A hA hAK w hw hwd
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWs, hWc⟩, hW3, hW1⟩ := hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  obtain ⟨-, -, -, -, he0, -⟩ := layerErr_parts b E s XX hg (W := W)
  set g := conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))
  set e := layerErr b E s XX
  have hWr : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hx0 : 0 ≤ 1 / Real.sqrt W := by positivity
  have hx1 : 1 / Real.sqrt W ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.mpr hWr)]
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hW1)
  obtain ⟨hΔ, hent, hm⟩ := hsl W hWs E hE s XX hXX nT nI w hw
  obtain ⟨ι, hι, c, x, y, hc, hxy, hrep⟩ := posCut_word A hA hAK hw.1
  have hσ : ∀ p, ‖slotSep b E XX w p‖ ≤ 1 := fun p => (sepOf_ord_herm (slot_ord hw p)).2
  have hT := fun τ => (hfb W hW3 E hE XX hXX τ).1
  have hmean : ∀ p, slotMean (freshLaw W b) (slotDelta b E XX w) p =
      matrixExpect (freshLaw W b) (transportedSep b E XX (w.get p).2) -
        sepOf b E XX (w.get p).2 := fun p => matrixExpect_sub_const _ _ (hT _)
  have hε0 : 0 ≤ Cc * (1 + g) ^ 2 * ((W : ℝ)⁻¹ / Real.sqrt W + e ^ 2) := by positivity
  have hD := drift_abstract hrep hxy hσ hΔ (by positivity) (by omega) (by omega) hent hm
    (fun _ _ k => fscK b E s W k)
    (fun p q k => slotSep b E XX w p * fscG b E XX k * slotSep b E XX w q)
    (fun p q k => slotSep b E XX w q * fscH b E XX k * slotSep b E XX w p) hε0
    (fun p q _ u v u' v' hu hv hu' hv' => by
      rw [hmean, hmean]
      exact hcv W hWc E hE s hs XX hXX _ _ (slot_ord hw p) (slot_ord hw q) u v u' v' hu hv hu' hv')
  refine hD.trans ?_
  have hR := rem_parts hx0 he0 d
  have hcube := cube_eq hWr
  have hlr : layerRem W d e = (1 / Real.sqrt W) ^ 3 + e ^ 2 + e ^ (2 * d + 4) := by
    rw [hcube]; rfl
  rw [hlr]
  have hβ0 : 0 ≤ Cs * (1 / Real.sqrt W + e) := by positivity
  have hr3 := pow_rem_le hx0 hx1 he0 hCs (d := d) (m := 3) le_rfl (by omega)
  have hrr := pow_rem_le hx0 hx1 he0 hCs (d := d) (m := w.length + 3) (by omega) (by omega)
  have hpow : (2 : ℝ) ^ w.length * w.length ≤ 2 ^ d * d := by
    have h1 : (2 : ℝ) ^ w.length ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hwd
    have h2 : (w.length : ℝ) ≤ d := by exact_mod_cast hwd
    exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
  refine drift_final_arith (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (hc.trans ((pow_le_pow_left₀ hK (le_max_right 1 K) _).trans
      (pow_le_pow_right₀ (le_max_left 1 K) hwd))) ?_ (by positivity) ?_ hε0 ?_ ?_ ?_
  · calc (2 : ℝ) ^ w.length * w.length * ((Cs * (1 / Real.sqrt W + e)) ^ 3 +
          (Cs * (1 / Real.sqrt W + e)) ^ (w.length + 3)) ≤
          2 ^ d * d * (2 * (max 1 Cs ^ (d + 3) * 2 ^ (d + 3) *
            ((1 / Real.sqrt W) ^ 3 + e ^ 2 + e ^ (2 * d + 4)))) := by
          gcongr; linarith
      _ = _ := by simp only [Ms]; ring
  · rw [← hcube]
    exact mul_le_mul_of_nonneg_left hR.1 (by positivity)
  · calc (Cs * e) ^ 2 = Cs ^ 2 * e ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hR.2.1 (sq_nonneg _)
  · have : (w.length : ℝ) ≤ d := by exact_mod_cast hwd
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  · nlinarith

end BlockBand.SourceProcess.ContractingWords
