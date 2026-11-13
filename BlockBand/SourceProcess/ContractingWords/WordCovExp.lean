module

public import BlockBand.SourceProcess.ContractingWords.WordDriftExp

/-!
# The one-layer covariance of two ordinary words, expanded

`word_cov_expand`: the one-layer covariance of the increments of two ordinary words is the sum,
over pairs of slots, of the cross functionals `crossF` against the four full-source covariance
tensors, up to `C(1 + g)²` times the one-layer remainder `layerRem`, uniformly on the bulk.
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

theorem cov_T1 {x e Cs : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (he0 : 0 ≤ e) (hCs : 0 ≤ Cs)
    {d a c : ℕ} (ha : a ≤ d) (hc : c ≤ d) :
    (2 : ℝ) ^ a * 2 ^ c * ((a + c : ℕ) * ((Cs * (x + e)) ^ 3 + (Cs * (x + e)) ^ (a + c + 3))) ≤
      2 ^ d * 2 ^ d * ((2 * d : ℕ) * (2 * (max 1 Cs ^ (2 * d + 3) * 2 ^ (2 * d + 3)))) *
        (x ^ 3 + e ^ 2 + e ^ (2 * d + 4)) := by
  have hr3 := pow_rem_le' hx0 hx1 he0 hCs (d := d) (m := 3) (D := 2 * d + 3) le_rfl (by omega)
    (by omega)
  have hrr := pow_rem_le' hx0 hx1 he0 hCs (d := d) (m := a + c + 3) (D := 2 * d + 3)
    (by omega) (by omega) (by omega)
  have h1 : (2 : ℝ) ^ a ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) ha
  have h2 : (2 : ℝ) ^ c ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hc
  have h3 : ((a + c : ℕ) : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast (by omega : a + c ≤ 2 * d)
  have hb3 : (Cs * (x + e)) ^ 3 + (Cs * (x + e)) ^ (a + c + 3) ≤
      2 * (max 1 Cs ^ (2 * d + 3) * 2 ^ (2 * d + 3) * (x ^ 3 + e ^ 2 + e ^ (2 * d + 4))) := by
    linarith
  have hb0 : 0 ≤ (Cs * (x + e)) ^ 3 + (Cs * (x + e)) ^ (a + c + 3) := by positivity
  have h12 : (2 : ℝ) ^ a * 2 ^ c ≤ 2 ^ d * 2 ^ d := mul_le_mul h1 h2 (by positivity) (by positivity)
  calc _ ≤ 2 ^ d * 2 ^ d * ((2 * d : ℕ) * (2 * (max 1 Cs ^ (2 * d + 3) * 2 ^ (2 * d + 3) *
        (x ^ 3 + e ^ 2 + e ^ (2 * d + 4))))) :=
        mul_le_mul h12 (mul_le_mul h3 hb3 hb0 (Nat.cast_nonneg _)) (by positivity) (by positivity)
    _ = _ := by ring

/-- **The word-level covariance expansion.** -/
theorem word_cov_expand (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hΓ : ProjGammaFluct) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ}
    (hκ : 0 < κ) (d : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (nT nI : ℕ) (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
        (∀ ℓ, (A ℓ).IsHermitian) → (∀ ℓ, nuclearNorm (A ℓ) ≤ K) →
      ∀ w v : TraceWord nT nI, IsOrdinaryWord w → IsOrdinaryWord v → w.length ≤ d →
        v.length ≤ d →
        ‖∫ y, (posTr (wl A w) (slotSep b E XX w + slotDelta b E XX w y) -
                posTr (wl A w) (slotSep b E XX w)) *
              (posTr (wl A v) (slotSep b E XX v + slotDelta b E XX v y) -
                posTr (wl A v) (slotSep b E XX v)) ∂freshLaw W b -
            ∑ p, ∑ q, ∑ k, fscK b E s W k * crossF (wl A w) (slotSep b E XX w) (wl A v)
              (slotSep b E XX v) p q (slotSep b E XX w p * fscG b E XX k * slotSep b E XX v q)
              (slotSep b E XX v q * fscH b E XX k * slotSep b E XX w p)‖ ≤
          C * (1 + conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))) ^ 2 *
            layerRem W d (layerErr b E s XX) := by
  obtain ⟨Cs, Ws, hCs, hsl⟩ := slot_basic hGA hLp hb0 hb hκ (2 * d + 2) (by omega)
  obtain ⟨Cc, Wc, hCc, hcv⟩ := slot_cov_delta hGA hLp hP hΓ hb0 hb hκ
  obtain ⟨μb, W₃, -, hfb⟩ := fresh_basic hGA hb0 hb hκ
  set Ms := 2 ^ d * 2 ^ d * ((2 * d : ℕ) * (2 * (max 1 Cs ^ (2 * d + 3) * 2 ^ (2 * d + 3))))
  refine ⟨max 1 K ^ d * max 1 K ^ d * (Ms + d ^ 2 * (Cc + Cs ^ 2)),
    max (max Ws Wc) (max W₃ 1), by positivity, ?_⟩
  intro W hW E hE s hs XX hXX nT nI A hA hAK w v hw hv hwd hvd
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
  obtain ⟨hΔ', hent', hm'⟩ := hsl W hWs E hE s XX hXX nT nI v hv
  obtain ⟨ι, hι, c, x, y, hc, hxy, hrep⟩ := posCut_word A hA hAK hw.1
  obtain ⟨ι', hι', c', x', y', hc', hxy', hrep'⟩ := posCut_word A hA hAK hv.1
  have hσ : ∀ p, ‖slotSep b E XX w p‖ ≤ 1 := fun p => (sepOf_ord_herm (slot_ord hw p)).2
  have hσ' : ∀ p, ‖slotSep b E XX v p‖ ≤ 1 := fun p => (sepOf_ord_herm (slot_ord hv p)).2
  have hT := fun τ => (hfb W hW3 E hE XX hXX τ).1
  have hmean : ∀ (u : TraceWord nT nI) (p : Fin u.length),
      slotMean (freshLaw W b) (slotDelta b E XX u) p =
        matrixExpect (freshLaw W b) (transportedSep b E XX (u.get p).2) -
          sepOf b E XX (u.get p).2 := fun u p => matrixExpect_sub_const _ _ (hT _)
  have hε0 : 0 ≤ Cc * (1 + g) ^ 2 * ((W : ℝ)⁻¹ / Real.sqrt W + e ^ 2) := by positivity
  have hD := cov_abstract hrep hxy hrep' hxy' hσ hσ' hΔ hΔ' (by positivity) (by omega) (by omega)
    hm hm' (fun _ _ k => fscK b E s W k)
    (fun p q k => slotSep b E XX w p * fscG b E XX k * slotSep b E XX v q)
    (fun p q k => slotSep b E XX v q * fscH b E XX k * slotSep b E XX w p) hε0
    (fun p q u₁ v₁ u₂ v₂ h₁ h₂ h₃ h₄ => by
      rw [hmean, hmean]
      exact hcv W hWc E hE s hs XX hXX _ _ (slot_ord hw p) (slot_ord hv q) u₁ v₁ u₂ v₂ h₁ h₂ h₃ h₄)
  refine hD.trans ?_
  have hR := rem_parts hx0 he0 d
  have hcube := cube_eq hWr
  have hlr : layerRem W d e = (1 / Real.sqrt W) ^ 3 + e ^ 2 + e ^ (2 * d + 4) := by
    rw [hcube]; rfl
  rw [hlr]
  have hKd : ∀ u : TraceWord nT nI, u.length ≤ d → K ^ u.length ≤ max 1 K ^ d := fun u hu =>
    (pow_le_pow_left₀ hK (le_max_right 1 K) _).trans (pow_le_pow_right₀ (le_max_left 1 K) hu)
  have hΓ0 := mul_nonneg (Finset.sum_nonneg fun l (_ : l ∈ Finset.univ) => norm_nonneg (c l))
    (Finset.sum_nonneg fun l (_ : l ∈ Finset.univ) => norm_nonneg (c' l))
  have hΓ := mul_le_mul (hc.trans (hKd w hwd)) (hc'.trans (hKd v hvd))
    (Finset.sum_nonneg fun l _ => norm_nonneg (c' l)) (by positivity)
  have hrr' : ((w.length : ℝ) * v.length) ≤ d ^ 2 := by
    have h1 : (w.length : ℝ) ≤ d := by exact_mod_cast hwd
    have h2 : (v.length : ℝ) ≤ d := by exact_mod_cast hvd
    nlinarith [Nat.cast_nonneg (α := ℝ) w.length, Nat.cast_nonneg (α := ℝ) v.length]
  have hT1 := cov_T1 hx0 hx1 he0 hCs hwd hvd
  have hεR : Cc * (1 + g) ^ 2 * ((W : ℝ)⁻¹ / Real.sqrt W + e ^ 2) ≤
      Cc * (1 + g) ^ 2 * ((1 / Real.sqrt W) ^ 3 + e ^ 2 + e ^ (2 * d + 4)) := by
    rw [← hcube]; exact mul_le_mul_of_nonneg_left hR.1 (by positivity)
  have hμ : (Cs * e) ^ 2 ≤ Cs ^ 2 * ((1 / Real.sqrt W) ^ 3 + e ^ 2 + e ^ (2 * d + 4)) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hR.2.1 (sq_nonneg _)
  have hG : (1 : ℝ) ≤ (1 + g) ^ 2 := by nlinarith
  exact final_arith2 (Cs := Cs) (μ₀ := Cs * e) hΓ0 hΓ hT1 (by positivity) hεR hε0 hμ hrr'
    (by positivity) hG

end BlockBand.SourceProcess.ContractingWords
