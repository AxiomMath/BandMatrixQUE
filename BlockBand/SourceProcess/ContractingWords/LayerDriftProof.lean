module

public import BlockBand.SourceProcess.ContractingWords.LayerDriftAt
public import BlockBand.SourceProcess.ContractingWords.WordCovExp
public import BlockBand.SourceProcess.ContractingWords.SlotMean

/-!
# The one-layer drift of words

`layerDrift_of_pins`: the one-layer drift bound `LayerDrift`, under `GaussianAbsorptionContract`,
`GaussianLpGradient`, `GaussianPoincare` and the one-layer slot hypotheses `ProjGammaMean`,
`ProjGammaFluct`, `ProjSeparator.InjNearMeanW2` and `InjFarTrace`. The proof starts from
`word_drift_expand` (expansion to second order, error `C(1+g)²R`), then
* first order: `slot_mean` + `first_match` (Ward-mean terms → `contrOne`, `-(D₀g/2W)P` →
  `-(D₀g/2W)#P Tr w`, rest `O((1+g)e²)`);
* second order: `drift_second` (opposite-sign tensors → `W⁻¹ pairContraction`, same-sign →
  `contrTwo`, `|κ₂|,|κ₃| ≤ C/W ≤ Ce`);
* the drift evaluation `wordDrift_eval` (proved in `FullSourceGenerator`) with `½ Tr J² = g` (`half_trace_current`), `g ≤ K²/2` (`cond_le_K`);
* injection: `inj_mean` (`O(e²)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceGenerator BlockBand.Transmission.Bridge
open scoped Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

theorem slotMean_eq (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hT : ∀ σ i j, Integrable (fun y => transportedSep b E XX σ y i j) (freshLaw W b))
    {w : TraceWord nT nI} (hw : IsOrdinaryWord w) (p : Fin w.length) :
    slotMean (freshLaw W b) (slotDelta b E XX w) p =
      (if (w.get p).2 = .proj then matrixExpect (freshLaw W b) (transportedSep b E XX .proj)
        else matrixExpect (freshLaw W b) (transportedSep b E XX .id)) - sepOf b E XX (w.get p).2 := by
  rw [show slotMean (freshLaw W b) (slotDelta b E XX w) p = matrixExpect (freshLaw W b)
      (transportedSep b E XX (w.get p).2) - sepOf b E XX (w.get p).2 from
    matrixExpect_sub_const _ _ (hT _)]
  rcases hw.2 _ (List.get_mem w p) with h | h <;> rw [h] <;> simp

theorem contrDrift_sum (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (B : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (w : TraceWord nT nI) :
    ((contrDrift w).map fun Zs => ‖coreProd A B Zs‖).sum =
      ((contrOne w).map fun Zs => ‖coreProd A B Zs‖).sum +
        ((contrTwo w).map fun Zs => ‖coreProd A B Zs‖).sum := by
  simp [contrDrift, List.map_append, List.sum_append]

theorem sum_norm_nonneg (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (B : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (L : List (List (TraceWord nT nI))) :
    0 ≤ (L.map fun Zs => ‖coreProd A B Zs‖).sum :=
  List.sum_nonneg fun z hz => by obtain ⟨Zs, -, rfl⟩ := List.mem_map.mp hz; exact norm_nonneg _

theorem sq_le_layerRem (W d : ℕ) {e : ℝ} (he : 0 ≤ e) : e ^ 2 ≤ layerRem W d e := by
  simp only [layerRem]
  have : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by positivity
  have : 0 ≤ e ^ (2 * d + 4) := by positivity
  linarith

/-- The constant of `LayerDrift`. -/
abbrev driftConst (C1 C2 C3 Ck K : ℝ) (d : ℕ) : ℝ :=
  (2 * C2 + 2 * Ck) + (C3 + C1 * (1 + K ^ 2 / 2) ^ 2 + d * max 1 K ^ d * C2 * (1 + K ^ 2 / 2))

/-- **`LayerDrift` at one old two-port**, from the instantiated pieces. -/
theorem layerDrift_at {b E : ℝ} {s : ℂ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hη : 0 < etaZ b E) (hXX : XX.IsHermitian)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (q : Fin nI → ℝ → ℝ)
    (j d : ℕ) {K C1 C2 C3 Ck : ℝ} (hK : 0 ≤ K) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hCk : 0 ≤ Ck) (hA : ∀ ℓ, (A ℓ).IsHermitian) (hAK : ∀ ℓ, nuclearNorm (A ℓ) ≤ K)
    (hJ : A .current = currentOf b E XX) {w : TraceWord nT nI} (hw : IsOrdinaryWord w)
    (hwd : w.length ≤ d)
    (hX : ‖∫ y, posTr (wl A w) (slotSep b E XX w + slotDelta b E XX w y) ∂freshLaw W b -
        posTr (wl A w) (slotSep b E XX w) -
        ∑ p, posTr (wl A w) (pw (slotSep b E XX w)
          (slotMean (freshLaw W b) (slotDelta b E XX w)) {p}) -
        ∑ p, ∑ q ∈ Finset.Ioi p, ∑ k, fscK b E s W k * pairF (wl A w) (slotSep b E XX w) p q
          (slotSep b E XX w p * fscG b E XX k * slotSep b E XX w q)
          (slotSep b E XX w q * fscH b E XX k * slotSep b E XX w p)‖ ≤
      C1 * (1 + conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))) ^ 2 *
        layerRem W d (layerErr b E s XX))
    (hI : ‖∫ y, layerNew b E A (injCoef q W j) XX w y ∂freshLaw W b -
        ∫ y, layerNew b E A (fun _ => 0) XX w y ∂freshLaw W b -
        (W : ℂ)⁻¹ * wordInjection b q (stepTime W j) w‖ ≤ C3 * layerErr b E s XX ^ 2)
    {Ω Ω' : ℂ} (hΩ : ‖Ω‖ ≤ C2 * layerErr b E s XX) (hΩ' : ‖Ω'‖ ≤ C2 * layerErr b E s XX)
    (h1 : ‖matrixExpect (freshLaw W b) (transportedSep b E XX .id) - 1 -
      (Ω • (nearProjection W * twoPortScattering b E XX) +
        Ω' • ((twoPortScattering b E XX)ᴴ * nearProjection W))‖ ≤ C2 * layerErr b E s XX ^ 2)
    (h2 : ‖matrixExpect (freshLaw W b) (transportedSep b E XX .proj) - nearProjection W -
      (Ω • (nearProjection W * twoPortScattering b E XX * nearProjection W) +
        Ω' • (nearProjection W * (twoPortScattering b E XX)ᴴ * nearProjection W) -
        ((transportD0 b E * conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) /
          (2 * W) : ℝ) : ℂ) • nearProjection W)‖ ≤
      C2 * (1 + conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))) *
        layerErr b E s XX ^ 2)
    (hT : ∀ σ i j, Integrable (fun y => transportedSep b E XX σ y i j) (freshLaw W b))
    (hκ : ‖fscK b E s W 2‖ ≤ Ck * (W : ℝ)⁻¹ ∧ ‖fscK b E s W 3‖ ≤ Ck * (W : ℝ)⁻¹) :
    ‖∫ y, layerNew b E A (injCoef q W j) XX w y ∂freshLaw W b -
        coreProd A (sepOf b E XX) [w] - (W : ℂ)⁻¹ *
          MvPolynomial.eval (fun v => coreProd A (sepOf b E XX) [v])
            (wordDrift (transportD0 b E) w +
              MvPolynomial.C (wordInjection b q (stepTime W j) w))‖ ≤
      driftConst C1 C2 C3 Ck K d * layerErr b E s XX *
          ((contrDrift w).map fun Zs => ‖coreProd A (sepOf b E XX) Zs‖).sum +
        driftConst C1 C2 C3 Ck K d * layerRem W d (layerErr b E s XX) := by
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  obtain ⟨-, -, -, hWe, he0, hsum⟩ := layerErr_parts b E s XX hg (W := W)
  have hgK := cond_le_K hXX hη hJ (hA _) (hAK _)
  set g := conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))
  set e := layerErr b E s XX
  set R := layerRem W d e
  set B := sepOf b E XX
  simp only [posTr_new0, posTr_old, coreProd_one] at hX
  obtain ⟨ι, hι, c, x, y, hc, hxy, hrep⟩ := posCut_word A hA hAK hw.1
  have hσ : ∀ p, ‖B (w.get p).2‖ ≤ 1 := fun p => (sepOf_ord_herm (slot_ord hw p)).2
  have hρ : C2 * e ^ 2 ≤ C2 * (1 + g) * e ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hC2 hg) (sq_nonneg e)]
  have hm : ∀ p, ‖slotMean (freshLaw W b) (slotDelta b E XX w) p -
      (Ω • B (aSep (w.get p).2) + Ω' • B (bSep (w.get p).2) -
        (if (w.get p).2 = .proj then ((transportD0 b E * g / (2 * W) : ℝ) : ℂ) else 0) •
          B (w.get p).2)‖ ≤ C2 * (1 + g) * e ^ 2 := fun p =>
    slot_mean_form b E XX h1 h2 hρ (hw.2 _ (List.get_mem w p)) _ (slotMean_eq b E XX hT hw p)
  have hF := first_match A B w hrep hxy hc hσ _ Ω Ω' ((transportD0 b E * g / (2 * W) : ℝ) : ℂ)
    (by positivity) hm
  have hS := drift_second b E s XX A hJ hw hκ
  rw [show (fun v => coreProd A B [v]) = wval A B from funext (coreProd_one A B), coreProd_one,
    map_add, MvPolynomial.eval_C, wordDrift_eval A (ordTable_sepOf b E XX) _ hw,
    half_trace_current hXX hη hJ (hA _)]
  rw [drift_alg _ (∫ y, layerNew b E A (fun _ => 0) XX w y ∂freshLaw W b) _
    (∑ p, posTr (wl A w) (pw (slotSep b E XX w) (slotMean (freshLaw W b) (slotDelta b E XX w)) {p}))
    (∑ p, ∑ q ∈ Finset.Ioi p, ∑ k, fscK b E s W k * pairF (wl A w) (slotSep b E XX w) p q
          (slotSep b E XX w p * fscG b E XX k * slotSep b E XX w q)
          (slotSep b E XX w q * fscH b E XX k * slotSep b E XX w p)) _ _ _ _ _ _
    ((transportD0 b E * g / (2 * W) : ℝ) : ℂ) (by push_cast; ring)]
  refine (norm_add4_le _ _ _ _).trans ?_
  have hS₁ := sum_norm_nonneg A B (contrOne w)
  have hS₂ := sum_norm_nonneg A B (contrTwo w)
  have hKd : K ^ w.length ≤ max 1 K ^ d :=
    (pow_le_pow_left₀ hK (le_max_right 1 K) _).trans (pow_le_pow_right₀ (le_max_left 1 K) hwd)
  have hρ0 : 0 ≤ C2 * (1 + g) * e ^ 2 := by positivity
  have hF' := hF.trans (add_le_add (mul_le_mul_of_nonneg_right (add_le_add hΩ hΩ') hS₁)
    (mul_le_mul (by exact_mod_cast hwd) (mul_le_mul_of_nonneg_right hKd hρ0) (by positivity)
      (Nat.cast_nonneg d)))
  rw [contrDrift_sum]
  refine (drift_final hI hX hF' hS hWe (sq_le_layerRem W d he0) hg hgK hS₁ hS₂ hC3 hC1 hC2 hCk
    (Nat.cast_nonneg d) (by positivity) le_rfl he0).trans ?_
  have hR : 0 ≤ R := (sq_nonneg e).trans (sq_le_layerRem W d he0)
  have ha : 0 ≤ 2 * C2 + 2 * Ck := by positivity
  have hb : 0 ≤ C3 + C1 * (1 + K ^ 2 / 2) ^ 2 + d * max 1 K ^ d * C2 * (1 + K ^ 2 / 2) := by
    positivity
  have heS : 0 ≤ e * ((contrOne w).map fun Zs => ‖coreProd A B Zs‖).sum +
      e * ((contrTwo w).map fun Zs => ‖coreProd A B Zs‖).sum := by positivity
  simp only [driftConst]
  nlinarith [mul_nonneg hb heS, mul_nonneg ha hR]

/-- **`LayerDrift`** from the input hypotheses and the one-layer slot hypotheses. -/
theorem layerDrift_of_pins (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hΓm : ProjGammaMean) (hΓf : ProjGammaFluct)
    (hIn : BlockBand.SourceProcess.ProjSeparator.InjNearMeanW2) (hIf : InjFarTrace) :
    LayerDrift := by
  intro b hb0 hb κ hκ d K c₀ hK hc₀
  obtain ⟨C1, W1, hC1, hexp⟩ := word_drift_expand hGA hLp hP hΓf hb0 hb hκ d hK
  obtain ⟨C2, W2, hC2, hmean⟩ := slot_mean hGA hLp hΓm hb0 hb hκ
  obtain ⟨C3, W3, hC3, hinj⟩ := inj_mean hGA hLp hIn hIf hb0 hb hκ d hK hc₀
  obtain ⟨Ck, hCk, hκb⟩ := fscK_same_le hb0 hb hκ
  obtain ⟨μb, W4, -, hfb⟩ := fresh_basic hGA hb0 hb hκ
  refine ⟨driftConst C1 C2 C3 Ck K d, max (max W1 W2) (max W3 W4), by positivity, ?_⟩
  intro W hW E hE s hs XX hXX nT nI A q j hA hAK hJ hq w hw hwd
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW3, hW4⟩ := hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  obtain ⟨Ω, Ω', hΩ, hΩ', h1, h2⟩ := hmean W hW2 E hE s hs XX hXX
  exact layerDrift_at hη hXX A q j d hK hC1 hC2 hC3 hCk hA hAK hJ hw hwd
    (hexp W hW1 E hE s hs XX hXX nT nI A hA hAK w hw hwd)
    (hinj W hW3 E hE s hs XX hXX nT nI A q j hA hAK hq w hw hwd).2.2 hΩ hΩ' h1 h2
    (fun σ => (hfb W hW4 E hE XX hXX σ).1) (hκb W E hE s hs)

end BlockBand.SourceProcess.ContractingWords
