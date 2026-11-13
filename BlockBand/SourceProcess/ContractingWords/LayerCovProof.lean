module

public import BlockBand.SourceProcess.ContractingWords.CovInj

/-!
# The one-layer covariance of words

`layerCov_of_pins`: the one-layer covariance bound `LayerCov`. The proof combines
`word_cov_expand` (error `C(1+g)²R`), `cov_second` (opposite-sign tensors → `W⁻¹ crossContraction`,
same-sign → `contrCov`), `wordCov_eval`, `cov_inj` (the injection, `O(R)`) and `g ≤ K²/2`.
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

theorem cov_final {a b c e R S W' Cx Cj Ck g K : ℝ} (ha : a ≤ Cj * R)
    (hb : b ≤ Cx * (1 + g) ^ 2 * R) (hc : c ≤ 2 * (Ck * W') * S) (hWe : W' ≤ e) (hR : 0 ≤ R)
    (hS : 0 ≤ S) (hg0 : 0 ≤ g) (hg : g ≤ K ^ 2 / 2) (hCx : 0 ≤ Cx) (hCj : 0 ≤ Cj) (hCk : 0 ≤ Ck)
    (he : 0 ≤ e) :
    a + b + c ≤ (2 * Ck + Cj + Cx * (1 + K ^ 2 / 2) ^ 2) * e * S +
      (2 * Ck + Cj + Cx * (1 + K ^ 2 / 2) ^ 2) * R := by
  have hg2 : (1 + g) ^ 2 ≤ (1 + K ^ 2 / 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h1 : Cx * (1 + g) ^ 2 * R ≤ Cx * (1 + K ^ 2 / 2) ^ 2 * R :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg2 hCx) hR
  have h2 : 2 * (Ck * W') * S ≤ 2 * Ck * e * S := by
    have := mul_le_mul_of_nonneg_left hWe hCk
    nlinarith
  have h3 : 0 ≤ (Cj + Cx * (1 + K ^ 2 / 2) ^ 2) * e * S := by positivity
  have h4 : 0 ≤ 2 * Ck * R := by positivity
  nlinarith

/-- **`LayerCov`** from the input hypotheses and `ProjGammaFluct`. -/
theorem layerCov_of_pins (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hΓf : ProjGammaFluct) : LayerCov := by
  intro b hb0 hb κ hκ d K c₀ hK hc₀
  obtain ⟨C1, W1, hC1, hexp⟩ := word_cov_expand hGA hLp hP hΓf hb0 hb hκ d hK
  obtain ⟨C2, W2, hC2, hinj⟩ := cov_inj hGA hLp hb0 hb hκ d hK hc₀
  obtain ⟨Ck, hCk, hκb⟩ := fscK_same_le hb0 hb hκ
  refine ⟨2 * Ck + C2 + C1 * (1 + K ^ 2 / 2) ^ 2, max W1 W2, by positivity, ?_⟩
  intro W hW E hE s hs XX hXX nT nI A q j hA hAK hJ hq w v hw hv hwd hvd
  simp only [max_le_iff] at hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  obtain ⟨-, -, -, hWe, he0, -⟩ := layerErr_parts b E s XX hg (W := W)
  have hgK := cond_le_K hXX hη hJ (hA _) (hAK _)
  have hX := hexp W hW.1 E hE s hs XX hXX nT nI A hA hAK w v hw hv hwd hvd
  simp only [posTr_new0, posTr_old] at hX
  have hI := hinj W hW.2 E hE s hs XX hXX nT nI A q j hA hAK hq w v hw hv hwd hvd
  have hS := cov_second b E s XX A hJ hw hv (hκb W E hE s hs)
  rw [show (fun u => coreProd A (sepOf b E XX) [u]) = wval A (sepOf b E XX) from
    funext (coreProd_one A (sepOf b E XX)), wordCov_eval A (ordTable_sepOf b E XX) _ hw hv]
  set I := ∫ y, (layerNew b E A (injCoef q W j) XX w y - coreProd A (sepOf b E XX) [w]) *
    (layerNew b E A (injCoef q W j) XX v y - coreProd A (sepOf b E XX) [v]) ∂freshLaw W b
  set I0 := ∫ y, (layerNew b E A (fun _ => 0) XX w y - coreProd A (sepOf b E XX) [w]) *
    (layerNew b E A (fun _ => 0) XX v y - coreProd A (sepOf b E XX) [v]) ∂freshLaw W b
  set T3 := ∑ p, ∑ q, ∑ k, fscK b E s W k * crossF (wl A w) (slotSep b E XX w) (wl A v)
    (slotSep b E XX v) p q (slotSep b E XX w p * fscG b E XX k * slotSep b E XX v q)
    (slotSep b E XX v q * fscH b E XX k * slotSep b E XX w p)
  have e : I - (W : ℂ)⁻¹ * ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range v.length,
      crossContraction ((transportD0 b E / 2 : ℝ) : ℂ) (sepOf b E XX .proj)
        (sepOf b E XX .proj + A .current) (singleM A (sepOf b E XX) w i)
        (singleM A (sepOf b E XX) v j) = (I - I0) + (I0 - T3) + (T3 - (W : ℂ)⁻¹ *
          ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range v.length,
            crossContraction ((transportD0 b E / 2 : ℝ) : ℂ) (sepOf b E XX .proj)
              (sepOf b E XX .proj + A .current) (singleM A (sepOf b E XX) w i)
              (singleM A (sepOf b E XX) v j)) := by ring
  rw [e]
  have h3 := norm_add_le (I - I0 + (I0 - T3)) (T3 - (W : ℂ)⁻¹ *
    ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range v.length,
      crossContraction ((transportD0 b E / 2 : ℝ) : ℂ) (sepOf b E XX .proj)
        (sepOf b E XX .proj + A .current) (singleM A (sepOf b E XX) w i)
        (singleM A (sepOf b E XX) v j))
  have h4 := norm_add_le (I - I0) (I0 - T3)
  have hR := (sq_nonneg _).trans (sq_le_layerRem W d he0)
  have hfin := cov_final hI hX hS hWe hR (sum_norm_nonneg A (sepOf b E XX) (contrCov w v)) hg hgK
    hC1 hC2 hCk he0
  linarith

end BlockBand.SourceProcess.ContractingWords
