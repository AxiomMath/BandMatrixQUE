module

public import BlockBand.SourceProcess.ClosedSummedProof.LayerLetters

/-!
# The one-layer drift of the Gram coordinates

The one-layer core of `ClosedDriftSummed`, for a deterministic old state: the full-source
calculation of the contracting words applies with finitely many far open channels.

**`gram_layer_drift`**: for a deterministic Hermitian old two-port `𝕏`, any frame `V`
(`Re Tr VᴴV ≤ R`) whose columns carry the whole current, `currentOf 𝕏 = V diag(d) Vᴴ` with
`|d| ≤ 1`, and every Gram coordinate `e`,
`‖E G_e(NᴴV) - G_e(V) - W⁻¹ b_e(G(V))‖ ≤ C·e(𝕏)·contrGram(𝕏,V) + C·layerRem W 1 e(𝕏)`,
where `b_e = gramDriftEntry D₀ diag(d)`, `e(𝕏) = layerErr` (`δ₀ + δ₁ + g/W + W⁻¹`
at the near Schur complement) and `contrGram` sums the contracting Gram coordinates `VᴴσV`,
`σ ∈ {P𝕊, 𝕊*P, P𝕊P, P𝕊*P}`. Uniform in `W ≥ W₀`, `E ∈ bulkInterval κ`, `𝕏`, the stationary jet,
the column type and `V`. Hypotheses: only the Gaussian inputs `GaussianAbsorptionContract`,
`GaussianLpGradient`, `GaussianPoincare` (through `layerDrift_holds`).

Proof: polarize `G_e = Σ_k (iᵏ/4) Tr(u_ku_k*T_σ)` (`Polar`), apply `LayerDrift` to each one-letter
word, and match the word drift with `gramDriftEntry` (`drift_match`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.ContractingWords
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Stochastic BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

theorem layerRem_nonneg (W : ℕ) (e : ℝ) : 0 ≤ layerRem W 1 e := by
  unfold layerRem
  have h : e ^ (2 * 1 + 4) = (e ^ 3) ^ 2 := by ring
  rw [h]; positivity

theorem layerErr_nonneg' {b : ℝ} (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {E : ℝ}
    (hE : E ∈ bulkInterval κ) (s : ℂ) {W : ℕ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) : 0 ≤ layerErr b E s XX := by
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  exact (layerErr_parts b E s XX (FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX))).2.2.2.2.1

/-- The norm of a polarized combination. -/
theorem norm_pol_sum_le (F : Fin 4 → ℂ) (B : ℝ) (hF : ∀ k, ‖F k‖ ≤ B) :
    ‖∑ k, polCoef k * F k‖ ≤ B := by
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul, norm_polCoef, Fin.sum_univ_four]
  linarith [hF 0, hF 1, hF 2, hF 3]

/-- **The one-layer Gram drift** (from the Gaussian inputs). -/
theorem gram_layer_drift (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (R : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ {c : Type} [Fintype c] [DecidableEq c] (V : Matrix (Fin 2 × Fin W) c ℂ) (d : c → ℝ),
        (∀ x, |d x| ≤ 1) → currentOf b E XX = V * sigD d * Vᴴ → (Vᴴ * V).trace.re ≤ R →
      ∀ e : Fin 2 × c × c,
        ‖(∫ y, gramEntry e (layerGram b E XX V y) ∂freshLaw W b) -
            gramEntry e (gramPair (nearProjection W) V) -
            (W : ℂ)⁻¹ * gramDriftEntry (transportD0 b E) (sigD d) e
              (gramPair (nearProjection W) V)‖ ≤
          C * layerErr b E s XX * contrGram b E XX V + C * layerRem W 1 (layerErr b E s XX) := by
  obtain ⟨C, W₁, hC0, hLD⟩ := layerDrift_holds hGA hLp hP b hb0 hb κ hκ 1 (2 * (2 * max R 0)) 0
    (by have := le_max_right R 0; positivity) le_rfl
  obtain ⟨W₂, hmom⟩ := fresh_moments hGA hb0 hb hκ
  refine ⟨4 * C, max W₁ (max W₂ 1), by positivity, ?_⟩
  intro W hW E hE s hs XX hXX c _ _ V d hd hJ hR e
  simp only [max_le_iff] at hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have he0 := layerErr_nonneg' hb hκ hE s hXX
  have hr0 := layerRem_nonneg W (layerErr b E s XX)
  set A := gramLetters (V * sigD d * Vᴴ) V e e
  set N := fun y => freshTransport b E XX y
  set T := sepOf b E XX (gramSep e.1)
  have hN : Measurable N := FullSource.measurable_freshTransport_comp b E measurable_const
    measurable_id
  have hT : ‖T‖ ≤ 1 := norm_sepOf_le b E hXX hη _
  have hint : ∀ k : Fin 4, Integrable (fun y => ((N y)ᴴ * entryLetter V e k * N y * T).trace)
      (freshLaw W b) := fun k =>
    integrable_trace_conj hN (hmom W hW.2.1 E hE XX hXX).1 _ _ hT
  set q : Fin 0 → ℝ → ℝ := fun a => a.elim0
  have key : ∀ k : Fin 4, ‖(∫ y, ((N y)ᴴ * entryLetter V e k * N y * T).trace ∂freshLaw W b) -
      coreProd A (sepOf b E XX) [[(tagL k, gramSep e.1)]] - (W : ℂ)⁻¹ *
        MvPolynomial.eval (fun v => coreProd A (sepOf b E XX) [v])
          (wordDrift (transportD0 b E) [(tagL k, gramSep e.1)])‖ ≤
      C * layerErr b E s XX * (4 * contrGram b E XX V) + C * layerRem W 1 (layerErr b E s XX) := by
    intro k
    have h := hLD W hW.1 E hE s hs XX hXX 8 0 A q 0 (gramLetters_herm V d e e)
      (gramLetters_nuc V d hd R hR e e) hJ.symm (fun a => a.elim0) [(tagL k, gramSep e.1)]
      (ordinary_tag _ _) le_rfl
    have hA : A (tagL k) = entryLetter V e k := gramLetters_tagL _ V e e k
    have hn : ∀ y, layerNew b E A (injCoef q W 0) XX [(tagL k, gramSep e.1)] y =
        ((N y)ᴴ * entryLetter V e k * N y * T).trace := fun y => by
      rw [show tagL k = TraceLetter.tag (Fin.castAdd 4 k) from rfl, layerNew_tag]
      rw [show TraceLetter.tag (Fin.castAdd 4 k) = tagL k from rfl, hA]
    simp only [hn, wordInjection_tag, map_zero, add_zero] at h
    refine h.trans (add_le_add_left (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 he0)) _)
    exact contrDrift_gram_le b E XX V _ e e _ k (gramLetters_tagL _ V e e k) _
  have hsum : (∫ y, gramEntry e (layerGram b E XX V y) ∂freshLaw W b) -
      gramEntry e (gramPair (nearProjection W) V) -
      (W : ℂ)⁻¹ * gramDriftEntry (transportD0 b E) (sigD d) e (gramPair (nearProjection W) V) =
      ∑ k, polCoef k * ((∫ y, ((N y)ᴴ * entryLetter V e k * N y * T).trace ∂freshLaw W b) -
        coreProd A (sepOf b E XX) [[(tagL k, gramSep e.1)]] - (W : ℂ)⁻¹ *
          MvPolynomial.eval (fun v => coreProd A (sepOf b E XX) [v])
            (wordDrift (transportD0 b E) [(tagL k, gramSep e.1)])) := by
    have hI : ∫ y, gramEntry e (layerGram b E XX V y) ∂freshLaw W b =
        ∑ k, polCoef k * ∫ y, ((N y)ᴴ * entryLetter V e k * N y * T).trace ∂freshLaw W b := by
      calc ∫ y, gramEntry e (layerGram b E XX V y) ∂freshLaw W b
          = ∫ y, ∑ k, polCoef k * ((N y)ᴴ * entryLetter V e k * N y * T).trace ∂freshLaw W b :=
            integral_congr_ae (Filter.Eventually.of_forall fun y => (sum_new V b E XX y e).symm)
        _ = ∑ k, ∫ y, polCoef k * ((N y)ᴴ * entryLetter V e k * N y * T).trace ∂freshLaw W b :=
            integral_finsetSum _ fun k _ => (hint k).const_mul _
        _ = _ := by simp only [integral_const_mul]
    rw [hI, ← sum_old V b E XX (V * sigD d * Vᴴ) e e,
      ← drift_match (transportD0 b E) V (sigD d) (sepOf b E XX) rfl rfl e e, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum]
  refine (norm_pol_sum_le _ _ key).trans ?_
  nlinarith [contrGram_nonneg b E XX V]

end BlockBand.SourceProcess.ClosedSummedProof
