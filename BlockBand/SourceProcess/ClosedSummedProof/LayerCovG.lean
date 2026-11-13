module

public import BlockBand.SourceProcess.ClosedSummedProof.CovBound

/-!
# The one-layer bracket of the Gram coordinates

`gram_layer_cov`: under the Gaussian inputs, for a stationary jet in the bulk, a Hermitian state
`XX` whose current is `V diag(d) Vᴴ` (`|d| ≤ 1`, `Re Tr VᴴV ≤ R`), the mean product of the
one-layer increments of two Gram coordinates under the fresh layer law differs from
`W⁻¹ gramCovEntry` by at most `C (layerErr · contrGram + layerRem)`.
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

/-- The old value of a right polarized word. -/
theorem sum_old_right {W : ℕ} {c : Type} [Fintype c] [DecidableEq c]
    (V : Matrix (Fin 2 × Fin W) c ℂ) (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (e e' : Fin 2 × c × c) :
    ∑ k, polCoef k * coreProd (gramLetters J V e e') (sepOf b E XX) [[(tagR k, gramSep e'.1)]] =
      gramEntry e' (gramPair (nearProjection W) V) := by
  simp only [coreProd_one, gramLetters_tagR, sum_entry]
  rw [gramEntry_sep _ (sepOf b E XX) rfl rfl e']

theorem norm_pol_sum2_le (F : Fin 4 → Fin 4 → ℂ) (B : ℝ) (hF : ∀ k l, ‖F k l‖ ≤ B) :
    ‖∑ k, ∑ l, polCoef k * polCoef l * F k l‖ ≤ B := by
  have h : ∀ k, ‖∑ l, polCoef k * polCoef l * F k l‖ ≤ B / 4 := fun k => by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul, norm_polCoef, Fin.sum_univ_four]
    linarith [hF k 0, hF k 1, hF k 2, hF k 3]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => h k).trans (le_of_eq ?_))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- **The one-layer Gram bracket**, from `GaussianAbsorptionContract`, `GaussianLpGradient` and
`GaussianPoincare`. -/
theorem gram_layer_cov (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (R : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ {c : Type} [Fintype c] [DecidableEq c] (V : Matrix (Fin 2 × Fin W) c ℂ) (d : c → ℝ),
        (∀ x, |d x| ≤ 1) → currentOf b E XX = V * sigD d * Vᴴ → (Vᴴ * V).trace.re ≤ R →
      ∀ e e' : Fin 2 × c × c,
        ‖(∫ y, (gramEntry e (layerGram b E XX V y) - gramEntry e (gramPair (nearProjection W) V)) *
              (gramEntry e' (layerGram b E XX V y) - gramEntry e' (gramPair (nearProjection W) V))
              ∂freshLaw W b) -
            (W : ℂ)⁻¹ * gramCovEntry (transportD0 b E) (sigD d) e e'
              (gramPair (nearProjection W) V)‖ ≤
          C * layerErr b E s XX * contrGram b E XX V + C * layerRem W 1 (layerErr b E s XX) := by
  obtain ⟨C, W₁, hC0, hLC⟩ := layerCov_holds hGA hLp hP b hb0 hb κ hκ 1 (2 * (2 * max R 0)) 0
    (by have := le_max_right R 0; positivity) le_rfl
  obtain ⟨W₂, hmom⟩ := fresh_moments hGA hb0 hb hκ
  refine ⟨C * (64 * max R 0 + 1), max W₁ (max W₂ 1), by positivity, ?_⟩
  intro W hW E hE s hs XX hXX c _ _ V d hd hJ hR e e'
  simp only [max_le_iff] at hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have he0 := layerErr_nonneg' hb hκ hE s hXX
  have hr0 := layerRem_nonneg W (layerErr b E s XX)
  have hM := le_max_right R 0
  set A := gramLetters (V * sigD d * Vᴴ) V e e'
  set N := fun y => freshTransport b E XX y
  set T := sepOf b E XX (gramSep e.1)
  set T' := sepOf b E XX (gramSep e'.1)
  set o := fun k : Fin 4 => coreProd A (sepOf b E XX) [[(tagL k, gramSep e.1)]]
  set o' := fun l : Fin 4 => coreProd A (sepOf b E XX) [[(tagR l, gramSep e'.1)]]
  set f := fun (k : Fin 4) y => ((N y)ᴴ * entryLetter V e k * N y * T).trace
  set f' := fun (l : Fin 4) y => ((N y)ᴴ * entryLetter V e' l * N y * T').trace
  have hN : Measurable N := FullSource.measurable_freshTransport_comp b E measurable_const
    measurable_id
  have hint : ∀ k l, Integrable (fun y => (f k y - o k) * (f' l y - o' l)) (freshLaw W b) :=
    fun k l => integrable_trace_conj_mul hN (hmom W hW.2.1 E hE XX hXX).1
      (hmom W hW.2.1 E hE XX hXX).2 _ _ _ _ (norm_sepOf_le b E hXX hη _)
      (norm_sepOf_le b E hXX hη _) _ _
  set q : Fin 0 → ℝ → ℝ := fun a => a.elim0
  have key : ∀ k l : Fin 4, ‖(∫ y, (f k y - o k) * (f' l y - o' l) ∂freshLaw W b) - (W : ℂ)⁻¹ *
      MvPolynomial.eval (fun v => coreProd A (sepOf b E XX) [v])
        (wordCov (transportD0 b E) [(tagL k, gramSep e.1)] [(tagR l, gramSep e'.1)])‖ ≤
      C * (64 * max R 0 + 1) * layerErr b E s XX * contrGram b E XX V +
        C * (64 * max R 0 + 1) * layerRem W 1 (layerErr b E s XX) := by
    intro k l
    have h := hLC W hW.1 E hE s hs XX hXX 8 0 A q 0 (gramLetters_herm V d e e')
      (gramLetters_nuc V d hd R hR e e') hJ.symm (fun a => a.elim0) [(tagL k, gramSep e.1)]
      [(tagR l, gramSep e'.1)] (ordinary_tag _ _) (ordinary_tag _ _) le_rfl le_rfl
    have hA : A (tagL k) = entryLetter V e k := gramLetters_tagL _ V e e' k
    have hA' : A (tagR l) = entryLetter V e' l := gramLetters_tagR _ V e e' l
    have hn : ∀ y, layerNew b E A (injCoef q W 0) XX [(tagL k, gramSep e.1)] y = f k y := fun y => by
      rw [show tagL k = TraceLetter.tag (Fin.castAdd 4 k) from rfl, layerNew_tag]
      rw [show TraceLetter.tag (Fin.castAdd 4 k) = tagL k from rfl, hA]
    have hn' : ∀ y, layerNew b E A (injCoef q W 0) XX [(tagR l, gramSep e'.1)] y = f' l y :=
      fun y => by
      rw [show tagR l = TraceLetter.tag (Fin.natAdd 4 l) from rfl, layerNew_tag]
      rw [show TraceLetter.tag (Fin.natAdd 4 l) = tagR l from rfl, hA']
    simp only [hn, hn'] at h
    have hc := contrCov_gram_le b E hXX hη V (V * sigD d * Vᴴ) e e' k l (gramSep e.1)
      (gramSep e'.1) hR
    have hcg := contrGram_nonneg b E XX V
    refine h.trans ((add_le_add_left (mul_le_mul_of_nonneg_left hc (mul_nonneg hC0 he0)) _).trans ?_)
    have p1 := mul_nonneg (mul_nonneg hC0 he0) hcg
    have p2 := mul_nonneg (mul_nonneg hC0 hM) hr0
    have e1 : C * (64 * max R 0 + 1) * layerErr b E s XX * contrGram b E XX V +
        C * (64 * max R 0 + 1) * layerRem W 1 (layerErr b E s XX) =
        (C * layerErr b E s XX * (64 * max R 0 * contrGram b E XX V) +
          C * layerRem W 1 (layerErr b E s XX)) +
        (C * layerErr b E s XX * contrGram b E XX V +
          64 * (C * max R 0 * layerRem W 1 (layerErr b E s XX))) := by ring
    rw [e1]; linarith
  have hsum : (∫ y, (gramEntry e (layerGram b E XX V y) - gramEntry e (gramPair (nearProjection W) V)) *
        (gramEntry e' (layerGram b E XX V y) - gramEntry e' (gramPair (nearProjection W) V))
        ∂freshLaw W b) -
      (W : ℂ)⁻¹ * gramCovEntry (transportD0 b E) (sigD d) e e' (gramPair (nearProjection W) V) =
      ∑ k, ∑ l, polCoef k * polCoef l * ((∫ y, (f k y - o k) * (f' l y - o' l) ∂freshLaw W b) -
        (W : ℂ)⁻¹ * MvPolynomial.eval (fun v => coreProd A (sepOf b E XX) [v])
          (wordCov (transportD0 b E) [(tagL k, gramSep e.1)] [(tagR l, gramSep e'.1)])) := by
    have hpt : ∀ y, (gramEntry e (layerGram b E XX V y) -
        gramEntry e (gramPair (nearProjection W) V)) * (gramEntry e' (layerGram b E XX V y) -
          gramEntry e' (gramPair (nearProjection W) V)) =
        ∑ k, ∑ l, polCoef k * polCoef l * ((f k y - o k) * (f' l y - o' l)) := fun y => by
      rw [← sum_new V b E XX y e, ← sum_new V b E XX y e', ← sum_old V b E XX (V * sigD d * Vᴴ) e e',
        ← sum_old_right V b E XX (V * sigD d * Vᴴ) e e', ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [f, f', o, o', N, T, T', A]
      ring
    have hI : ∫ y, (gramEntry e (layerGram b E XX V y) -
        gramEntry e (gramPair (nearProjection W) V)) * (gramEntry e' (layerGram b E XX V y) -
          gramEntry e' (gramPair (nearProjection W) V)) ∂freshLaw W b =
        ∑ k, ∑ l, polCoef k * polCoef l * ∫ y, (f k y - o k) * (f' l y - o' l) ∂freshLaw W b := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hint k l).const_mul _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ fun l _ => (hint k l).const_mul _]
      simp only [integral_const_mul]
    rw [hI, ← cov_match (transportD0 b E) V (sigD d) (by simp) (sepOf b E XX) rfl rfl e e',
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hsum]
  exact norm_pol_sum2_le _ _ key

end BlockBand.SourceProcess.ClosedSummedProof
