module

public import BlockBand.SourceProcess.ClosedSummedProof.StepCondE

/-!
# One closed step: the drift error is bounded by the chain error scale

**`drift_step`**: at a step `n_s ≤ j` where the closed path is a Hermitian chain (`IsClosedChain`
clauses at `j`), with the one-layer bound of `gram_layer_drift` (hypothesis `hD`) and fresh
fourth moments (`h4`), the `j`-th summand of `driftSum` is at most `C · E[1_{alive ∩ no birth}
chainErr_j]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedSumProof
open BlockBand.SourceProcess.ClosedPath BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ContractingWords BlockBand.SourceProcess.ClosedLimit
open scoped ENNReal Matrix.Norms.L2Operator

variable {W p K M : ℕ}

/-- The one-layer drift bound at width `W` for the closed column type (`gram_layer_drift`). -/
abbrev DriftBound (b E : ℝ) (σ : ℂ) (R C : ℝ) (W K : ℕ) (π : Type) [Fintype π] [DecidableEq π] :
    Prop :=
  ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
    ∀ V : Matrix (Fin 2 × Fin W) (SrcCol K π) ℂ,
      currentOf b E XX = V * sigD (sigVals K π) * Vᴴ → (Vᴴ * V).trace.re ≤ R →
    ∀ e : Fin 2 × SrcCol K π × SrcCol K π,
      ‖(∫ y, gramEntry e (layerGram b E XX V y) ∂freshLaw W b) -
          gramEntry e (gramPair (nearProjection W) V) -
          (W : ℂ)⁻¹ * gramDriftEntry (transportD0 b E) (sigD (sigVals K π)) e
            (gramPair (nearProjection W) V)‖ ≤
        C * layerErr b E σ XX * contrGram b E XX V + C * layerRem W 1 (layerErr b E σ XX)

/-- Fresh fourth moments at width `W`. -/
abbrev FreshFour (b : ℝ) (W : ℕ) (E C₄ : ℝ) : Prop :=
  ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
    ∫ y, ‖freshTransport b E XX y‖ ^ 4 ∂freshLaw W b ≤ C₄ ∧
      Integrable (fun y => ‖freshTransport b E XX y‖ ^ 4) (freshLaw W b)

theorem integrable_layerGramEntry {b E : ℝ} {C₄ : ℝ} (h4 : FreshFour b W E C₄)
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : XX.IsHermitian) {c : Type} [Fintype c]
    [DecidableEq c] (V : Matrix (Fin 2 × Fin W) c ℂ) (e : Fin 2 × c × c) :
    Integrable (fun y => gramEntry e (layerGram b E XX V y)) (freshLaw W b) := by
  have h2 : Integrable (fun y => (Vᴴ * V).trace.re * (‖freshTransport b E XX y‖ ^ 4 + 1))
      (freshLaw W b) := ((h4 XX hXX).2.add (integrable_const 1)).const_mul _
  refine h2.mono' (measurable_layerGramEntry b E measurable_const measurable_const measurable_id
    e).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ (Vᴴ * V).trace.re := (norm_nonneg _).trans (norm_gramEntry_old_le V e)
  refine (norm_gramEntry_layerGram_le b E XX V y e).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (sq_le_pow4 _) h0

/-- **The drift error of one closed step.** -/
theorem drift_step (b E s T h : ℝ) {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (hb1 : b < 1)
    (hE1 : -2 < E) (hE2 : E < 2) (R : ℝ) {j : ℕ} (hj : closeLen s W ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {X : ChainState W p M}
    (hXm : Measurable (X j)) (hXh : ∀ x, (X j x).IsHermitian)
    (hrel : ∀ᵐ y ∂lawW b T q M W, y ∈ aliveNB b E s T h q R W j Vs →
      closedFrameAt b E s T h q W (j + 1) Vs y =
          (freshTransport b E (X j (cpast j y)) (freshSample W j y.1.1))ᴴ *
            closedFrameAt b E s T h q W j Vs y ∧
        currentOf b E (X j (cpast j y)) = closedFrameAt b E s T h q W j Vs y *
          srcSignature K (Fin p × Fin M) * (closedFrameAt b E s T h q W j Vs y)ᴴ)
    {σ : ℂ} {C C₄ : ℝ} (hC0 : 0 ≤ C) (hD : DriftBound b E σ R C W K (Fin p × Fin M))
    (h4 : FreshFour b W E C₄) (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) :
    ∫⁻ y, ‖(aliveNB b E s T h q R W j Vs).indicator (fun y =>
      (lawW b T q M W)[(aliveNB b E s T h q R W j Vs).indicator (fun y =>
        zc b E s T h q W Vs e (j + 1) y - zc b E s T h q W Vs e j y) | closedSigma W j p M] y -
          (W : ℂ)⁻¹ * gramDriftEntry (transportD0 b E) (srcSignature K (Fin p × Fin M)) e
            (closedGramAt b E s T h q W j Vs y)) y‖ₑ ∂lawW b T q M W ≤
      ENNReal.ofReal C * ∫⁻ y, (aliveNB b E s T h q R W j Vs).indicator
        (fun y => ENNReal.ofReal (chainErr b E s T h q W Vs X σ j y)) y ∂lawW b T q M W := by
  set μ := lawW b T q M W
  have hA := am_ae_eq (b := b) (E := E) (s := s) (T := T) (h := h) (R := R) (Vs := Vs)
    hb1 hE1 hE2 hq (M := M) j
  rw [lintegral_condErr_congr hA, lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hA)]
  set Am := am b E s T h q R W Vs j
  have hfr : ∀ y : SampledPath W p M × ℝ,
      closedFrameAt b E s T h q W j Vs y = framePast b E s T h q W j Vs (cpast j y) :=
    closedFrameAt_eq_framePast b E s T h q hj hVs
  have hFm := measurable_framePast b E s T h q W j (p := p) (M := M) hVs
  have hrel' : ∀ᵐ y ∂μ, y ∈ Am →
      closedFrameAt b E s T h q W (j + 1) Vs y =
          (freshTransport b E (X j (cpast j y)) (freshSample W j y.1.1))ᴴ *
            closedFrameAt b E s T h q W j Vs y ∧
        currentOf b E (X j (cpast j y)) = closedFrameAt b E s T h q W j Vs y *
          srcSignature K (Fin p × Fin M) * (closedFrameAt b E s T h q W j Vs y)ᴴ := by
    filter_upwards [hrel, hA] with y hy hyA hyAm
    exact hy ((Iff.of_eq hyA).mpr hyAm)
  have hce := condExp_step b E s T h hq R hj hVs (X := X j) hXh (fun XX V f => incr b E XX V e f)
    ((measurable_layerGramEntry b E (hXm.comp measurable_fst) (hFm.comp measurable_fst)
      measurable_snd e).sub (measurable_gramEntry_gramPair (hFm.comp measurable_fst) e))
    (max R 0 * (C₄ + 2))
    (fun XX hXX V hV => lintegral_incr_le (h4 XX hXX).1 (h4 XX hXX).2 V (le_max_right R 0)
      (hV.trans (le_max_left R 0)) e)
    (fun y => zc b E s T h q W Vs e (j + 1) y - zc b E s T h q W Vs e j y)
    (by filter_upwards [hrel'] with y hy hyA
        simp only [ClosedSumProof.zc, closedGramAt, incr, layerGram, (hy hyA).1]
        rfl)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hce, hrel'] with y hy hyr
  by_cases hyA : y ∈ Am
  · rw [Set.indicator_of_mem hyA, Set.indicator_of_mem hyA, hy hyA, ← ofReal_norm,
      ← ENNReal.ofReal_mul hC0]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨-, hJ⟩ := hyr hyA
    set XX := X j (cpast j y)
    set V := closedFrameAt b E s T h q W j Vs y
    have hTr : (Vᴴ * V).trace.re ≤ R := (hyA.1.2 j hj le_rfl).le
    have hb := hD XX (hXh _) V (by rw [hJ, srcSignature_eq]) hTr e
    have hi : ∫ f, incr b E XX V e f ∂freshLaw W b =
        (∫ f, gramEntry e (layerGram b E XX V f) ∂freshLaw W b) -
          gramEntry e (gramPair (nearProjection W) V) := by
      rw [show (fun f => incr b E XX V e f) = fun f => gramEntry e (layerGram b E XX V f) -
        gramEntry e (gramPair (nearProjection W) V) from rfl,
        integral_sub (integrable_layerGramEntry h4 (hXh _) V e) (integrable_const _),
        integral_const, probReal_univ, one_smul]
    rw [hi, srcSignature_eq]
    refine hb.trans (le_of_eq ?_)
    simp only [chainErr, XX, V]
    ring
  · rw [Set.indicator_of_notMem hyA]; simp

end BlockBand.SourceProcess.ClosedSummedProof
