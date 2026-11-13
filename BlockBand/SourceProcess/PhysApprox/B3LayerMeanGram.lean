module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanChain
public import BlockBand.SourceProcess.PhysApprox.B3DecayDrift
public import BlockBand.SourceProcess.PhysApprox.B3CovRepErr
public import BlockBand.SourceProcess.PhysApprox.B3MeanFresh
public import BlockBand.SourceProcess.ClosedSummedProof.DriftStep
public import BlockBand.SourceProcess.ClosedSummedProof.LayerDriftG

/-!
# `B3ClosedGramLayerMean` from the closed chain

The argument (the closed-process version of `condExp_step`/`drift_step`):
* the closed frame at `j` is a function of the past (`b3ClosedFrameAt_b3Ext`);
* on the alive set, the increment is `incr(XX, V_j, e, F_j)` (chain transport), so the conditional
  mean is the fresh integral at the chain state (`condExp_b3_chain`, via
  `condExp_closed_fresh`; integrability from fresh fourth moments and Tonelli,
  `integrable_b3_of_fresh`);
* the cited one-layer bound `gram_layer_drift` at the chain state, with `layerErr = b3CovErr` (`nearSchur XX = b3ClosedX`,
  `layerErr_eq_b3LayerErrX`), `contrGram ≤ C·b3CovZ` and `b3CovZ = b3ContrSum` on `A_j`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ContractingWords (currentOf layerErr layerRem)
open BlockBand.SourceProcess.ClosedSummedProof (contrGram incr layerGram sigD sigVals
  FreshFour integrable_layerGramEntry)
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {W np K : ℕ}

/-!
## The closed frame is a function of the past
-/

/-- **The closed frame at length `n_s ≤ k ≤ j` is a function of the past at `j`.** -/
theorem b3ClosedFrameAt_b3Ext (b E s h : ℝ) (τ m : Fin np → ℝ) {k j : ℕ}
    (hck : closeLen s W ≤ k) (hkj : k ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : ∀ ω, Vs (extPast W j (pastCoords W j ω)) = Vs ω) (y : ProbedPath W np × ℝ) :
    b3ClosedFrameAt b E s h τ m W k Vs (b3Ext W j y) = b3ClosedFrameAt b E s h τ m W k Vs y := by
  have hS := ClosedSumProof.scatteringMatrix_extPast hkj b E y.1.1
  have hS' := ClosedSumProof.scatteringMatrix_extPast (hck.trans hkj) b E y.1.1
  have hR : farReflection b E W (closeLen s W) (extPast W j (pastCoords W j y.1.1)) =
      farReflection b E W (closeLen s W) y.1.1 := by simp only [farReflection, hS']
  have hF := fullInverse_b3Ext hkj b E y.1.1
  have hP := ClosedSumProof.stepProd_extPast (j := j) b E (closeLen s W) y.1.1
    (k - closeLen s W) (by omega)
  simp only [b3Ext, b3ClosedFrameAt, b3OpenFrameAt, physClosingMapAt, probeFrame,
    boundaryToInterior, omittedProj, closingPairing, farTransmission, hR, hS, hF, hP, hV]

/-!
## Tonelli and the conditional step
-/

/-- **Tonelli on the closed past × fresh layer** (closed law). -/
theorem integrable_b3_of_fresh (b : ℝ) (j : ℕ)
    {Φ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ}
    (hΦ : Measurable Φ) (B : ℝ)
    (hB : ∀ x, ∫⁻ f, ‖Φ (x, f)‖ₑ ∂freshLaw W b ≤ ENNReal.ofReal B) :
    Integrable (fun y => Φ (b3Past W j y, freshSample W j y.1.1)) (closedLaw b W np) := by
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    (measurable_b3Past W j).prodMk
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  refine ⟨(hΦ.comp hT).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have e : ∫⁻ y, ‖Φ (b3Past W j y, freshSample W j y.1.1)‖ₑ ∂closedLaw b W np =
      ∫⁻ z, ‖Φ z‖ₑ ∂(((pastLaw W j b).prod (probePhaseLaw W np)).prod (freshLaw W b)) := by
    rw [← closedLaw_map_past_fresh b W np j, lintegral_map hΦ.enorm hT]
  have : IsProbabilityMeasure (pastLaw W j b) := by unfold pastLaw; infer_instance
  rw [e, lintegral_prod _ hΦ.enorm.aemeasurable]
  refine lt_of_le_of_lt ((lintegral_mono fun x => hB x).trans (le_of_eq (b := ENNReal.ofReal B)
    (by simp))) ENNReal.ofReal_lt_top

/-- The Hermitian part `(M + Mᴴ)/2`. -/
def hermPart {ι : Type*} (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1 / 2 : ℂ) • (M + Mᴴ)

theorem hermPart_isHermitian {ι : Type*} (M : Matrix ι ι ℂ) : (hermPart M).IsHermitian := by
  rw [IsHermitian, hermPart, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
  simp [add_comm]

theorem hermPart_of_isHermitian {ι : Type*} {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    hermPart M = M := by
  rw [hermPart, hM.eq, ← two_smul ℂ M, smul_smul]; norm_num

/-- **The conditional mean of a chain step**: a.e. on the alive set, the conditional mean of the
alive Gram increment is the fresh integral of `incr` at the chain state and the closed frame. -/
theorem condExp_b3_chain {b E s h : ℝ} {τ m : Fin np → ℝ} {R R' : ℝ} {j : ℕ}
    (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hj : closeLen s W ≤ j) (hRR : R ≤ R')
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hVm : Measurable Vs)
    (hV : ∀ ω, Vs (extPast W j (pastCoords W j ω)) = Vs ω)
    {XX : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXm : Measurable XX)
    (hXinv : ∀ y, XX (b3Ext W j y) = XX y)
    (hT : ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
      (XX y).IsHermitian ∧ b3ClosedFrameAt b E s h τ m W (j + 1) Vs y =
        (freshTransport b E (XX y) (freshSample W j y.1.1))ᴴ *
          b3ClosedFrameAt b E s h τ m W j Vs y)
    (B : ℝ) (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np))
    (hB : ∀ X' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X'.IsHermitian →
      ∀ V' : Matrix (Fin 2 × Fin W) (SrcCol K (Fin np)) ℂ, (V'ᴴ * V').trace.re ≤ R' →
        ∫⁻ f, ‖incr b E X' V' e f‖ₑ ∂freshLaw W b ≤ ENNReal.ofReal B) :
    ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
      (closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator
          (b3dX b E s h τ m W j Vs (Sum.inl e)) | b3Sigma W j np] y =
        ∫ f, incr b E (XX y) (b3ClosedFrameAt b E s h τ m W j Vs y) e f ∂freshLaw W b := by
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j Vs
  set AM := b3AliveM b E s h τ m R W j Vs
  set V := fun y => b3ClosedFrameAt b E s h τ m W j Vs y
  set XH := fun y => hermPart (XX y)
  have hAeq : A =ᵐ[μ] AM := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs
  have hAMm : MeasurableSet AM := measurableSet_b3AliveM b E s h τ m R W j hVm
  have hVmeas : Measurable V := measurable_b3ClosedFrameAt b E s h τ m W j hVm
  have hXHm : Measurable XH := by
    have : Measurable fun y => XX y + (XX y)ᴴ :=
      measurable_matrix_add hXm (measurable_matrix_conjTranspose' hXm)
    exact measurable_matrix_cmul measurable_const this
  have hQm : Measurable fun z : (ProbedPath W np × ℝ) × LayerSample W .oneBlockOnePort =>
      incr b E (XH z.1) (V z.1) e z.2 :=
    (ClosedSummedProof.measurable_layerGramEntry b E (hXHm.comp measurable_fst)
      (hVmeas.comp measurable_fst) measurable_snd e).sub
      (ClosedSummedProof.measurable_gramEntry_gramPair (hVmeas.comp measurable_fst) e)
  set Ψ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => AM.indicator (fun y => incr b E (XH y) (V y) e z.2) (b3Rebuild W j z.1)
  have hΨm : Measurable Ψ := by
    have hr : Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
        LayerSample W .oneBlockOnePort => (b3Rebuild W j z.1, z.2) :=
      ((measurable_b3Rebuild W j).comp measurable_fst).prodMk measurable_snd
    have hI : Measurable fun z : (ProbedPath W np × ℝ) × LayerSample W .oneBlockOnePort =>
        (AM ×ˢ Set.univ).indicator (fun z => incr b E (XH z.1) (V z.1) e z.2) z :=
      hQm.indicator (hAMm.prod MeasurableSet.univ)
    have e : Ψ = (fun z : (ProbedPath W np × ℝ) × LayerSample W .oneBlockOnePort =>
        (AM ×ˢ Set.univ).indicator (fun z => incr b E (XH z.1) (V z.1) e z.2) z) ∘
          fun z => (b3Rebuild W j z.1, z.2) := by
      funext z
      by_cases hz : b3Rebuild W j z.1 ∈ AM
      · simp [Ψ, hz]
      · simp [Ψ, hz]
    rw [e]
    exact hI.comp hr
  have hinvAM : ∀ y, b3Ext W j y ∈ AM ↔ y ∈ AM := fun y =>
    mem_b3AliveM_b3Ext b E s h τ m R hj le_rfl hV y
  have hinvV : ∀ y, V (b3Ext W j y) = V y := fun y =>
    b3ClosedFrameAt_b3Ext b E s h τ m hj le_rfl hV y
  have hinvX : ∀ y, XH (b3Ext W j y) = XH y := fun y => by simp only [XH, hXinv]
  have hΨy : ∀ y f, Ψ (b3Past W j y, f) = AM.indicator (fun y => incr b E (XH y) (V y) e f) y :=
    fun y f => by
      simp only [Ψ, b3Rebuild_b3Past]
      by_cases hy : y ∈ AM
      · rw [Set.indicator_of_mem ((hinvAM y).2 hy), Set.indicator_of_mem hy, hinvX, hinvV]
      · rw [Set.indicator_of_notMem (fun h' => hy ((hinvAM y).1 h')),
          Set.indicator_of_notMem hy]
  have heq : A.indicator (b3dX b E s h τ m W j Vs (Sum.inl e)) =ᵐ[μ]
      fun y => Ψ (b3Past W j y, freshSample W j y.1.1) := by
    filter_upwards [hT, hAeq] with y hy hyA
    rw [hΨy]
    by_cases hA : y ∈ A
    · have hAM : y ∈ AM := (Iff.of_eq hyA).mp hA
      obtain ⟨hH, hTr⟩ := hy hA
      rw [Set.indicator_of_mem hA, Set.indicator_of_mem hAM]
      simp only [XH, hermPart_of_isHermitian hH, V, incr, layerGram, ← hTr]
      rfl
    · have hAM : y ∉ AM := fun h' => hA ((Iff.of_eq hyA).mpr h')
      rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hAM]
  have hint : Integrable (fun y => Ψ (b3Past W j y, freshSample W j y.1.1)) μ := by
    refine integrable_b3_of_fresh b j hΨm B fun x => ?_
    by_cases hx : b3Rebuild W j x ∈ AM
    · simp only [Ψ, Set.indicator_of_mem hx]
      refine hB _ (hermPart_isHermitian _) _ ?_
      have h1 := hx.2 j hj le_rfl
      exact h1.le.trans hRR
    · simp [Ψ, Set.indicator_of_notMem hx]
  have h1 := condExp_congr_ae (m := b3Sigma W j np) heq
  have h2 := condExp_closed_fresh b j hΨm hint
  filter_upwards [h1, h2, hT, hAeq] with y hy1 hy2 hy hyA hA
  have hAM : y ∈ AM := (Iff.of_eq hyA).mp hA
  rw [hy1, hy2]
  refine integral_congr_ae (Eventually.of_forall fun f => ?_)
  simp only [hΨy, Set.indicator_of_mem hAM, XH, hermPart_of_isHermitian (hy hA).1, V]

/-!
## The Gram layer mean
-/

/-- **`B3ClosedGramLayerMean` from the closed chain and the closed jets.** -/
theorem b3ClosedGramLayerMean_of_chain (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hC : B3ClosedChainPin)
    (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp) (hg : ClosedCondLp) : B3ClosedGramLayerMean := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hF.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  set R' := max R 0 with hR'
  obtain ⟨C₁, W₁, hC₁, hLD⟩ :=
    ClosedSummedProof.gram_layer_drift hGA hLp hP hb0 hb hκ R'
  obtain ⟨C₄, W₂, hC₄, hfp⟩ := ClosedSummedProof.fresh_pow_bound hGA hb0 hb hκ
  obtain ⟨C₂, hC₂, hch⟩ := hC b E np τ m T s h K Vs hF R
  obtain ⟨C₃, hC₃, herr⟩ := closedErrLp_of_jets h0 h1 hg b E np τ m T s h K Vs hF R 6
    (by norm_num)
  set C := max (max (C₁ * C₂) C₁) C₃ with hCdef
  have hC0 : 0 ≤ C := le_max_of_le_right hC₃
  have hCa : C₁ * C₂ ≤ C := le_max_of_le_left (le_max_left _ _)
  have hCb : C₁ ≤ C := le_max_of_le_left (le_max_right _ _)
  have hCc : C₃ ≤ C := le_max_right _ _
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hch, herr, eventually_ge_atTop (max W₁ (max W₂ 1)), hF.2.2.2.2.2] with
    W hchW herrW hW hVs j hj e
  simp only [max_le_iff] at hW
  obtain ⟨hW1, hW2, hW0⟩ := hW
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
  have hVm : Measurable (Vs W) :=
    hVs.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ ω, Vs W (extPast W j (pastCoords W j ω)) = Vs W ω :=
    fun ω => growth_fun_extPast hjc hVs.1 ω
  obtain ⟨XX, hXm, hXinv, hXae⟩ := hchW j hj
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j (Vs W)
  have h4 : FreshFour b W E C₄ := fun X' hX' => hfp W hW2 E hE X' hX'
  have hce := condExp_b3_chain (τ := τ) (m := m) (h := h) (R := R) (R' := R')
    (by linarith : b < 1) hE1 hE2 hjc (le_max_left R 0) hVm hVinv hXm hXinv
    (by filter_upwards [hXae] with y hy hyA
        exact ⟨(hy hyA).1, (hy hyA).2.2.1⟩)
    (R' * (C₄ + 2)) e
    (fun X' hX' V' hV' => ClosedSummedProof.lintegral_incr_le (h4 X' hX').1 (h4 X' hX').2 V'
      (le_max_right R 0) hV' e)
  refine ⟨A.indicator (b3CovErr b E np τ m s h K W (Vs W) j), ?_, ?_⟩
  · have := herrW j hj
    rw [show (ENNReal.ofReal 6) = (6 : ℝ≥0∞) by norm_num] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCc (by positivity)))
  filter_upwards [hce, hXae] with y hy hX
  by_cases hyA : y ∈ A
  · rw [Set.indicator_of_mem hyA, hy hyA, Set.indicator_of_mem hyA]
    obtain ⟨hH, hNS, -, hCur, hCG⟩ := hX hyA
    set XY := XX y
    set V := b3ClosedFrameAt b E s h τ m W j (Vs W) y
    have hTr : (Vᴴ * V).trace.re ≤ R' := (hyA.2 j hjc le_rfl).le.trans (le_max_left R 0)
    have hJ : currentOf b E XY = V * sigD (sigVals K (Fin np)) * Vᴴ := by
      rw [hCur, ClosedSummedProof.srcSignature_eq]
    have hbd := hLD W hW1 E hE (b3Jet b E) (b3Jet_spec hb0 hb hE1 hE2) XY hH V
      (sigVals K (Fin np)) (ClosedSummedProof.abs_sigVals_le K (Fin np)) hJ hTr e
    have hi : ∫ f, incr b E XY V e f ∂freshLaw W b =
        (∫ f, gramEntry e (layerGram b E XY V f) ∂freshLaw W b) -
          gramEntry e (gramPair (nearProjection W) V) := by
      rw [show (fun f => incr b E XY V e f) = fun f => gramEntry e (layerGram b E XY V f) -
        gramEntry e (gramPair (nearProjection W) V) from rfl,
        integral_sub (integrable_layerGramEntry h4 hH V e) (integrable_const _),
        integral_const, probReal_univ, one_smul]
    have hLE : layerErr b E (b3Jet b E) XY = b3CovErr b E np τ m s h K W (Vs W) j y :=
      layerErr_eq_b3LayerErrX hb0 hb hE1 hE2 (b3Jet_spec hb0 hb hE1 hE2) hNS
    have hZ : b3CovZ b E np τ m s h K W (Vs W) j y =
        b3ContrSum b E s h τ m R W j (Vs W) y := by
      simp only [b3CovZ, b3ContrSum, b3ContrAlive]
      exact Finset.sum_congr rfl fun x _ => by rw [Set.indicator_of_mem hyA]
    have hdrift : cDrift b E (Sum.inl e : CIdx K np) (b3ClosedGramAt b E s h τ m W j (Vs W) y) =
        gramDriftEntry (transportD0 b E) (sigD (sigVals K (Fin np))) e
          (gramPair (nearProjection W) V) := by
      simp only [cDrift, ClosedSummedProof.srcSignature_eq]
      rfl
    rw [hi, hdrift]
    rw [hLE] at hbd
    set ev := b3CovErr b E np τ m s h K W (Vs W) j y
    set S := b3ContrSum b E s h τ m R W j (Vs W) y
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hG0 : 0 ≤ contrGram b E XY V := ClosedSummedProof.contrGram_nonneg b E XY V
    have hev : ev ≤ ‖ev‖ := Real.le_norm_self ev
    have hGZ : contrGram b E XY V ≤ C₂ * S := by rw [← hZ]; exact hCG
    have h6 : |ev| ^ 6 = ev ^ 6 := by
      rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    have hrem : layerRem W 1 ev = 1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + ‖ev‖ ^ 6 := by
      rw [layerRem, Real.norm_eq_abs, sq_abs, h6, one_div, mul_inv, div_eq_mul_inv]
    refine hbd.trans ?_
    rw [hrem]
    have hW0' : (0 : ℝ) ≤ 1 / ((W : ℝ) * Real.sqrt W) := by positivity
    have hA1 : C₁ * ev * contrGram b E XY V ≤ C * (‖ev‖ * S) :=
      calc C₁ * ev * contrGram b E XY V ≤ C₁ * ‖ev‖ * (C₂ * S) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hev hC₁) hGZ hG0 ?_
            exact mul_nonneg hC₁ (norm_nonneg _)
        _ = (C₁ * C₂) * (‖ev‖ * S) := by ring
        _ ≤ C * (‖ev‖ * S) := mul_le_mul_of_nonneg_right hCa
            (mul_nonneg (norm_nonneg _) hS0)
    have hA2 : C₁ * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + ‖ev‖ ^ 6) ≤
        C * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + ‖ev‖ ^ 6) :=
      mul_le_mul_of_nonneg_right hCb (by positivity)
    calc C₁ * ev * contrGram b E XY V + C₁ * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + ‖ev‖ ^ 6)
        ≤ C * (‖ev‖ * S) + C * (1 / ((W : ℝ) * Real.sqrt W) + ‖ev‖ ^ 2 + ‖ev‖ ^ 6) :=
          add_le_add hA1 hA2
      _ = C * (‖ev‖ * S + ‖ev‖ ^ 2 + ‖ev‖ ^ 6 + 1 / ((W : ℝ) * Real.sqrt W)) := by ring
  · rw [Set.indicator_of_notMem hyA, norm_zero]
    have : 0 ≤ b3ContrSum b E s h τ m R W j (Vs W) y :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    positivity

end BlockBand.SourceProcess.PhysApprox.B3
