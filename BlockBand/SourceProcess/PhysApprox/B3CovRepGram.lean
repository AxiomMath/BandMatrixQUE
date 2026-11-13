module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepSplit
public import BlockBand.SourceProcess.PhysApprox.B3MeanFresh
public import BlockBand.SourceProcess.PhysApprox.B3ModulAdapt
public import BlockBand.SourceProcess.ClosedSummedProof.BracketReduce
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanChain
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanGram

/-!
# The Gram part of `CovLayerHyp` from the one-layer core

The Gram pairs of `CovLayerHyp` are proved from the closed chain, by the one-layer bracket bound
`bracket_step` applied to the complex closed process with fresh-layer conditioning. Merged with
the `𝒦` pairs this gives `CovLayerHyp`, and from it the targets `KStepCov`, `GramSumStepCov` and
`ComplexClosedSummed`.

Law `closedLaw`, with fresh-layer law `freshLaw W b`; `e = b3CovErr`, `Z = b3CovZ`. The Gram pairs
use the hypotheses `GaussianAbsorptionContract`, `GaussianLpGradient`, `GaussianPoincare` and the closed chain
`B3ClosedChainPin`: eventually, at every no-birth step `j`, a padded Hermitian closed two-port `𝕏_j`,
a function of the past at `j`, with `nearSchur z_b 𝕏_j = X_cl,j` (so `layerErr 𝕏_j = e_j`) and
`contrGram(𝕏_j, V_j) ≤ C·Z_j`, a.e. on the alive set.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ContractingWords (layerErr layerRem currentOf)
open BlockBand.SourceProcess.ClosedSummedProof (layerGram contrGram incr gram_layer_cov
  fresh_pow_bound lintegral_incr_mul_le measurable_layerGramEntry measurable_gramEntry_gramPair
  srcSignature_eq sigVals sigD abs_sigVals_le layerErr_nonneg' CovBound FreshFour)
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexConjugate

/-!
## The Gram pairs and the sign of `e`
-/

/-- The Gram pairs of `CovLayerHyp`. -/
def CovLayerHypGram (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ 2 ≤ N ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ g g' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
        CovLayerAt e Z b E τ m s h R (Vs W) j C N (Sum.inl g) (Sum.inl g')

/-- `e ≥ 0` a.e. on the alive set, eventually, at the no-birth steps. -/
def CovErrNonneg (e : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        0 ≤ e b E np τ m s h K W (Vs W) j y

/-!
## Tonelli under the closed law
-/

theorem integrable_closed_of_fresh_b3 (b : ℝ) {W np : ℕ} (j : ℕ)
    {Φ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ}
    (hΦ : Measurable Φ) (B : ℝ)
    (hB : ∀ x, ∫⁻ f, ‖Φ (x, f)‖ₑ ∂freshLaw W b ≤ ENNReal.ofReal B) :
    Integrable (fun y => Φ (b3Past W j y, freshSample W j y.1.1)) (closedLaw b W np) := by
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    (measurable_b3Past W j).prodMk
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  have hν : IsProbabilityMeasure ((pastLaw W j b).prod (probePhaseLaw W np)) := by
    rw [← closedLaw_map_b3Past b W np j]; infer_instance
  refine ⟨(hΦ.comp hT).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have e : ∫⁻ y, ‖Φ (b3Past W j y, freshSample W j y.1.1)‖ₑ ∂closedLaw b W np =
      ∫⁻ z, ‖Φ z‖ₑ ∂(((pastLaw W j b).prod (probePhaseLaw W np)).prod (freshLaw W b)) := by
    rw [← closedLaw_map_past_fresh b W np j, lintegral_map hΦ.enorm hT]
  rw [e, lintegral_prod _ hΦ.enorm.aemeasurable]
  refine lt_of_le_of_lt ((lintegral_mono fun x => hB x).trans
    (le_of_eq (b := ENNReal.ofReal B) ?_)) ENNReal.ofReal_lt_top
  rw [lintegral_const, measure_univ, mul_one]

/-!
## One step
-/

theorem layerErr_b3Jet_eq {b E : ℝ} {W : ℕ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : nearSchur (boundaryZ b E) XX = X) :
    layerErr b E (b3Jet b E) XX = b3LayerErrX b E X := by
  rw [BlockBand.SourceProcess.ContractingWords.layerErr, b3LayerErrX, hX]

theorem measurable_trace_re_gram {α : Type*} [MeasurableSpace α] {ι c : Type*} [Fintype ι]
    [Fintype c] {U : α → Matrix ι c ℂ} (hU : Measurable U) :
    Measurable fun x => ((U x)ᴴ * U x).trace.re := by
  have hM := measurable_matrix_mul' (measurable_matrix_conjTranspose' hU) hU
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  exact Finset.measurable_sum _ fun i _ => Complex.measurable_re.comp hM.eval_matrix

theorem measurableSet_isHermitian {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]
    {X : α → Matrix ι ι ℂ} (hX : Measurable X) : MeasurableSet {x | (X x).IsHermitian} := by
  have e : {x | (X x).IsHermitian} = ⋂ i, ⋂ k, {x | star (X x k i) = X x i k} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Matrix.IsHermitian, ← Matrix.ext_iff,
      conjTranspose_apply]
  rw [e]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
    measurableSet_eq_fun (continuous_star.measurable.comp hX.eval_matrix) hX.eval_matrix

/-- **The Gram bracket at one step from a closed chain state** (`bracket_step` for the
complex closed process, with fresh-layer conditioning). -/
theorem covLayerAt_gram_step {b E : ℝ} (hb1 : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ)
    {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) {W j : ℕ} (hj : closeLen s W ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs)
    {XX : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {Cch : ℝ}
    (hCch : 0 ≤ Cch) (hch : B3ClosedChainAt b E s h τ m R W j Vs XX Cch) {C C₄ : ℝ}
    (hC0 : 0 ≤ C) (hB : CovBound b E (b3Jet b E) R C W K (Fin np)) (h4 : FreshFour b W E C₄)
    (hnn : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      0 ≤ layerErr b E (b3Jet b E) XX)
    (g g' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    CovLayerAt b3CovErr b3CovZ b E τ m s h R Vs j (C * (Cch + 1)) 6 (Sum.inl g)
      (Sum.inl g') := by
  unfold CovLayerAt
  obtain ⟨hXm, hXinv, hrel⟩ := hch
  have hV := Modul.eq_of_growth hj hVs
  have hVm : Measurable Vs :=
    hVs.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set X' : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) →
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fun x => XX (b3Rebuild W j x)
  set U' : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) →
      Matrix (Fin 2 × Fin W) (SrcCol K (Fin np)) ℂ :=
    fun x => b3ClosedFrameAt b E s h τ m W j Vs (b3Rebuild W j x)
  have hX'm : Measurable X' := hXm.comp (measurable_b3Rebuild W j)
  have hU'm : Measurable U' :=
    (measurable_b3ClosedFrameAt b E s h τ m W j hVm).comp (measurable_b3Rebuild W j)
  have hXy : ∀ y, X' (b3Past W j y) = XX y := fun y => by
    simp only [X', b3Rebuild_b3Past, hXinv]
  have hUy : ∀ y, U' (b3Past W j y) = b3ClosedFrameAt b E s h τ m W j Vs y := fun y => by
    simp only [U', b3Rebuild_b3Past]
    exact b3ClosedFrameAt_b3Ext b E s h τ m hj le_rfl hV y
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j Vs
  have hA : A =ᵐ[μ] b3AliveM b E s h τ m R W j Vs := b3Alive_ae_eq hb1 hE1 hE2 s h τ m R W j Vs
  have hAm : MeasurableSet[b3Sigma W j np] (b3AliveM b E s h τ m R W j Vs) :=
    Modul.measurableSet_b3AliveM_past (b := b) (E := E) s h τ m R hj le_rfl hVs
  obtain ⟨A', hA'm, hA'⟩ := hAm
  set S : Set (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) :=
    A' ∩ {x | ((U' x)ᴴ * U' x).trace.re ≤ R} ∩ {x | (X' x).IsHermitian}
  have hSm : MeasurableSet S :=
    (hA'm.inter (measurableSet_le (measurable_trace_re_gram hU'm) measurable_const)).inter
      (measurableSet_isHermitian hX'm)
  set Q : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) → LayerSample W .oneBlockOnePort → ℂ :=
    fun x f => incr b E (X' x) (U' x) g f * incr b E (X' x) (U' x) g' f
  have hm1 := (measurable_layerGramEntry b E (hX'm.comp measurable_fst)
    (hU'm.comp measurable_fst) measurable_snd g).sub
    (measurable_gramEntry_gramPair (hU'm.comp measurable_fst) g)
  have hm2 := (measurable_layerGramEntry b E (hX'm.comp measurable_fst)
    (hU'm.comp measurable_fst) measurable_snd g').sub
    (measurable_gramEntry_gramPair (hU'm.comp measurable_fst) g')
  have hQm : Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => Q z.1 z.2 := hm1.mul hm2
  set Ψ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ :=
    (S ×ˢ Set.univ).indicator fun z => Q z.1 z.2
  have hΨm : Measurable Ψ := hQm.indicator (hSm.prod MeasurableSet.univ)
  have hΨ1 : ∀ x f, x ∈ S → Ψ (x, f) = Q x f := fun x f hx =>
    Set.indicator_of_mem (Set.mk_mem_prod hx (Set.mem_univ f)) _
  have hΨ0 : ∀ x f, x ∉ S → Ψ (x, f) = 0 := fun x f hx =>
    Set.indicator_of_notMem (fun hh => hx (Set.mem_prod.mp hh).1) _
  have hpast : ∀ᵐ y ∂μ, y ∈ A → b3Past W j y ∈ S := by
    filter_upwards [hrel, hA] with y hy hyA hyAl
    have hyM : y ∈ b3AliveM b E s h τ m R W j Vs := (Iff.of_eq hyA).mp hyAl
    refine ⟨⟨by rw [← hA'] at hyM; exact hyM, ?_⟩, ?_⟩
    · show ((U' (b3Past W j y))ᴴ * U' (b3Past W j y)).trace.re ≤ R
      rw [hUy]
      exact (hyAl.2 j hj le_rfl).le
    · show (X' (b3Past W j y)).IsHermitian
      rw [hXy]
      exact (hy hyAl).1
  have heq : A.indicator (fun y => b3dX b E s h τ m W j Vs (Sum.inl g) y *
      b3dX b E s h τ m W j Vs (Sum.inl g') y) =ᵐ[μ]
      fun y => Ψ (b3Past W j y, freshSample W j y.1.1) := by
    filter_upwards [hrel, hA, hpast] with y hy hyA hyp
    by_cases hyAl : y ∈ A
    · rw [Set.indicator_of_mem hyAl, hΨ1 _ _ (hyp hyAl)]
      obtain ⟨-, -, hfr, -, -⟩ := hy hyAl
      simp only [Q, hXy, hUy, incr, layerGram, b3dX, b3X, cEntry, b3ClosedGramAt, hfr]
      rfl
    · have hyM : y ∉ b3AliveM b E s h τ m R W j Vs := fun hh => hyAl ((Iff.of_eq hyA).mpr hh)
      have hx : b3Past W j y ∉ S := fun hx => hyM (by rw [← hA']; exact hx.1.1)
      rw [Set.indicator_of_notMem hyAl, hΨ0 _ _ hx]
  have hint : Integrable (fun y => Ψ (b3Past W j y, freshSample W j y.1.1)) μ := by
    refine integrable_closed_of_fresh_b3 b j hΨm (2 * max R 0 ^ 2 * (C₄ + 1)) fun x => ?_
    by_cases hx : x ∈ S
    · simp only [hΨ1 x _ hx]
      exact lintegral_incr_mul_le (h4 (X' x) hx.2).1 (h4 (X' x) hx.2).2 (U' x)
        (le_max_right R 0) (hx.1.2.trans (le_max_left R 0)) g g'
    · simp [hΨ0 x _ hx]
  have hce := (condExp_congr_ae (m := b3Sigma W j np) heq).trans
    (condExp_closed_fresh b j hΨm hint)
  filter_upwards [hce, hrel, hpast] with y hy hyr hyp hyAl
  rw [hy]
  obtain ⟨-, hN, -, hJ, hZ⟩ := hyr hyAl
  have hxin := hyp hyAl
  rw [← hXy y, ← hUy y] at hJ
  rw [← hXy y] at hN
  rw [← hXy y, ← hUy y] at hZ
  set x := b3Past W j y
  have hint_eq : ∫ f, Ψ (x, f) ∂freshLaw W b = ∫ f, Q x f ∂freshLaw W b :=
    integral_congr_ae (Eventually.of_forall fun f => hΨ1 x f hxin)
  rw [hint_eq]
  have hbd := hB (X' x) hxin.2 (U' x) (by rw [hJ, srcSignature_eq]) hxin.1.2 g g'
  have hcc : cCov b E (Sum.inl g) (Sum.inl g') (b3ClosedGramAt b E s h τ m W j Vs y) =
      gramCovEntry (transportD0 b E) (sigD (sigVals K (Fin np))) g g'
        (gramPair (nearProjection W) (U' x)) := by
    rw [← srcSignature_eq, hUy y]; rfl
  rw [hcc]
  have he : layerErr b E (b3Jet b E) (X' x) = b3CovErr b E np τ m s h K W Vs j y :=
    layerErr_b3Jet_eq hN
  have he0 : 0 ≤ b3CovErr b E np τ m s h K W Vs j y := by rw [← he]; exact hnn _ hxin.2
  rw [he] at hbd
  refine hbd.trans ?_
  rw [norm_b3CovZ]
  set ev := b3CovErr b E np τ m s h K W Vs j y
  set zv := b3CovZ b E np τ m s h K W Vs j y
  have hz0 : 0 ≤ zv := b3CovZ_nonneg b E np τ m s h K W Vs j y
  have hrem : layerRem W 1 ev = (W : ℝ)⁻¹ / Real.sqrt W + ev ^ 2 + ev ^ 6 := rfl
  rw [hrem]
  have hr0 : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W + ev ^ 2 + ev ^ 6 := by positivity
  have h1 : C * ev * contrGram b E (X' x) (U' x) ≤ C * ev * (Cch * zv) :=
    mul_le_mul_of_nonneg_left hZ (mul_nonneg hC0 he0)
  have h2 : C * ev * (Cch * zv) ≤ C * (Cch + 1) * (ev * zv) := by
    have := mul_nonneg (mul_nonneg hC0 he0) hz0
    nlinarith
  have h3 : C * ((W : ℝ)⁻¹ / Real.sqrt W + ev ^ 2 + ev ^ 6) ≤
      C * (Cch + 1) * ((W : ℝ)⁻¹ / Real.sqrt W + ev ^ 2 + ev ^ 6) := by
    have := mul_nonneg hC0 hr0
    nlinarith
  linarith

/-!
## The Gram pairs of `CovLayerHyp`
-/

/-- **`CovLayerHypGram b3CovErr b3CovZ` from the input hypotheses and LayerMean's closed chain.** -/
theorem covLayerHypGram_of_chain (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hCh : B3ClosedChainPin) : CovLayerHypGram b3CovErr b3CovZ := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  obtain ⟨C, W₀, hC0, hD⟩ := gram_layer_cov hGA hLp hP hb0 hb hκ R
  obtain ⟨C₄, W₄, -, h4⟩ := fresh_pow_bound hGA hb0 hb hκ
  obtain ⟨Cch, hCch, hevC⟩ := hCh b E np τ m T s h K Vs hFD R
  refine ⟨C * (Cch + 1), 6, by positivity, by norm_num, ?_⟩
  filter_upwards [hevC, hFD.2.2.2.2.2, eventually_ge_atTop W₀,
    eventually_ge_atTop W₄] with W hW hVW hW0 hW4 j hj g g'
  obtain ⟨XX, hch⟩ := hW j hj
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  exact covLayerAt_gram_step (by linarith) hE1 hE2 s h τ m R hj'.1.1 hVW.1 hCch hch hC0
    (fun XX hXX V hJ hTr e e' => hD W hW0 E hE (b3Jet b E) (b3Jet_spec hb0 hb hE1 hE2) XX hXX V
      (sigVals K (Fin np)) (abs_sigVals_le K _) hJ hTr e e') (h4 W hW4 E hE)
    (fun XX hXX => layerErr_nonneg' hb hκ hE _ hXX) g g'

/-- **`e ≥ 0` on the alive set from the closed chain** (`e = layerErr 𝕏_j`, `𝕏_j` Hermitian). -/
theorem covErrNonneg_of_chain (hCh : B3ClosedChainPin) : CovErrNonneg b3CovErr := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨-, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  obtain ⟨Cch, -, hevC⟩ := hCh b E np τ m T s h K Vs hFD R
  filter_upwards [hevC] with W hW j hj
  obtain ⟨XX, -, -, hrel⟩ := hW j hj
  filter_upwards [hrel] with y hy hyA
  obtain ⟨hH, hN, -⟩ := hy hyA
  have := layerErr_nonneg' hb hκ hE (b3Jet b E) hH
  rw [layerErr_b3Jet_eq hN] at this
  exact this

/-!
## Merging with the `𝒦` pairs; the targets
-/

/-- **`CovLayerHypGram + CovLayerHypK + (e ≥ 0) ⇒ CovLayerHyp`.** -/
theorem covLayerHyp_of_gramK {e Z : CovField} (hG : CovLayerHypGram e Z) (hK : CovLayerHypK e Z)
    (hnn : CovErrNonneg e) : CovLayerHyp e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨CG, NG, hCG, hNG, hevG⟩ := hG b E np τ m T s h K Vs hFD R
  obtain ⟨CK, NK, hCK, hNK, hevK⟩ := hK b E np τ m T s h K Vs hFD R
  refine ⟨2 * (CG + CK), max NG NK, by positivity, le_max_of_le_right hNK, ?_⟩
  filter_upwards [hevG, hevK, hnn b E np τ m T s h K Vs hFD R] with W hWG hWK hWn j hj c c'
  have hw : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by positivity
  have hKc : ((∃ ij, c = Sum.inr ij) ∨ (∃ ij, c' = Sum.inr ij)) →
      CovLayerAt e Z b E τ m s h R (Vs W) j (2 * (CG + CK)) (max NG NK) c c' := by
    intro hc
    filter_upwards [hWK j hj c c' hc, hWn j hj] with y hy hy0 hyA
    exact cov_bound_weaken hCK (by linarith) (hy0 hyA) (norm_nonneg _) hw hNK
      (le_max_right _ _) (hy hyA)
  rcases c with g | ij
  · rcases c' with g' | kl
    · filter_upwards [hWG j hj g g', hWn j hj] with y hy hy0 hyA
      exact cov_bound_weaken hCG (by linarith) (hy0 hyA) (norm_nonneg _) hw hNG
        (le_max_left _ _) (hy hyA)
    · exact hKc (Or.inr ⟨kl, rfl⟩)
  · exact hKc (Or.inl ⟨ij, rfl⟩)

/-- **`CovLayerHyp b3CovErr b3CovZ`** from the input hypotheses, LayerMean's closed chain and the
`𝒦` pairs.
-/
theorem covLayerHyp_of_chain (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hCh : B3ClosedChainPin) (hK : CovLayerHypK b3CovErr b3CovZ) :
    CovLayerHyp b3CovErr b3CovZ :=
  covLayerHyp_of_gramK (covLayerHypGram_of_chain hGA hLp hP hCh) hK (covErrNonneg_of_chain hCh)

/-- **Target `KStepCov`** from the closed chain. -/
theorem kStepCov_of_chain (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hL2 : GenStepMemL2) (hM : GenStepMeanL2) (hCh : B3ClosedChainPin)
    (hK : CovLayerHypK b3CovErr b3CovZ) (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp)
    (hg : ClosedCondLp) (hD : B3ClosedContrDecay) : KStepCov :=
  kStepCov_of_layer hL2 hM (covLayerHyp_of_chain hGA hLp hP hCh hK)
    (covErrMoments_b3CovErr h0 h1 hg) (covDecayHyp_b3CovZ hD)

/-- **Target `GramSumStepCov`** from the closed chain. -/
theorem gramSumStepCov_of_chain (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hL2 : GramSumStepMemL2) (hM : GramSumStepMeanL2)
    (hCh : B3ClosedChainPin) (hK : CovLayerHypK b3CovErr b3CovZ) (h0 : ClosedJet0Lp)
    (h1 : ClosedJet1Lp) (hg : ClosedCondLp) (hD : B3ClosedContrDecay) : GramSumStepCov :=
  gramSumStepCov_of_layer hL2 hM (covLayerHyp_of_chain hGA hLp hP hCh hK)
    (covErrMoments_b3CovErr h0 h1 hg) (covDecayHyp_b3CovZ hD)

/-- **`ComplexClosedSummed` from the layer hypotheses** with the closed chain. -/
theorem complexClosedSummed_of_chain (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hGD : GramSumStepDrift)
    (hB : GenReqBirth) (hKD : KStepDrift) (hCh : B3ClosedChainPin)
    (hK : CovLayerHypK b3CovErr b3CovZ) (hC : ConjLayerHyp b3CovErr b3CovZ)
    (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp) (hg : ClosedCondLp) (hD : B3ClosedContrDecay) :
    ComplexClosedSummed :=
  complexClosedSummed_of_layer hGD hB hKD (covLayerHyp_of_chain hGA hLp hP hCh hK) hC
    (covErrMoments_b3CovErr h0 h1 hg) (covDecayHyp_b3CovZ hD)

end BlockBand.SourceProcess.PhysApprox.B3
