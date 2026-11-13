module

public import BlockBand.SourceProcess.PhysApprox.B3MomK
public import BlockBand.SourceProcess.PhysApprox.Meas
public import BlockBand.SourceProcess.FullSourceStops.CurrentPast
public import BlockBand.SourceProcess.ClosedIdent.Restrict
public import BlockBand.Transmission.Generator.Basic

/-!
# Tightness at `⌊Wt₁⌋` from the stops, and the modulus

`ComplexClosedTight` is split into its two conjuncts:
* `ComplexClosedTightAt` (tightness of every coordinate at `⌊Wt₁⌋` on the cap event) and
* `ComplexClosedModulus` (the modulus on `[t₁, T]` of the births-removed coordinates);
`complexClosedTight_of_parts` recombines them.

Proved here:
* measurability of the closed process at every length (`measurable_b3ClosedGramAt`,
  `measurable_b3KCorrAt`, `measurable_b3ClosedKAt`) and a Borel version of the alive set,
  a.e. equal to `b3Alive` (`b3Alive_ae_eq`, from `physCapEvent_ae_eq`);
* `norm_gramEntry_le`: every Gram coordinate is at most `Re Tr M`;
* **`complexClosedTightAt_of`**: `ComplexKStoppedMoment + ComplexClosedStopTail ⇒
  ComplexClosedTightAt`; `complexClosedTightAt_of_max`, `complexClosedTight_of_max` from the
  maximal form `ComplexKStoppedMomentMax`. Gram coordinates: bounded by the trace before the
  stop. `𝒦` coordinates: Markov on `ComplexKStoppedMoment` at `j = ⌊Wt₁⌋ − 1` before the stop.

Stated as a hypothesis: `ComplexClosedStopTail` (complex copy of `ClosedStopTail`): the closed
trace stop is rarely reached on the cap event.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingAux BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum
open scoped NNReal ENNReal

variable {W np K : ℕ}

/-!
## Measurability of the closed process
-/

theorem measurable_stepProd_transportN (b E : ℝ) (j₀ k : ℕ) :
    Measurable fun ω : GrowthPath W => stepProd (fun i => transportN b E W i ω) j₀ k := by
  induction k with
  | zero => simp only [stepProd]; exact measurable_const
  | succ k ih =>
      simp only [stepProd]
      exact measurable_matrix_mul' ih (measurable_transportN b E (j₀ + k))

theorem measurable_b3OpenFrameAt (b E s : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs) :
    Measurable fun x : ProbedPath W np => b3OpenFrameAt b E s τ m W j Vs x := by
  refine Measurable.of_eval_matrix _ fun z col => ?_
  cases col with
  | inl k =>
      simp only [b3OpenFrameAt, of_apply, Sum.elim_inl]
      exact (measurable_matrix_mul' (measurable_matrix_conjTranspose'
        ((measurable_stepProd_transportN b E _ _).comp measurable_fst))
        (hV.comp measurable_fst)).eval_matrix
  | inr i =>
      simp only [b3OpenFrameAt, of_apply, Sum.elim_inr]
      exact (measurable_probeFrame b E W j τ m).eval_matrix

theorem measurable_physClosingMapAt_comp {α : Type*} [MeasurableSpace α] (b E s h : ℝ)
    (n : ℕ) {f : α → GrowthPath W} {z : α → ℂ} (hf : Measurable f) (hz : Measurable z) :
    Measurable fun a => physClosingMapAt b E s h W n (f a) (z a) :=
  measurable_closingMap ((measurable_scatteringMatrix b E _).comp hf)
    (measurable_farEmbed ((measurable_omittedProj b E h _).comp hf))
    (measurable_farEmbed ((measurable_closingPairing b E h _).comp hf)) hz

theorem measurable_b3ClosedFrameAt (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs) :
    Measurable fun y : ProbedPath W np × ℝ => b3ClosedFrameAt b E s h τ m W j Vs y :=
  measurable_matrix_mul' (measurable_matrix_conjTranspose' (measurable_physClosingMapAt_comp
    b E s h j (measurable_fst.comp measurable_fst) (measurable_phase.comp measurable_snd)))
    ((measurable_b3OpenFrameAt b E s τ m W j hV).comp measurable_fst)

theorem measurable_b3ClosedGramAt (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs) :
    Measurable fun y : ProbedPath W np × ℝ => b3ClosedGramAt b E s h τ m W j Vs y := by
  have hF := measurable_b3ClosedFrameAt b E s h τ m W j hV
  unfold b3ClosedGramAt gramPair sourceGram nearGram
  exact (measurable_matrix_mul' (measurable_matrix_conjTranspose' hF) hF).prodMk
    (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hF)
      measurable_const) hF)

theorem measurable_b3KCorrAt (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ => b3KCorrAt b E s h τ m W j y := by
  have hω : Measurable fun y : ProbedPath W np × ℝ => y.1.1 := measurable_fst.comp measurable_fst
  have hz : Measurable fun y : ProbedPath W np × ℝ => phase y.2 :=
    measurable_phase.comp measurable_snd
  have hV : Measurable fun y : ProbedPath W np × ℝ => probeFrame b E W j τ m y.1 :=
    (measurable_probeFrame b E W j τ m).comp measurable_fst
  have hS := (measurable_scatteringMatrix b E j).comp hω
  have hA := measurable_farEmbed ((measurable_omittedProj b E h (closeLen s W)).comp hω)
  have hP := measurable_farEmbed ((measurable_closingPairing b E h (closeLen s W)).comp hω)
  have hN : Measurable fun y : ProbedPath W np × ℝ => closingN (scatteringMatrix b E W j y.1.1)
      (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1)) :=
    measurable_matrix_mul' (measurable_matrix_mul' hP hS) hA
  have hinv : Measurable fun y : ProbedPath W np × ℝ =>
      (1 - phase y.2 • closingN (scatteringMatrix b E W j y.1.1)
        (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
        (farEmbed (closingPairing b E h W (closeLen s W) y.1.1)))⁻¹ :=
    measurable_matrix_inv.comp
      (measurable_matrix_sub measurable_const (measurable_matrix_cmul hz hN))
  unfold b3KCorrAt
  exact measurable_matrix_cmul (measurable_const.mul hz) (measurable_matrix_mul'
    (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_mul'
      (measurable_matrix_conjTranspose' hV) hinv) hP) hS) hV)

theorem measurable_b3ClosedKAt (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ => b3ClosedKAt b E s h τ m W j y :=
  measurable_matrix_sub ((measurable_complexSourceK b E W j τ m).comp measurable_fst)
    (measurable_b3KCorrAt b E s h τ m W j)

/-!
## The alive set, up to a null set
-/

/-- The trace part of the alive set: `Re Tr M_i < R` for `n_s ≤ i ≤ j`. -/
def b3TraceOK (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    Set (ProbedPath W np × ℝ) :=
  {y | ∀ i, closeLen s W ≤ i → i ≤ j → ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re < R}

theorem b3Alive_eq (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    b3Alive b E s h τ m R W j Vs =
      {y | y.1.1 ∈ physCapEventC b E s h K W} ∩ b3TraceOK b E s h τ m R W j Vs := rfl

theorem measurable_reTrace_b3ClosedGramAt (b E s h : ℝ) (τ m : Fin np → ℝ) (W i : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs) :
    Measurable fun y : ProbedPath W np × ℝ =>
      ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re := by
  have hG := (measurable_b3ClosedGramAt b E s h τ m W i hV).fst
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  exact Finset.measurable_sum _ fun d _ => Complex.measurable_re.comp hG.eval_matrix

theorem measurableSet_b3TraceOK (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs) :
    MeasurableSet (b3TraceOK (np := np) b E s h τ m R W j Vs) := by
  rw [b3TraceOK, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => ?_
  by_cases h1 : closeLen s W ≤ i
  · by_cases h2 : i ≤ j
    · simp only [h1, h2, true_implies]
      exact measurableSet_lt (measurable_reTrace_b3ClosedGramAt b E s h τ m W i hV)
        measurable_const
    · simp only [h2, false_implies, imp_true_iff, Set.ofPred_true, MeasurableSet.univ]
  · simp only [h1, false_implies, Set.ofPred_true, MeasurableSet.univ]

/-- The Borel alive set (`physCapEventM` for the cap event). -/
def b3AliveM (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    Set (ProbedPath W np × ℝ) :=
  {y | y.1.1 ∈ ClosedIdent.physCapEventM b E s h K W} ∩ b3TraceOK b E s h τ m R W j Vs

theorem measurableSet_b3AliveM (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs) :
    MeasurableSet (b3AliveM (np := np) b E s h τ m R W j Vs) :=
  ((measurable_fst.comp measurable_fst)
    (ClosedIdent.measurableSet_physCapEventM b E s h K W)).inter
    (measurableSet_b3TraceOK b E s h τ m R W j hV)

/-- **The alive set is a.e. its Borel version** under `closedLaw`. -/
theorem b3Alive_ae_eq {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ)
    (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    b3Alive b E s h τ m R W j Vs =ᵐ[closedLaw b W np] b3AliveM b E s h τ m R W j Vs := by
  rw [b3Alive_eq, b3AliveM]
  refine EventuallyEqSet.inter ?_ EventuallyEqSet.rfl
  have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      (closedLaw b W np) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
  exact hq.preimage_ae_eq (ClosedIdent.physCapEvent_ae_eq hb hE1 hE2 s h K)

/-- Markov on a set that is a.e. Borel: `μ(S ∩ {C < ‖X‖}) ≤ E[1_S‖X‖⁴]/C⁴`. -/
theorem meas_inter_lt_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {S S' : Set α}
    (hS' : MeasurableSet S') (hSS : S =ᵐ[μ] S') {X : α → ℂ} (hX : Measurable X) {C : ℝ}
    (hC : 0 < C) :
    μ {y | y ∈ S ∧ C < ‖X y‖} ≤
      (∫⁻ y, S.indicator (fun y => ‖X y‖ₑ ^ 4) y ∂μ) / ENNReal.ofReal C ^ 4 := by
  have hint : ∫⁻ y, S.indicator (fun y => ‖X y‖ₑ ^ 4) y ∂μ =
      ∫⁻ y, S'.indicator (fun y => ‖X y‖ₑ ^ 4) y ∂μ :=
    lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hSS)
  have hset : {y | y ∈ S ∧ C < ‖X y‖} =ᵐ[μ] {y | y ∈ S' ∧ C < ‖X y‖} :=
    hSS.inter EventuallyEqSet.rfl
  rw [measure_congr hset, hint]
  refine (measure_mono ?_).trans (meas_ge_le_lintegral_div
    ((hX.enorm.pow_const 4).indicator hS').aemeasurable
    (pow_ne_zero 4 (ENNReal.ofReal_pos.2 hC).ne') (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  rintro y ⟨hy, hlt⟩
  simp only [Set.mem_ofPred_eq, Set.indicator_of_mem hy]
  refine pow_le_pow_left₀ zero_le ?_ 4
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hlt.le

/-!
## Gram coordinates are bounded by the trace
-/

theorem norm_gram_diagonal_le {ι c : Type*} [Fintype ι] [Fintype c] [DecidableEq ι]
    (V : Matrix ι c ℂ) (D : ι → ℂ) (hD : ∀ x, ‖D x‖ ≤ 1) (a b : c) :
    ‖(Vᴴ * diagonal D * V) a b‖ ≤ ((Vᴴ * V).trace).re := by
  have htr : ((Vᴴ * V).trace).re = ∑ x, ∑ d, ‖V x d‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [htr]
  rw [mul_apply]
  simp only [mul_diagonal, conjTranspose_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have hab : ‖V x a‖ * ‖V x b‖ ≤ ∑ d, ‖V x d‖ ^ 2 := by
    have h1 := Finset.single_le_sum (f := fun d => ‖V x d‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ a)
    have h2 := Finset.single_le_sum (f := fun d => ‖V x d‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b)
    nlinarith [norm_nonneg (V x a), norm_nonneg (V x b), sq_nonneg (‖V x a‖ - ‖V x b‖)]
  calc ‖V x a‖ * ‖D x‖ * ‖V x b‖ ≤ ‖V x a‖ * 1 * ‖V x b‖ := by
        gcongr; exact hD x
    _ ≤ _ := by rw [mul_one]; exact hab

/-- **Every Gram coordinate is at most `Re Tr M`.** -/
theorem norm_gramEntry_le {ι c : Type*} [Fintype ι] [Fintype c] [DecidableEq ι]
    (V : Matrix ι c ℂ) (Pd : ι → ℂ) (hP : ∀ x, ‖Pd x‖ ≤ 1) (e : Fin 2 × c × c) :
    ‖gramEntry e (gramPair (diagonal Pd) V)‖ ≤ ((gramPair (diagonal Pd) V).1.trace).re := by
  unfold gramEntry gramPair sourceGram nearGram
  split_ifs
  · have := norm_gram_diagonal_le V (fun _ => 1) (fun _ => by simp) e.2.1 e.2.2
    simpa [diagonal_one] using this
  · exact norm_gram_diagonal_le V Pd hP e.2.1 e.2.2

theorem norm_gramEntry_b3ClosedGramAt_le (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    ‖gramEntry e (b3ClosedGramAt b E s h τ m W j Vs y)‖ ≤
      ((b3ClosedGramAt b E s h τ m W j Vs y).1.trace).re :=
  norm_gramEntry_le _ _ (fun x => by split_ifs <;> simp) e

/-!
## The estimates and the reduction
-/

/-- **`ComplexClosedStopTail`** (the stop argument for the closed complex path; complex copy of
`ClosedStopTail`): for every `θ > 0` some trace level `R` is, eventually in `W`, reached by the
closed Gram process on `[n_s, ⌊WT⌋]` on the cap event with probability at most `θ`. -/
def ComplexClosedStopTail : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ θ : ℝ, 0 < θ → ∃ R : ℝ, ∀ᶠ W in atTop,
      closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i, closeLen s W ≤ i ∧
        i ≤ ⌊(W : ℝ) * T⌋₊ ∧ R ≤ ((b3ClosedGramAt b E s h τ m W i (Vs W) y).1.trace).re} ≤
        ENNReal.ofReal θ

/-- The first conjunct of `ComplexClosedTight`: tightness of every coordinate at `⌊Wt₁⌋` on the
cap event. -/
def ComplexClosedTightAt : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (c : CIdx K np) (t₁ : ℝ), s < t₁ → t₁ < T →
      ∀ θ : ℝ, 0 < θ → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧
          C < ‖b3X b E s h τ m W ⌊(W : ℝ) * t₁⌋₊ (Vs W) c y‖} ≤ ENNReal.ofReal θ

/-- **`ComplexClosedModulus`**: the second conjunct of `ComplexClosedTight`, the
vanishing modulus on `[t₁, T]` of every births-removed coordinate on the cap event. -/
def ComplexClosedModulus : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (c : CIdx K np) (t₁ : ℝ), s < t₁ → t₁ < T →
      ∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧
          ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧ η <
            ‖b3X b E s h τ m W ⌊(W : ℝ) * t⌋₊ (Vs W) c y -
              cEntry c (b3JumpAt b s τ m W ⌊(W : ℝ) * t⌋₊) (b3KJumpAt E s τ m W ⌊(W : ℝ) * t⌋₊) -
              (b3X b E s h τ m W ⌊(W : ℝ) * t'⌋₊ (Vs W) c y -
                cEntry c (b3JumpAt b s τ m W ⌊(W : ℝ) * t'⌋₊)
                  (b3KJumpAt E s τ m W ⌊(W : ℝ) * t'⌋₊))‖} ≤ ENNReal.ofReal θ

/-- **`ComplexClosedFourth`** (away from the finitely many prescribed births,
`E Σ_j |ΔZ_j|^p ≤ C_K W^{1-p/2} → 0` at `p = 4`; complex copy of `ClosedFourth`): the summed
stopped fourth moments of the steps of every coordinate at the steps without a birth tend to
`0`. -/
def ComplexClosedFourth : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (c : CIdx K np),
      Tendsto (fun W : ℕ => ∑ j ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter
          (fun j => ¬ IsBirthStep τ W j),
        ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => ‖b3dX b E s h τ m W j (Vs W) c y‖ₑ ^ 4) y ∂closedLaw b W np) atTop (𝓝 0)

/-- **`TargetModulus`**: the summed errors, the summed fourth moments of the steps and the stop
tail give the modulus. This is the complex copy of `closedTight_of` (modulus half), with the
complex coordinates read through real parts `Re(uΔX)` (bilinear bracket `b3SummedErr`, conjugate
bracket `b3ConjErr`); it is proved in `targetModulus_holds`. -/
def TargetModulus : Prop :=
  ComplexClosedSummed → ComplexClosedFourth → ComplexClosedStopTail → ComplexClosedModulus

theorem complexClosedTight_of_parts (hA : ComplexClosedTightAt) (hM : ComplexClosedModulus) :
    ComplexClosedTight :=
  fun b E np τ m T s h K Vs hF c t₁ h1 h2 =>
    ⟨hA b E np τ m T s h K Vs hF c t₁ h1 h2, hM b E np τ m T s h K Vs hF c t₁ h1 h2⟩

theorem eventually_closeLen_lt {s t₁ : ℝ} (hs : 0 ≤ s) (hst : s < t₁) :
    ∀ᶠ W : ℕ in atTop, closeLen s W + 1 ≤ ⌊(W : ℝ) * t₁⌋₊ := by
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / (t₁ - s))
  filter_upwards [eventually_ge_atTop N] with W hW
  have hW' : (N : ℝ) ≤ W := by exact_mod_cast hW
  have hpos : 0 < t₁ - s := by linarith
  have h1 : 1 ≤ (W : ℝ) * (t₁ - s) := by
    calc (1 : ℝ) = 1 / (t₁ - s) * (t₁ - s) := by field_simp
      _ ≤ W * (t₁ - s) := mul_le_mul_of_nonneg_right (hN.trans hW') hpos.le
  apply Nat.le_floor
  have := Nat.floor_le (mul_nonneg (Nat.cast_nonneg W) hs)
  push_cast
  nlinarith

/-- The real inequality behind the choice of the `𝒦` level. -/
theorem le_half_mul_pow_four {C₄ θ : ℝ} (hθ : 0 < θ) :
    max C₄ 0 ≤ θ / 2 * max 1 (2 * max C₄ 0 / θ + 1) ^ 4 := by
  set C := max 1 (2 * max C₄ 0 / θ + 1)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC2 : 2 * max C₄ 0 / θ + 1 ≤ C := le_max_right _ _
  have hC4 : C ≤ C ^ 4 := le_self_pow₀ hC1 (by norm_num)
  have h3 : 2 * max C₄ 0 / θ ≤ C := by linarith
  rw [div_le_iff₀ hθ] at h3
  have h4 : max C₄ 0 ≤ θ / 2 * C := by nlinarith
  exact h4.trans (mul_le_mul_of_nonneg_left hC4 (by positivity))

/-- **Tightness at `⌊Wt₁⌋` from the stops**: `ComplexKStoppedMoment + ComplexClosedStopTail ⇒
ComplexClosedTightAt`. -/
theorem complexClosedTightAt_of (hK : ComplexKStoppedMoment) (hS : ComplexClosedStopTail) :
    ComplexClosedTightAt := by
  intro b E np τ m T s h K Vs hF c t₁ hst hlt θ hθ
  obtain ⟨hD, hs0, -, -, -, hVs⟩ := id hF
  obtain ⟨R, hR⟩ := hS b E np τ m T s h K Vs hF (θ / 2) (by positivity)
  have hidx := eventually_closeLen_lt hs0.le hst
  have hT : ∀ W : ℕ, ⌊(W : ℝ) * t₁⌋₊ ≤ ⌊(W : ℝ) * T⌋₊ := fun W =>
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left hlt.le (Nat.cast_nonneg W))
  cases c with
  | inl e =>
      obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 (hR.and hidx)
      refine ⟨R, W₀, fun W hW => ?_⟩
      obtain ⟨hRW, hiW⟩ := hW₀ W hW
      refine (measure_mono ?_).trans (hRW.trans (ENNReal.ofReal_le_ofReal (by linarith)))
      rintro y ⟨hcap, hC⟩
      refine ⟨hcap, ⌊(W : ℝ) * t₁⌋₊, by omega, hT W, ?_⟩
      exact (hC.trans_le (norm_gramEntry_b3ClosedGramAt_le b E s h τ m W _ (Vs W) y e)).le
  | inr ij =>
      obtain ⟨C₄, hC₄⟩ := hK b E np τ m T s h K Vs hF R
      have hb1 : b < 1 := by linarith [hD.2.1]
      obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 ((hR.and hidx).and (hC₄.and hVs))
      refine ⟨max 1 (2 * max C₄ 0 / θ + 1), W₀, fun W hW => ?_⟩
      obtain ⟨⟨hRW, hiW⟩, hKW, hVW⟩ := hW₀ W hW
      have hj1 : closeLen s W ≤ ⌊(W : ℝ) * t₁⌋₊ - 1 := by omega
      have hj2 : ⌊(W : ℝ) * t₁⌋₊ - 1 < ⌊(W : ℝ) * T⌋₊ := by have := hT W; omega
      have hjn : ⌊(W : ℝ) * t₁⌋₊ - 1 + 1 = ⌊(W : ℝ) * t₁⌋₊ := by omega
      have hsub : {y | y.1.1 ∈ physCapEventC b E s h K W ∧
          max 1 (2 * max C₄ 0 / θ + 1) <
            ‖b3X b E s h τ m W ⌊(W : ℝ) * t₁⌋₊ (Vs W) (Sum.inr ij) y‖} ⊆
          {y | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i, closeLen s W ≤ i ∧
            i ≤ ⌊(W : ℝ) * T⌋₊ ∧ R ≤ ((b3ClosedGramAt b E s h τ m W i (Vs W) y).1.trace).re} ∪
          {y | y ∈ b3Alive b E s h τ m R W (⌊(W : ℝ) * t₁⌋₊ - 1) (Vs W) ∧
            max 1 (2 * max C₄ 0 / θ + 1) <
              ‖b3ClosedKAt b E s h τ m W (⌊(W : ℝ) * t₁⌋₊ - 1 + 1) y ij.1 ij.2‖} := by
        rintro y ⟨hcap, hy⟩
        by_cases hA : ∀ i, closeLen s W ≤ i → i ≤ ⌊(W : ℝ) * t₁⌋₊ - 1 →
            ((b3ClosedGramAt b E s h τ m W i (Vs W) y).1.trace).re < R
        · right
          refine ⟨⟨hcap, hA⟩, ?_⟩
          rw [hjn]
          exact hy
        · left
          push Not at hA
          obtain ⟨i, hi1, hi2, hi3⟩ := hA
          exact ⟨hcap, i, hi1, by omega, hi3⟩
      have hmV : Measurable (Vs W) :=
        hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
      have hX : Measurable fun y : ProbedPath W np × ℝ =>
          b3ClosedKAt b E s h τ m W (⌊(W : ℝ) * t₁⌋₊ - 1 + 1) y ij.1 ij.2 :=
        (measurable_b3ClosedKAt b E s h τ m W _).eval_matrix
      have hMk := meas_inter_lt_le (measurableSet_b3AliveM b E s h τ m R W
        (⌊(W : ℝ) * t₁⌋₊ - 1) hmV) (b3Alive_ae_eq hb1 hD.2.2.1 hD.2.2.2.1 s h τ m R W _ (Vs W))
        hX (C := max 1 (2 * max C₄ 0 / θ + 1)) (lt_of_lt_of_le one_pos (le_max_left _ _))
      have hbd : (∫⁻ y, (b3Alive b E s h τ m R W (⌊(W : ℝ) * t₁⌋₊ - 1) (Vs W)).indicator
          (fun y => ‖b3ClosedKAt b E s h τ m W (⌊(W : ℝ) * t₁⌋₊ - 1 + 1) y ij.1 ij.2‖ₑ ^ 4) y
            ∂closedLaw b W np) / ENNReal.ofReal (max 1 (2 * max C₄ 0 / θ + 1)) ^ 4 ≤
          ENNReal.ofReal (θ / 2) := by
        refine ENNReal.div_le_of_le_mul ((hKW _ hj1 hj2 ij).trans ?_)
        rw [← ENNReal.ofReal_pow (le_trans zero_le_one (le_max_left _ _)),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal ((le_max_left C₄ 0).trans (le_half_mul_pow_four hθ))
      calc closedLaw b W np _ ≤ closedLaw b W np _ + closedLaw b W np _ :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := add_le_add hRW (hMk.trans hbd)
        _ = ENNReal.ofReal θ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- **Tightness at `⌊Wt₁⌋`** from the maximal stopped moment `ComplexKStoppedMomentMax` and the
stop tail `ComplexClosedStopTail`. -/
theorem complexClosedTightAt_of_max (hK : ComplexKStoppedMomentMax) (hS : ComplexClosedStopTail) :
    ComplexClosedTightAt :=
  complexClosedTightAt_of (complexKStoppedMoment_of_max hK) hS

/-- **`ComplexClosedTight` from the maximal stopped moment, the stop tail and the modulus.** -/
theorem complexClosedTight_of_max (hK : ComplexKStoppedMomentMax) (hS : ComplexClosedStopTail)
    (hM : ComplexClosedModulus) : ComplexClosedTight :=
  complexClosedTight_of_parts (complexClosedTightAt_of_max hK hS) hM

/-- **`ComplexClosedTight` from `ComplexKStoppedMoment`, the stop tail and the modulus.** -/
theorem complexClosedTight_of (hK : ComplexKStoppedMoment) (hS : ComplexClosedStopTail)
    (hM : ComplexClosedModulus) : ComplexClosedTight :=
  complexClosedTight_of_parts (complexClosedTightAt_of hK hS) hM

end BlockBand.SourceProcess.PhysApprox.B3
