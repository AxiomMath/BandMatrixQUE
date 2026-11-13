module

public import BlockBand.SourceProcess.PhysApprox.B3StopTailPath
public import BlockBand.SourceProcess.PhysApprox.B3GenDoob
public import BlockBand.SourceProcess.ClosedSumProof.ClosedStep

/-!
# The stopped tail bound at fixed `W`

Abstract:
* `enorm_integral_indicator_le`: for an `m`-event `A'` a.e. equal to `A` and an integrable
  `1_A X`, `‖∫ 1_A X‖ₑ ≤ ∫⁻ ‖1_A (E[1_A X | m] - P)‖ₑ` whenever `P = 0` on `A`;
* `enorm_integral_indicator_sub_le`: `‖∫ 1_A X‖ₑ ≤ ∫⁻ ‖1_A (X - β)‖ₑ + ‖β‖ₑ` (probability).

Closed path (`μ = closedLaw b W np`, steps `I = [n_s, ⌊WT⌋)`, `dg x = (0, x, x)`):
* `driftT`, `birthT`: the drift and birth integrands of `b3SummedErr` for the pair
  `(dg x, dg x)`; `errT` picks the one of step `j`; **`sum_errT_le`**:
  `Σ_{j ∈ I} errT x j ≤ b3SummedErr (dg x) (dg x)`;
* **`fixedW_bound`**: given the adaptedness of the Borel alive sets (hypothesis `hAd`, the
  content of `measurableSet_b3AliveM_past`) and integrable stopped steps,
  `R · P(stop) ≤ 4K + birthC + Σ_x Σ_{j ∈ I} errT x j`. Proof: the stopped trace `Y`
  (`stopped_trace`) is `≥ 0` and `≥ R` on the stop event (Markov); `E Re Tr M_{n_s} ≤ 4K`
  (`ae_b3Tr_start_le`); a no-birth step has mean bounded by its drift integrand (the `M`-drift
  is `0`); a birth step has mean bounded by its birth integrand plus the birth jump.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.StopTail

open MeasureTheory Filter Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ClosedSum
open scoped ENNReal

/-!
## Abstract means of stopped steps
-/

section Abstract

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The mean of a stopped step is bounded by its conditional drift error** (`P = 0` on `A`). -/
theorem enorm_integral_indicator_le [IsFiniteMeasure μ] (hm : m ≤ m0) {A A' : Set Ω}
    (hA' : MeasurableSet[m] A') (hAA : A =ᵐ[μ] A') {X : Ω → ℂ}
    (hX : Integrable (A.indicator X) μ) {P : Ω → ℂ} (hP : ∀ ω ∈ A, P ω = 0) :
    ‖∫ ω, A.indicator X ω ∂μ‖ₑ ≤
      ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator X | m] ω - P ω) ω‖ₑ ∂μ := by
  have hAA' : A' ∩ A =ᵐ[μ] A :=
    (hAA.symm.inter (EventuallyEq.refl _ A)).trans (by rw [Set.inter_self])
  have e : A'.indicator (A.indicator X) =ᵐ[μ] A.indicator X := by
    rw [Set.indicator_indicator]
    exact indicator_ae_eq_of_ae_eq_set hAA'
  have h1 : μ[A.indicator X | m] =ᵐ[μ] A'.indicator (μ[A.indicator X | m]) :=
    (condExp_congr_ae e.symm).trans (condExp_indicator hX hA')
  have h2 : A'.indicator (μ[A.indicator X | m]) =ᵐ[μ] A.indicator (μ[A.indicator X | m]) :=
    indicator_ae_eq_of_ae_eq_set hAA.symm
  rw [← integral_condExp hm, integral_congr_ae (h1.trans h2)]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun ω => ?_))
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hP ω hω, sub_zero]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]

theorem enorm_indicator_le_sub (A : Set Ω) (X : Ω → ℂ) (β : ℂ) (ω : Ω) :
    ‖A.indicator X ω‖ₑ ≤ ‖A.indicator (fun ω => X ω - β) ω‖ₑ + ‖β‖ₑ := by
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
    calc ‖X ω‖ₑ = ‖(X ω - β) + β‖ₑ := by rw [sub_add_cancel]
      _ ≤ _ := enorm_add_le _ _
  · rw [Set.indicator_of_notMem hω]
    simp

theorem lintegral_indicator_le_sub [IsProbabilityMeasure μ] (A : Set Ω) (X : Ω → ℂ) (β : ℂ) :
    ∫⁻ ω, ‖A.indicator X ω‖ₑ ∂μ ≤ ∫⁻ ω, ‖A.indicator (fun ω => X ω - β) ω‖ₑ ∂μ + ‖β‖ₑ := by
  refine (lintegral_mono fun ω => enorm_indicator_le_sub A X β ω).trans (le_of_eq ?_)
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- **The mean of a stopped birth step** is bounded by its birth error plus the jump. -/
theorem enorm_integral_indicator_sub_le [IsProbabilityMeasure μ] (A : Set Ω) (X : Ω → ℂ)
    (β : ℂ) :
    ‖∫ ω, A.indicator X ω ∂μ‖ₑ ≤ ∫⁻ ω, ‖A.indicator (fun ω => X ω - β) ω‖ₑ ∂μ + ‖β‖ₑ :=
  (enorm_integral_le_lintegral_enorm _).trans (lintegral_indicator_le_sub A X β)

end Abstract

/-!
## The error integrands of `b3SummedErr` on the trace coordinates
-/

variable {W np K : ℕ}

section Errs

variable (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
  (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)

/-- The drift integrand of `b3SummedErr` at step `j`, coordinate `dg x`. -/
def driftT (x : SrcCol K (Fin np)) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
      (closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator
          (b3dX b E s h τ m W j Vs (Sum.inl (dg x) : CIdx K np)) | b3Sigma W j np] y -
        (W : ℂ)⁻¹ * cDrift b E (Sum.inl (dg x) : CIdx K np)
          (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ ∂closedLaw b W np

/-- The birth integrand of `b3SummedErr` at step `j`, coordinate `dg x`. -/
def birthT (x : SrcCol K (Fin np)) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
      b3dX b E s h τ m W j Vs (Sum.inl (dg x) : CIdx K np) y -
        cEntry (Sum.inl (dg x) : CIdx K np) (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j)) y‖ₑ
    ∂closedLaw b W np

/-- The error integrand of step `j`: birth integrand at a birth step, drift integrand otherwise. -/
def errT (x : SrcCol K (Fin np)) (j : ℕ) : ℝ≥0∞ :=
  if IsBirthStep τ W j then birthT b E s h τ m R W Vs x j else driftT b E s h τ m R W Vs x j

/-- **The summed error integrands are part of `b3SummedErr`.** -/
theorem sum_errT_le (T : ℝ) (x : SrcCol K (Fin np)) :
    ∑ j ∈ Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, errT b E s h τ m R W Vs x j ≤
      b3SummedErr b E s T h τ m R W Vs (Sum.inl (dg x)) (Sum.inl (dg x)) := by
  unfold errT
  rw [sum_ite, add_comm]
  unfold b3SummedErr
  exact add_le_add (le_add_right le_rfl) le_rfl

end Errs

/-!
## The bound at fixed `W`
-/

/-- The stop event of `ComplexClosedStopTail` at width `W`. -/
def stopSet (b E s h : ℝ) (τ m : Fin np → ℝ) (T R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    Set (ProbedPath W np × ℝ) :=
  {y | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i, closeLen s W ≤ i ∧ i ≤ ⌊(W : ℝ) * T⌋₊ ∧
    R ≤ ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re}

theorem measurable_b3dX {b E s h : ℝ} {τ m : Fin np → ℝ} {W j : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (x : SrcCol K (Fin np)) :
    Measurable (b3dX b E s h τ m W j Vs (Sum.inl (dg x) : CIdx K np)) := by
  have h1 := (ClosedSumProof.measurable_gramEntry (dg x)).comp
    (measurable_b3ClosedGramAt b E s h τ m W (j + 1) hV)
  have h2 := (ClosedSumProof.measurable_gramEntry (dg x)).comp
    (measurable_b3ClosedGramAt b E s h τ m W j hV)
  exact h1.sub h2

/-- The stopped step is a.e. strongly measurable. -/
theorem aestronglyMeasurable_stepX {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W : ℕ}
    (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (x : SrcCol K (Fin np)) (j : ℕ) :
    AEStronglyMeasurable (stepX b E s h τ m R W Vs x j) (closedLaw b W np) :=
  (((measurable_b3dX hV x).indicator (measurableSet_b3AliveM b E s h τ m R W j hV)).aemeasurable
    |>.aestronglyMeasurable).congr
    (indicator_ae_eq_of_ae_eq_set (b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs)).symm

/-- The mean of one stopped trace-coordinate step. -/
theorem enorm_integral_stepX_le {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W : ℕ}
    (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {j : ℕ}
    (hAd : MeasurableSet[b3Sigma W j np] (b3AliveM b E s h τ m R W j Vs))
    (x : SrcCol K (Fin np)) (hI : Integrable (stepX b E s h τ m R W Vs x j) (closedLaw b W np)) :
    ‖∫ y, stepX b E s h τ m R W Vs x j y ∂closedLaw b W np‖ₑ ≤
      errT b E s h τ m R W Vs x j +
        if IsBirthStep τ W j then ‖(b3BirthAt b τ m W j).1 x x‖ₑ else 0 := by
  unfold errT
  split_ifs with hj
  · have := enorm_integral_indicator_sub_le (μ := closedLaw b W np)
      (b3Alive b E s h τ m R W j Vs) (b3dX b E s h τ m W j Vs (Sum.inl (dg x) : CIdx K np))
      (cEntry (Sum.inl (dg x) : CIdx K np) (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j))
    rwa [cEntry_dg_birth] at this
  · rw [add_zero]
    exact enorm_integral_indicator_le (gen_sigma_le W j np) hAd
      (b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs) hI fun y _ => by rw [cDrift_dg, mul_zero]

/-- **The stop bound at fixed `W`.** -/
theorem fixedW_bound {b E s h T : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W : ℕ}
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) (hτ : ∀ i, s < τ i)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : IsTimeSFrame b E s h K W Vs)
    (hAd : ∀ j, closeLen s W ≤ j →
      MeasurableSet[b3Sigma W j np] (b3AliveM b E s h τ m R W j Vs))
    (hI : ∀ j ∈ Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∀ x : SrcCol K (Fin np),
      Integrable (stepX b E s h τ m R W Vs x j) (closedLaw b W np)) :
    ENNReal.ofReal R * closedLaw b W np (stopSet b E s h τ m T R W Vs) ≤
      ENNReal.ofReal (4 * K + birthC b m) + ∑ x : SrcCol K (Fin np),
        ∑ j ∈ Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, errT b E s h τ m R W Vs x j := by
  set μ := closedLaw b W np
  set n := closeLen s W
  set I := Ico n ⌊(W : ℝ) * T⌋₊
  have hb1 : b < 1 := by linarith
  by_cases hnN : n ≤ ⌊(W : ℝ) * T⌋₊
  swap
  · have : stopSet b E s h τ m T R W Vs = ∅ := by
      ext y
      simp only [stopSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro - ⟨i, h1, h2, -⟩
      exact hnN (h1.trans h2)
    rw [this, measure_empty, mul_zero]
    exact zero_le
  have hmV : Measurable Vs :=
    hVs.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set Y : ProbedPath W np × ℝ → ℝ := fun y => b3Tr b E s h τ m W n Vs y +
    ∑ j ∈ I, (∑ x, stepX b E s h τ m R W Vs x j y).re
  have hstart := ae_b3Tr_start_le (m := m) hb hE1 hE2 hW hτ hVs
  have hX0 : Integrable (b3Tr b E s h τ m W n Vs) μ :=
    Integrable.mono' (integrable_const ((4 : ℝ) * K))
      (measurable_reTrace_b3ClosedGramAt b E s h τ m W n hmV).aestronglyMeasurable
      (by
        filter_upwards [hstart] with y hy
        rw [Real.norm_eq_abs, abs_of_nonneg (b3Tr_nonneg _ _ _ _ _ _ _ _ _ y)]
        exact hy)
  have hF : ∀ j ∈ I, Integrable (fun y => (∑ x, stepX b E s h τ m R W Vs x j y).re) μ :=
    fun j hj => (integrable_finsetSum _ fun x _ => hI j hj x).re
  have hYi : Integrable Y μ := hX0.add (integrable_finsetSum _ fun j hj => hF j hj)
  have hpath := stopped_trace (K := K) b E s h τ m R T W Vs hnN
  -- Markov
  have hM : ENNReal.ofReal R * μ (stopSet b E s h τ m T R W Vs) ≤ ENNReal.ofReal (∫ y, Y y ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hYi (ae_of_all _ fun y => (hpath y).1)]
    refine (mul_le_mul_right (measure_mono fun y hy => ?_) _).trans
      (mul_meas_ge_le_lintegral₀ hYi.aemeasurable.ennreal_ofReal _)
    exact ENNReal.ofReal_le_ofReal ((hpath y).2 hy)
  refine hM.trans ?_
  -- the mean of the stopped trace
  have hstep : ∀ j ∈ I, ∫ y, (∑ x, stepX b E s h τ m R W Vs x j y).re ∂μ ≤
      ∑ x, ‖∫ y, stepX b E s h τ m R W Vs x j y ∂μ‖ := by
    intro j hj
    have e : ∫ y, (∑ x, stepX b E s h τ m R W Vs x j y).re ∂μ =
        (∫ y, ∑ x, stepX b E s h τ m R W Vs x j y ∂μ).re :=
      integral_re (𝕜 := ℂ) (integrable_finsetSum _ fun x _ => hI j hj x)
    rw [e, integral_finsetSum _ fun x _ => hI j hj x]
    exact (Complex.re_le_norm _).trans (norm_sum_le _ _)
  have hs0 : ∫ y, b3Tr b E s h τ m W n Vs y ∂μ ≤ 4 * K := by
    refine (integral_mono_ae hX0 (integrable_const _) hstart).trans (le_of_eq ?_)
    simp
  have hY : ∫ y, Y y ∂μ ≤ 4 * K + ∑ j ∈ I, ∑ x, ‖∫ y, stepX b E s h τ m R W Vs x j y ∂μ‖ := by
    simp only [Y]
    rw [integral_add hX0 (integrable_finsetSum _ fun j hj => hF j hj),
      integral_finsetSum _ fun j hj => hF j hj]
    exact add_le_add hs0 (sum_le_sum hstep)
  have hnn : ∀ j ∈ I, 0 ≤ ∑ x, ‖∫ y, stepX b E s h τ m R W Vs x j y ∂μ‖ := fun j _ =>
    sum_nonneg fun x _ => norm_nonneg _
  refine (ENNReal.ofReal_le_ofReal hY).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (sum_nonneg hnn), ENNReal.ofReal_sum_of_nonneg hnn]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => norm_nonneg _), ofReal_norm]
  -- the step means
  have hle : ∑ j ∈ I, ∑ x, ‖∫ y, stepX b E s h τ m R W Vs x j y ∂μ‖ₑ ≤
      ∑ j ∈ I, ∑ x : SrcCol K (Fin np), (errT b E s h τ m R W Vs x j +
        if IsBirthStep τ W j then ‖(b3BirthAt b τ m W j).1 x x‖ₑ else 0) :=
    sum_le_sum fun j hj => sum_le_sum fun x _ =>
      enorm_integral_stepX_le hb1 hE1 hE2 (hAd j (mem_Ico.1 hj).1) x (hI j hj x)
  have hbirth : ∑ j ∈ I, ∑ x : SrcCol K (Fin np),
      (if IsBirthStep τ W j then ‖(b3BirthAt b τ m W j).1 x x‖ₑ else 0) ≤
        ENNReal.ofReal (birthC b m) := by
    calc ∑ j ∈ I, ∑ x : SrcCol K (Fin np),
          (if IsBirthStep τ W j then ‖(b3BirthAt b τ m W j).1 x x‖ₑ else 0)
        ≤ ∑ j ∈ I, ∑ x : SrcCol K (Fin np), ENNReal.ofReal ‖(b3BirthAt b τ m W j).1 x x‖ :=
          sum_le_sum fun j _ => sum_le_sum fun x _ => by
            split_ifs
            · exact le_of_eq (ofReal_norm _).symm
            · exact zero_le
      _ = ENNReal.ofReal (∑ j ∈ I, ∑ x : SrcCol K (Fin np), ‖(b3BirthAt b τ m W j).1 x x‖) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun j _ => sum_nonneg fun x _ => norm_nonneg _]
          simp_rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => norm_nonneg _)]
      _ ≤ ENNReal.ofReal (birthC b m) := ENNReal.ofReal_le_ofReal (sum_norm_birth_le b τ m W I)
  refine (add_le_add le_rfl hle).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (birthC_nonneg b m)]
  simp_rw [sum_add_distrib]
  rw [sum_comm (s := I) (t := (univ : Finset (SrcCol K (Fin np))))]
  calc ENNReal.ofReal (4 * K) + (∑ y : SrcCol K (Fin np), ∑ x ∈ I, errT b E s h τ m R W Vs y x +
        ∑ j ∈ I, ∑ x : SrcCol K (Fin np),
          (if IsBirthStep τ W j then ‖(b3BirthAt b τ m W j).1 x x‖ₑ else 0))
      ≤ ENNReal.ofReal (4 * K) + (∑ y : SrcCol K (Fin np), ∑ x ∈ I,
          errT b E s h τ m R W Vs y x + ENNReal.ofReal (birthC b m)) := by gcongr
    _ = _ := by ring

end BlockBand.SourceProcess.PhysApprox.B3.StopTail
