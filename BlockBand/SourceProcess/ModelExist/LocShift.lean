module

public import BlockBand.SourceProcess.RankFree.LocMartShift

/-!
# Increments after a stopping time with an unbounded `𝓕_τ`-measurable weight

`LocMart.shift_unbdd`: `LocMart.shift` without the bound on the weight. The weight `ζ` is truncated
to `ζ 1{|ζ| ≤ n}`, and the localizing sequence of `Z` is combined with `ρ_n = ⊤` on `{|ζ| ≤ n}`,
`ρ_n = τ` otherwise (a stopping time, since `{|ζ| > n} ∈ 𝓕_τ`); before `τ` the increment vanishes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges (tendsto_min_top)
open BlockBand.SourceProcess.RankFree
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The weight truncated at level `n`. -/
def truncW (n : ℕ) (ζ : Ω → ℝ) : Ω → ℝ := fun ω => if |ζ ω| ≤ n then ζ ω else 0

/-- `⊤` where the weight is at most `n`, `τ` elsewhere. -/
def truncStop (n : ℕ) (ζ : Ω → ℝ) (τ : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω => if |ζ ω| ≤ n then ⊤ else τ ω

theorem isStoppingTime_truncStop {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) {ζ : Ω → ℝ}
    (hζ : StronglyMeasurable[hτ.measurableSpace] ζ) (n : ℕ) :
    IsStoppingTime 𝓖 (truncStop n ζ τ) := by
  intro t
  have hA : MeasurableSet[hτ.measurableSpace] {ω | ¬ |ζ ω| ≤ n} :=
    (measurableSet_le ((continuous_abs.measurable.comp hζ.measurable)) measurable_const).compl
  have e : {ω | truncStop n ζ τ ω ≤ t} = {ω | ¬ |ζ ω| ≤ n} ∩ {ω | τ ω ≤ t} := by
    ext ω
    simp only [truncStop, mem_ofPred_eq, mem_inter_iff]
    split_ifs with h
    · simp only [h, not_true_eq_false, false_and, iff_false, not_le]
      exact WithTop.coe_lt_top t
    · simp [h]
  rw [e]
  exact ((hτ.measurableSet _).1 hA).2 t

omit [MeasurableSpace Ω] in
theorem tendsto_truncStop (ζ : Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    Tendsto (fun n => truncStop n ζ τ ω) atTop (𝓝 ⊤) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |ζ ω|
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have h' : |ζ ω| ≤ n := hN.trans (by exact_mod_cast hn)
  simp only [truncStop, h', ↓reduceIte]

theorem stronglyMeasurable_truncW {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) {ζ : Ω → ℝ}
    (hζ : StronglyMeasurable[hτ.measurableSpace] ζ) (n : ℕ) :
    StronglyMeasurable[hτ.measurableSpace] (truncW n ζ) :=
  StronglyMeasurable.ite (measurableSet_le ((continuous_abs.measurable.comp hζ.measurable)) measurable_const) hζ
    stronglyMeasurable_const

omit [MeasurableSpace Ω] in
theorem norm_truncW_le (n : ℕ) (ζ : Ω → ℝ) (ω : Ω) : ‖truncW n ζ ω‖ ≤ n := by
  simp only [truncW]
  split_ifs with h
  · exact h
  · simp

omit [MeasurableSpace Ω] in
theorem stopTime_eq_self {τ : WithTop ℝ≥0} {t : ℝ≥0} (h : (t : WithTop ℝ≥0) ≤ τ) :
    stopTime τ t = t := by
  induction τ with
  | top => exact stopTime_top t
  | coe s => rw [stopTime_coe]; exact min_eq_left (WithTop.coe_le_coe.1 h)

theorem untopA_coe' (a : ℝ≥0) : (a : WithTop ℝ≥0).untopA = a := rfl

omit [MeasurableSpace Ω] in
theorem stopTime_le_self' (τ : WithTop ℝ≥0) (t : ℝ≥0) : (stopTime τ t : WithTop ℝ≥0) ≤ τ := by
  induction τ with
  | top => exact le_top
  | coe s₀ => rw [stopTime_coe]; exact WithTop.coe_le_coe.2 (min_le_right _ _)

variable [IsProbabilityMeasure Q]

variable {Z β : ℝ≥0 → Ω → ℝ}

/-- **Increments after `τ` with an `𝓕_τ`-measurable weight** (no bound on the weight). -/
theorem _root_.BlockBand.SourceProcess.RankFree.LocMart.shift_unbdd (h : LocMart Q 𝓖 Z β) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {ζ : Ω → ℝ} (hζ : StronglyMeasurable[hτ.measurableSpace] ζ) :
    LocMart Q 𝓖 (fun t ω => ζ ω * (Z t ω - stoppedProcess Z τ t ω))
      (fun s ω => if τ ω < (s : WithTop ℝ≥0) then ζ ω * β s ω else 0) := by
  obtain ⟨σ, hσ, hl, hm⟩ := h.loc
  refine ⟨fun i => ?_, ?_, ?_, fun n ω => min (σ n ω) (truncStop n ζ τ ω),
    fun n => (hσ n).min (isStoppingTime_truncStop hτ hζ n), ?_, fun n => ?_⟩
  · convert ((stronglyMeasurable_ite_le hτ hζ i).comp_measurable measurable_snd).mul
      ((h.prog i).sub ((h.prog.stoppedProcess hτ) i)) using 1
    funext p
    simp only [Pi.mul_apply, Function.comp_apply, Pi.sub_apply]
    split_ifs with hp
    · rfl
    · have hle : ((p.1 : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2 :=
        (WithTop.coe_le_coe.2 (mem_Iic.1 p.1.2)).trans (not_le.1 hp).le
      rw [stoppedProcess_eq_of_le hle]
      ring
  · filter_upwards [h.cont] with ω hω
    exact continuous_const.mul (hω.sub (hω.comp (continuous_stopTime (τ ω))))
  · filter_upwards [h.integ] with ω hω t
    have e : (fun s : ℝ => if τ ω < ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) then
        ζ ω * β s.toNNReal ω else 0) = {s : ℝ | τ ω < (s.toNNReal : WithTop ℝ≥0)}.indicator
          (fun s => ζ ω * β s.toNNReal ω) := by
      funext s; simp only [indicator_apply, mem_ofPred_eq]
    rw [e]
    exact ((hω t).const_mul (ζ ω)).indicator
      (measurableSet_lt measurable_const (WithTop.measurable_coe.comp measurable_real_toNNReal))
  · filter_upwards [hl] with ω hω
    exact tendsto_min_top hω (tendsto_truncStop ζ τ ω)
  · have hΦc : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess (locComp Z β) (σ n) t ω := by
      filter_upwards [h.cont_comp] with ω hω
      exact hω.comp (continuous_stopTime _)
    refine hmm_congr' (hmm_mul_sub_stopped (hm n) hΦc hτ (stronglyMeasurable_truncW hτ hζ n)
      (C := n) (ae_of_all _ fun ω => norm_truncW_le n ζ ω)) ?_
    filter_upwards [h.integ] with ω hω t
    have h0 : stopTime (τ ω) 0 = 0 := le_antisymm (stopTime_le _ 0) zero_le
    by_cases hζn : |ζ ω| ≤ n
    · have e : min (σ n ω) (truncStop n ζ τ ω) = σ n ω := by
        simp only [truncStop, hζn, ↓reduceIte, min_top_right]
      simp only [stoppedProcess_eq_stopTime, locComp, e, truncW, hζn, ↓reduceIte]
      rw [stopTime_comm (σ n ω) (τ ω) t, h0,
        setIntegral_ite_lt (τ ω) _ ((hω _).const_mul (ζ ω)), integral_const_mul,
        integral_const_mul]
      ring
    · have e : min (σ n ω) (truncStop n ζ τ ω) = min (σ n ω) (τ ω) := by
        simp only [truncStop, hζn, ↓reduceIte]
      simp only [stoppedProcess_eq_stopTime, locComp, e, truncW, hζn, ↓reduceIte, zero_mul]
      set u := stopTime (min (σ n ω) (τ ω)) t
      have hu : (u : WithTop ℝ≥0) ≤ τ ω :=
        (stopTime_le_self' _ t).trans (min_le_right _ _)
      have hzero : ∫ s in Ioc (0 : ℝ) u, (if τ ω < ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) then
          ζ ω * β s.toNNReal ω else 0) = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
        have hs' : (s.toNNReal : WithTop ℝ≥0) ≤ τ ω := by
          refine le_trans (WithTop.coe_le_coe.2 ?_) hu
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1.le]; exact hs.2
        simp only [not_lt.2 hs', ↓reduceIte]
      rw [hzero, stopTime_eq_self hu, h0]
      ring

end BlockBand.SourceProcess.ModelExist
