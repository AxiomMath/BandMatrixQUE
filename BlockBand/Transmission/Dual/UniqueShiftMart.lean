module

public import BlockBand.Transmission.Dual.UniqueLevel
public import BlockBand.Transmission.Dual.UniqueShiftPath
public import BlockBand.Transmission.Dual.LevelPath
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularOS
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorCond

/-!
# Uniqueness in law: the shift at the first deletion

* `isStoppingTime_untopA_add`, `shiftFil`: for a finite stopping time `τ`, the times `τ + s` are
  stopping times and `s ↦ 𝓖_{τ+s}` is a filtration.
* `martingale_shift`: for a martingale `M` that is continuous at every `ω` and bounded on
  bounded intervals, and `E ∈ 𝓖_τ` with `τ ≤ T`, `s ↦ 1_E (M_{τ+s} − M_τ)` is a martingale for
  `𝓖_{τ+·}` (optional sampling, `integral_mul_sub_stopped_eq_zero`).

These are used in the sibling module to prove `IsDualFrom.shift`: for `σ' = σ_{p−1} ∧ T`,
`E = {σ_{p−1} ≤ T}` and any `A ⊆ E` in `𝓖_{σ'}` with `P A ≠ 0`, the post-deletion path (shifted by
`σ'` and truncated on `E`, empty off `E`) is an `IsDualFrom` realization at level `p − 1` under
`P[|A]` for `𝓖_{σ'+·}`. Adaptedness comes from the front-padded `V`, which is adapted and continuous
at every `ω`, hence progressively measurable; no stopped value of a non-progressive process is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stopTime_coe
  stoppedProcess_eq_stopTime exists_martingale_stoppedProcess continuous_stopTime)
open BlockBand.SourceProcess.Stochastic.GramUniqueness (martingale_cond ae_cond_of_ae)
open scoped NNReal ENNReal

section Stop

variable {Ω : Type*} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}

theorem isStoppingTime_untopA_add {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hfin : ∀ ω, τ ω ≠ ⊤) (s : ℝ≥0) :
    IsStoppingTime 𝓖 (fun ω => (((τ ω).untopA + s : ℝ≥0) : WithTop ℝ≥0)) := by
  intro t
  by_cases hst : s ≤ t
  · have e : {ω | (((τ ω).untopA + s : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        {ω | τ ω ≤ ((t - s : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
      conv_rhs => rw [← coe_untopA_of_ne_top (hfin ω)]
      rw [WithTop.coe_le_coe, le_tsub_iff_right hst]
    rw [e]; exact (𝓖.mono (tsub_le_self : t - s ≤ t)) _ (hτ (t - s))
  · have e : {ω | (((τ ω).untopA + s : ℝ≥0) : WithTop ℝ≥0) ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (lt_of_not_ge hst) le_add_self
    rw [e]; exact @MeasurableSet.empty _ (𝓖 t)

/-- The filtration `s ↦ 𝓖_{τ+s}` for a finite stopping time `τ`. -/
def shiftFil {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (hfin : ∀ ω, τ ω ≠ ⊤) :
    Filtration ℝ≥0 m where
  seq s := (isStoppingTime_untopA_add hτ hfin s).measurableSpace
  mono' _ _ h := IsStoppingTime.measurableSpace_mono _ _ fun _ =>
    WithTop.coe_le_coe.2 ((add_le_add_iff_left _).2 h)
  le' s := (isStoppingTime_untopA_add hτ hfin s).measurableSpace_le

/-- **Optional sampling after a finite stopping time.** -/
theorem martingale_shift {P : Measure Ω} [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓖 P) (hc : ∀ ω, Continuous fun t => M t ω)
    (hb : ∀ K : ℝ≥0, ∃ C, ∀ t ≤ K, ∀ ω, |M t ω| ≤ C) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) (hfin : ∀ ω, τ ω ≠ ⊤) {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    {E : Set Ω} (hE : MeasurableSet[shiftFil hτ hfin 0] E) :
    Martingale (fun s => E.indicator fun ω => M ((τ ω).untopA + s) ω - M (τ ω).untopA ω)
      (shiftFil hτ hfin) P := by
  set ρ : Ω → ℝ≥0 := fun ω => (τ ω).untopA
  have hρT : ∀ ω, ρ ω ≤ T := fun ω => by
    have := hτT ω; rw [← coe_untopA_of_ne_top (hfin ω)] at this; exact_mod_cast this
  have hτs := isStoppingTime_untopA_add hτ hfin
  have hprog : IsStronglyProgressive 𝓖 M :=
    StronglyAdapted.isStronglyProgressive_of_continuous hM.1 hc
  have hMs : ∀ s, Measurable[shiftFil hτ hfin s] fun ω => M (ρ ω + s) ω := fun s =>
    measurable_stoppedValue hprog (hτs s)
  have hM0 : ∀ s, Measurable[shiftFil hτ hfin s] fun ω => M (ρ ω) ω := fun s => by
    have := hMs 0
    simp only [add_zero] at this
    exact this.mono ((shiftFil hτ hfin).mono zero_le) le_rfl
  have hEs : ∀ s, MeasurableSet[shiftFil hτ hfin s] E := fun s =>
    (shiftFil hτ hfin).mono zero_le _ hE
  set G : ℝ≥0 → Ω → ℝ := fun s => E.indicator fun ω => M (ρ ω + s) ω - M (ρ ω) ω
  have hGm : ∀ s, StronglyMeasurable[shiftFil hτ hfin s] (G s) := fun s =>
    (((hMs s).sub (hM0 s)).stronglyMeasurable).indicator (hEs s)
  have hGi : ∀ s, Integrable (G s) P := fun s => by
    obtain ⟨C, hC⟩ := hb (T + s)
    refine Integrable.of_bound ((hGm s).mono ((shiftFil hτ hfin).le s)).aestronglyMeasurable
      (C + C) (Eventually.of_forall fun ω => ?_)
    simp only [G, Real.norm_eq_abs]
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      exact (abs_sub _ _).trans (add_le_add (hC _ ((add_le_add_iff_right s).2 (hρT ω)) ω)
        (hC _ ((hρT ω).trans le_self_add) ω))
    · rw [indicator_of_notMem hω, abs_zero]
      exact (abs_nonneg _).trans ((hC 0 zero_le ω).trans (le_add_of_nonneg_left
        ((abs_nonneg _).trans (hC 0 zero_le ω))))
  refine ⟨fun s => hGm s, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((shiftFil hτ hfin).le s) (hGi t)
    (fun B _ _ => (hGi s).integrableOn) (fun B hB _ => ?_) (hGm s).aestronglyMeasurable).symm
  -- optional sampling for `M` stopped at `τ + t`, between `τ + s` and a large deterministic time
  have hcont : ∀ᵐ ω ∂P, Continuous fun u => stoppedProcess M (fun ω =>
      (((τ ω).untopA + t : ℝ≥0) : WithTop ℝ≥0)) u ω := Eventually.of_forall fun ω => by
    simp only [stoppedProcess_eq_stopTime]
    exact (hc ω).comp (continuous_stopTime _)
  obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM (fun _ => ae_eq_refl _)
    (Eventually.of_forall hc) (hτs t)
  have hB' : MeasurableSet[(hτs s).measurableSpace] (B ∩ E) := hB.inter (hEs s)
  have hζ : StronglyMeasurable[(hτs s).measurableSpace] ((B ∩ E).indicator fun _ => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hB'
  have hzero := BlockBand.SourceProcess.Stochastic.Dyson.Angular.integral_mul_sub_stopped_eq_zero
    ⟨M', hM', hM'X⟩ hcont (hτs s) hζ (C := 1)
    (Eventually.of_forall fun ω => by
      by_cases h : ω ∈ B ∩ E <;> simp [indicator, h]) (T + t)
  have hpt : ∀ ω, (B ∩ E).indicator (fun _ => (1 : ℝ)) ω *
      (stoppedProcess M (fun ω => (((τ ω).untopA + t : ℝ≥0) : WithTop ℝ≥0)) (T + t) ω -
        stoppedProcess (stoppedProcess M (fun ω => (((τ ω).untopA + t : ℝ≥0) : WithTop ℝ≥0)))
          (fun ω => (((τ ω).untopA + s : ℝ≥0) : WithTop ℝ≥0)) (T + t) ω) =
      B.indicator (fun ω => G t ω - G s ω) ω := fun ω => by
    simp only [stoppedProcess_eq_stopTime, stopTime_coe]
    have h1 : min (T + t) (ρ ω + t) = ρ ω + t := min_eq_right ((add_le_add_iff_right t).2 (hρT ω))
    have h2 : min (T + t) (ρ ω + s) = ρ ω + s :=
      min_eq_right (((add_le_add_iff_right s).2 (hρT ω)).trans ((add_le_add_iff_left T).2 hst))
    have h3 : min (ρ ω + s) (ρ ω + t) = ρ ω + s := min_eq_left ((add_le_add_iff_left _).2 hst)
    simp only [ρ] at h1 h2 h3
    rw [h1, h2, h3]
    by_cases hb : ω ∈ B <;> by_cases he : ω ∈ E <;> simp [G, hb, he, ρ]
  symm
  rw [← sub_eq_zero, ← integral_sub (hGi t).integrableOn (hGi s).integrableOn,
    ← integral_indicator ((hτs s).measurableSpace_le _ hB)]
  rw [← hzero]
  exact integral_congr_ae (Eventually.of_forall fun ω => (hpt ω).symm)

end Stop

end BlockBand.Transmission.Dual
