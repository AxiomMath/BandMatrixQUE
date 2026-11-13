module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.Pathwise
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Contract: a stopped continuous semimartingale

`stoppedSemimartingale_holds d : StoppedSemimartingale d` (contract of
`BlockBand.Internal.Contracts.Transmission`): on an arbitrary filtered probability space
(raw filtration, a.s. continuous paths), a continuous semimartingale stopped at a
`𝓖`-stopping time `ρ` is a continuous semimartingale with characteristics switched off after
`ρ`, with the same localizing sequence.

The martingale part uses `exists_martingale_stoppedProcess` (optional stopping for a.s.
continuous processes with a martingale modification); the compensated processes of the stopped
process are the original ones evaluated at `t ∧ ρ` (`smCompensated_stopped`).
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {Ω : Type*} {d : ℕ}

/-- A path that is integrable on every `(0, t]` (through `toNNReal`) is interval integrable
on every interval. -/
theorem intervalIntegrable_toNNReal_path {g : ℝ≥0 → ℝ}
    (hg : ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => g s.toNNReal) (Ioc 0 t)) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => g s.toNNReal) volume a b := by
  set R : ℝ≥0 := (|a| + |b|).toNNReal
  have hR : (R : ℝ) = |a| + |b| := Real.coe_toNNReal _ (by positivity)
  have h1 : IntegrableOn (fun s : ℝ => g s.toNNReal) (Ioc (-(R : ℝ)) 0) := by
    refine (integrableOn_const (C := g 0) (by simp)).congr_fun (fun s hs => ?_) measurableSet_Ioc
    simp [Real.toNNReal_of_nonpos hs.2]
  have h3 := h1.union (hg R)
  rw [Ioc_union_Ioc_eq_Ioc (by simp) (by positivity)] at h3
  rw [intervalIntegrable_iff]
  refine h3.mono_set ?_
  intro x hx
  rw [uIoc, mem_Ioc] at hx
  rw [mem_Ioc, hR]
  constructor
  · have := hx.1
    have : -(|a| + |b|) ≤ min a b := by
      rcases min_choice a b with h | h <;> rw [h] <;>
        linarith [neg_abs_le a, neg_abs_le b, abs_nonneg a, abs_nonneg b]
    linarith
  · have := hx.2
    have : max a b ≤ |a| + |b| := by
      rcases max_choice a b with h | h <;> rw [h] <;>
        linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]
    linarith

theorem continuous_setIntegral_Ioc {g : ℝ≥0 → ℝ}
    (hg : ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => g s.toNNReal) (Ioc 0 t)) :
    Continuous fun u : ℝ≥0 => ∫ s in Ioc (0 : ℝ) u, g s.toNNReal := by
  have := (intervalIntegral.continuous_primitive (intervalIntegrable_toNNReal_path hg) 0).comp
    NNReal.continuous_coe
  refine this.congr fun u => ?_
  simp only [Function.comp]
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg u)]

theorem continuous_smCompensated {Y β : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hY : Continuous fun t => Y t ω) {i : Fin d}
    (hβ : ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => β s.toNNReal ω i) (Ioc 0 t)) :
    Continuous fun u => smCompensated Y β i u ω :=
  (((continuous_apply i).comp hY).sub continuous_const).sub
    (continuous_setIntegral_Ioc (g := fun u => β u ω i) hβ)

theorem integrableOn_switchAfter_path {G : Type*} [Zero G] (ρ : Ω → WithTop ℝ≥0)
    (f : ℝ≥0 → Ω → G) (h : G → ℝ) (h0 : h 0 = 0) (ω : Ω) (t : ℝ≥0)
    (hi : IntegrableOn (fun s : ℝ => h (f s.toNNReal ω)) (Ioc 0 t)) :
    IntegrableOn (fun s : ℝ => h (switchAfter ρ f s.toNNReal ω)) (Ioc 0 t) := by
  classical
  have e : (fun s : ℝ => h (switchAfter ρ f s.toNNReal ω)) =
      {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ ρ ω}.indicator
        (fun s : ℝ => h (f s.toNNReal ω)) := by
    funext v
    by_cases hv : (v.toNNReal : WithTop ℝ≥0) ≤ ρ ω
    · rw [Set.indicator_of_mem (show v ∈ {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ ρ ω} from hv)]
      simp only [switchAfter]; split_ifs; rfl
    · rw [Set.indicator_of_notMem (show v ∉ {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ ρ ω}
        from hv)]
      simp only [switchAfter]; split_ifs; exact h0
  rw [e]
  exact hi.indicator (measurableSet_toNNReal_le _)

/-- **Contract (a2).** -/
theorem stoppedSemimartingale_holds (d : ℕ) : StoppedSemimartingale d := by
  intro Ω _ Q _ 𝓖 Y β α H ρ hρ
  obtain ⟨τ, hτ, hτlim, hmart⟩ := H.localizing
  refine ⟨fun t => H.progressive.stronglyAdapted_stoppedProcess hρ t,
    H.progressive.stoppedProcess hρ, ?_,
    isStronglyProgressive_switchAfter H.drift_progressive hρ,
    isStronglyProgressive_switchAfter H.cov_progressive hρ, ?_,
    ⟨τ, hτ, hτlim, fun n => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [H.continuous] with ω hω
    exact hω.comp (continuous_stopTime _)
  · filter_upwards [H.integrable] with ω hω t
    refine ⟨fun i => integrableOn_switchAfter_path ρ β (fun b : Fin d → ℝ => b i) rfl ω t
      ((hω t).1 i), fun i j => integrableOn_switchAfter_path ρ α
        (fun a : Matrix (Fin d) (Fin d) ℝ => a i j) rfl ω t ((hω t).2 i j)⟩
  · -- drift part
    obtain ⟨M, hM, hMX⟩ := (hmart n).1 i
    have hc : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess (smCompensated Y β i) (τ n) t ω := by
      filter_upwards [H.continuous, H.integrable] with ω hω hi
      exact (continuous_smCompensated hω fun t => (hi t).1 i).comp (continuous_stopTime _)
    obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM hMX hc hρ
    refine ⟨M', hM', fun t => (hM'X t).trans (ae_of_all _ fun ω => ?_)⟩
    simp only [stoppedProcess_eq_stopTime, smCompensated_stopped]
    rw [stopTime_comm]
  · -- bracket part
    obtain ⟨M, hM, hMX⟩ := (hmart n).2 i j
    have hc : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess (fun t ω =>
        smCompensated Y β i t ω * smCompensated Y β j t ω -
          ∫ s in Set.Ioc (0 : ℝ) t, α s.toNNReal ω i j) (τ n) t ω := by
      filter_upwards [H.continuous, H.integrable] with ω hω hi
      exact (((continuous_smCompensated hω fun t => (hi t).1 i).mul
        (continuous_smCompensated hω fun t => (hi t).1 j)).sub
        (continuous_setIntegral_Ioc (g := fun u => α u ω i j) fun t => (hi t).2 i j)).comp
        (continuous_stopTime _)
    obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM hMX hc hρ
    refine ⟨M', hM', fun t => (hM'X t).trans (ae_of_all _ fun ω => ?_)⟩
    simp only [stoppedProcess_eq_stopTime, smCompensated_stopped, integral_switchAfter_α]
    rw [stopTime_comm]

end BlockBand.SourceProcess.Stochastic.Semimartingale
