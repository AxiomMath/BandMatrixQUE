module

public import BlockBand.SourceProcess.Stochastic.Bridges.Concat
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract

/-!
# Localized compensated martingales

`LocMart Q 𝓖 Z β`: the real process `Z` is progressively measurable with a.s. continuous paths,
its drift `β` has a.s. locally integrable paths, and the compensated process
`Z_t - Z_0 - ∫_0^t β` has `𝓖`-martingale modifications along a localizing sequence. This is
the drift part of `IsContinuousSemimartingale` (no bracket), which is all that the rank-free
coupling estimate uses. The class is closed under sums, scalar multiples,
constants, a.e. changes of the drift and stopping.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The compensated process `Z_t - Z_0 - ∫_0^t β_s ds`. -/
def locComp (Z β : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Z t ω - Z 0 ω - ∫ s in Ioc (0 : ℝ) t, β s.toNNReal ω

variable (Q 𝓖) in
/-- `Z` has drift `β` and a localized martingale compensated part. -/
structure LocMart (Z β : ℝ≥0 → Ω → ℝ) : Prop where
  prog : IsStronglyProgressive 𝓖 Z
  cont : ∀ᵐ ω ∂Q, Continuous fun t => Z t ω
  integ : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => β s.toNNReal ω) (Ioc 0 t)
  loc : ∃ τ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime 𝓖 (τ n)) ∧
    (∀ᵐ ω ∂Q, Tendsto (fun n => τ n ω) atTop (𝓝 ⊤)) ∧
    ∀ n, HasMartingaleModification Q 𝓖 (stoppedProcess (locComp Z β) (τ n))

variable {Z β : ℝ≥0 → Ω → ℝ}

theorem LocMart.cont_comp (h : LocMart Q 𝓖 Z β) :
    ∀ᵐ ω ∂Q, Continuous fun t => locComp Z β t ω := by
  filter_upwards [h.cont, h.integ] with ω h1 h2
  exact (h1.sub continuous_const).sub (continuous_setIntegral_Ioc (g := fun u => β u ω) h2)

/-- Martingale modifications of stopped processes transfer along a.s. equal paths. -/
theorem hmm_congr {F G : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0}
    (h : HasMartingaleModification Q 𝓖 (stoppedProcess G σ)) (hFG : ∀ᵐ ω ∂Q, ∀ t, F t ω = G t ω) :
    HasMartingaleModification Q 𝓖 (stoppedProcess F σ) := by
  obtain ⟨M, hM, hMG⟩ := h
  refine ⟨M, hM, fun t => ?_⟩
  filter_upwards [hMG t, hFG] with ω h1 h2
  rw [h1, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, h2]

/-- The scalar coordinate of a continuous semimartingale in `ℝ¹`. -/
theorem LocMart.of_sm {Y b : ℝ≥0 → Ω → Fin 1 → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ}
    (h : IsContinuousSemimartingale Q 𝓖 Y b α) :
    LocMart Q 𝓖 (fun t ω => Y t ω 0) (fun t ω => b t ω 0) := by
  obtain ⟨τ, hτ, hτlim, hm⟩ := h.localizing
  exact ⟨fun t => (continuous_apply 0).comp_stronglyMeasurable (h.progressive t),
    h.continuous.mono fun ω hω => (continuous_apply 0).comp hω,
    h.integrable.mono fun ω hω t => (hω t).1 0, τ, hτ, hτlim, fun n => (hm n).1 0⟩

variable [IsProbabilityMeasure Q]

theorem LocMart.add {Z' β' : ℝ≥0 → Ω → ℝ} (h₁ : LocMart Q 𝓖 Z β) (h₂ : LocMart Q 𝓖 Z' β') :
    LocMart Q 𝓖 (fun t ω => Z t ω + Z' t ω) (fun t ω => β t ω + β' t ω) := by
  obtain ⟨τ₁, hτ₁, hl₁, hm₁⟩ := h₁.loc
  obtain ⟨τ₂, hτ₂, hl₂, hm₂⟩ := h₂.loc
  refine ⟨h₁.prog.add h₂.prog, ?_, ?_, fun n ω => min (τ₁ n ω) (τ₂ n ω),
    fun n => (hτ₁ n).min (hτ₂ n), ?_, fun n => ?_⟩
  · filter_upwards [h₁.cont, h₂.cont] with ω a b
    exact a.add b
  · filter_upwards [h₁.integ, h₂.integ] with ω a b t
    exact (a t).add (b t)
  · filter_upwards [hl₁, hl₂] with ω a b
    exact tendsto_min_top a b
  · obtain ⟨M₁, hM₁, e₁⟩ := hasMartingaleModification_stopped_min (hm₁ n) h₁.cont_comp (hτ₂ n)
      (σ := fun ω => min (τ₁ n ω) (τ₂ n ω)) fun ω => min_comm _ _
    obtain ⟨M₂, hM₂, e₂⟩ := hasMartingaleModification_stopped_min (hm₂ n) h₂.cont_comp (hτ₁ n)
      (σ := fun ω => min (τ₁ n ω) (τ₂ n ω)) fun ω => rfl
    refine ⟨M₁ + M₂, hM₁.add hM₂, fun t => ?_⟩
    filter_upwards [e₁ t, e₂ t, h₁.integ, h₂.integ] with ω a b c d
    simp only [Pi.add_apply, a, b, stoppedProcess_eq_stopTime, locComp]
    rw [integral_add (c _) (d _)]
    ring

omit [IsProbabilityMeasure Q] in
theorem LocMart.const_mul (r : ℝ) (h : LocMart Q 𝓖 Z β) :
    LocMart Q 𝓖 (fun t ω => r * Z t ω) (fun t ω => r * β t ω) := by
  obtain ⟨τ, hτ, hl, hm⟩ := h.loc
  refine ⟨fun t => (h.prog t).const_mul r, ?_, ?_, τ, hτ, hl, fun n => ?_⟩
  · filter_upwards [h.cont] with ω a
    exact continuous_const.mul a
  · filter_upwards [h.integ] with ω a t
    exact (a t).const_mul r
  · obtain ⟨M, hM, e⟩ := hm n
    refine ⟨r • M, hM.smul r, fun t => ?_⟩
    filter_upwards [e t] with ω a
    simp only [Pi.smul_apply, smul_eq_mul, a, stoppedProcess_eq_stopTime, locComp]
    rw [integral_const_mul]
    ring

omit [IsProbabilityMeasure Q] in
/-- Changing the drift on a Lebesgue-null set of positive times. -/
theorem LocMart.congr_drift (h : LocMart Q 𝓖 Z β) {β' : ℝ≥0 → Ω → ℝ}
    (hβ : ∀ᵐ ω ∂Q, ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), β' s.toNNReal ω = β s.toNNReal ω) :
    LocMart Q 𝓖 Z β' := by
  obtain ⟨τ, hτ, hl, hm⟩ := h.loc
  have hsub : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) t)),
      β' s.toNNReal ω = β s.toNNReal ω := by
    filter_upwards [hβ] with ω hω t
    exact ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self hω
  refine ⟨h.prog, h.cont, ?_, τ, hτ, hl, fun n => hmm_congr (hm n) ?_⟩
  · filter_upwards [h.integ, hsub] with ω a b t
    exact (a t).congr_fun_ae ((b t).mono fun s hs => hs.symm)
  · filter_upwards [hsub] with ω a t
    simp only [locComp]
    rw [integral_congr_ae (a t)]

omit [IsProbabilityMeasure Q] in
/-- A time-constant `𝓖₀`-measurable process has drift `0`. -/
theorem LocMart.const {f : Ω → ℝ} (hf : StronglyMeasurable[𝓖 0] f) :
    LocMart Q 𝓖 (fun _ ω => f ω) (fun _ _ => 0) := by
  refine ⟨fun i => (hf.mono (𝓖.mono zero_le)).comp_measurable measurable_snd,
    ae_of_all _ fun _ => continuous_const, ae_of_all _ fun _ _ => integrableOn_zero,
    fun _ _ => ⊤, fun _ => isStoppingTime_top_const, ae_of_all _ fun _ => tendsto_const_nhds,
    fun n => ⟨0, martingale_zero ℝ 𝓖 Q, fun t => ae_of_all _ fun ω => ?_⟩⟩
  simp [locComp, stoppedProcess_eq_stopTime]

theorem LocMart.sum {ι : Type*} (s : Finset ι) {Z β : ι → ℝ≥0 → Ω → ℝ}
    (h : ∀ i ∈ s, LocMart Q 𝓖 (Z i) (β i)) :
    LocMart Q 𝓖 (fun t ω => ∑ i ∈ s, Z i t ω) (fun t ω => ∑ i ∈ s, β i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using LocMart.const (Q := Q) (𝓖 := 𝓖) (f := fun _ => (0 : ℝ)) stronglyMeasurable_const
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
theorem locComp_stopped (Z β : ℝ≥0 → Ω → ℝ) (ρ : Ω → WithTop ℝ≥0) :
    locComp (stoppedProcess Z ρ) (switchAfter ρ β) = stoppedProcess (locComp Z β) ρ := by
  funext u ω
  simp only [locComp, stoppedProcess_eq_stopTime, switchAfter]
  have h0 : stopTime (ρ ω) 0 = 0 := le_antisymm (stopTime_le _ 0) zero_le
  rw [h0]
  congr 1
  exact setIntegral_switch (fun v : ℝ => β v.toNNReal ω) (ρ ω) u

/-- **Stopping.** -/
theorem LocMart.stop (h : LocMart Q 𝓖 Z β) {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓖 ρ) :
    LocMart Q 𝓖 (stoppedProcess Z ρ) (switchAfter ρ β) := by
  obtain ⟨τ, hτ, hl, hm⟩ := h.loc
  refine ⟨h.prog.stoppedProcess hρ, ?_, ?_, τ, hτ, hl, fun n => ?_⟩
  · filter_upwards [h.cont] with ω hω
    exact hω.comp (continuous_stopTime (ρ ω))
  · filter_upwards [h.integ] with ω hω t
    exact integrableOn_switchAfter_path ρ β id rfl ω t (hω t)
  · rw [locComp_stopped, stoppedProcess_stoppedProcess']
    exact hasMartingaleModification_stopped_min (hm n) h.cont_comp hρ fun ω => min_comm _ _

end BlockBand.SourceProcess.RankFree
