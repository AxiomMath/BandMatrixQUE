module

public import BlockBand.SourceProcess.BornRestart.Lim
public import BlockBand.SourceProcess.BornStopped.Piece

/-!
# Restart of martingale clauses at a deterministic time

* `shiftFil 𝓖 a`: the filtration `𝓗_u = 𝓖_{a+u}` (no right limits, `a` deterministic);
  `martingale_shift`; `isStoppingTime_add`: `a + θ` is a `𝓖`-stopping time for an
  `𝓗`-stopping time `θ`.
* **`exists_restart`**: if `N` is a `𝓖`-martingale modification of `X^σ` (`X` a.s. continuous),
  `ρ ≤ σ` is a `𝓖`-stopping time and `a + θ ≤ ρ` on an event `E ∈ 𝓖_a`, then
  `1_E (X(a + u ∧ θ) - X(a))` has an `𝓗`-martingale modification.
* **`exists_martingale_of_ind`**: if `1_{E_k} V_u` has an `𝓗`-martingale modification for every
  `k`, a.s. eventually `ω ∈ E_k`, and every `V_u` is a.s. bounded, then `V` has one
  (dominated limit, `BornRestart.exists_martingale_of_tendsto`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.SourceProcess.BornRestart
open scoped NNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {Q : Measure Ω}

/-- The deterministic shift `𝓗_u = 𝓖_{a+u}`. -/
def shiftFil (𝓖 : Filtration ℝ≥0 m) (a : ℝ≥0) : Filtration ℝ≥0 m where
  seq u := 𝓖 (a + u)
  mono' _ _ h := 𝓖.mono (add_le_add le_rfl h)
  le' _ := 𝓖.le _

theorem shiftFil_apply (𝓖 : Filtration ℝ≥0 m) (a u : ℝ≥0) : shiftFil 𝓖 a u = 𝓖 (a + u) := rfl

theorem shiftFil_zero (𝓖 : Filtration ℝ≥0 m) (a : ℝ≥0) : shiftFil 𝓖 a 0 = 𝓖 a := by
  rw [shiftFil_apply, add_zero]

theorem martingale_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝓖 : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → E} (hN : Martingale N 𝓖 Q) (a : ℝ≥0) :
    Martingale (fun u => N (a + u)) (shiftFil 𝓖 a) Q :=
  ⟨fun u => hN.1 (a + u), fun s t hst => hN.2 (a + s) (a + t) (add_le_add le_rfl hst)⟩

theorem coe_add_le_iff {a t : ℝ≥0} (ht : a ≤ t) (θ : WithTop ℝ≥0) :
    (a : WithTop ℝ≥0) + θ ≤ t ↔ θ ≤ ((t - a : ℝ≥0) : WithTop ℝ≥0) := by
  induction θ with
  | top =>
    simp only [WithTop.add_top, top_le_iff]
    exact ⟨fun h => absurd h WithTop.coe_ne_top, fun h => absurd h WithTop.coe_ne_top⟩
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    exact (le_tsub_iff_left ht).symm

theorem isStoppingTime_add {𝓖 : Filtration ℝ≥0 m} {a : ℝ≥0} {θ : Ω → WithTop ℝ≥0}
    (hθ : IsStoppingTime (shiftFil 𝓖 a) θ) :
    IsStoppingTime 𝓖 fun ω => (a : WithTop ℝ≥0) + θ ω := by
  intro t
  by_cases ht : a ≤ t
  · have e : {ω | (a : WithTop ℝ≥0) + θ ω ≤ t} = {ω | θ ω ≤ ((t - a : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω; exact coe_add_le_iff ht (θ ω)
    rw [e]
    have h := hθ (t - a)
    rwa [shiftFil_apply, add_tsub_cancel_of_le ht] at h
  · have e : {ω | (a : WithTop ℝ≥0) + θ ω ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (not_le.1 ht)) le_self_add
    rw [e]; exact @MeasurableSet.empty _ (𝓖 t)

theorem stopTime_coe_add (a u : ℝ≥0) (θ : WithTop ℝ≥0) :
    stopTime ((a : WithTop ℝ≥0) + θ) (a + u) = a + stopTime θ u := by
  induction θ with
  | top => rw [WithTop.add_top, stopTime_top, stopTime_top]
  | coe x => rw [← WithTop.coe_add, stopTime_coe, stopTime_coe, min_add_add_left]

theorem stopTime_coe_add_zero (a : ℝ≥0) (θ : WithTop ℝ≥0) :
    stopTime ((a : WithTop ℝ≥0) + θ) a = a := by
  have h := stopTime_coe_add a 0 θ
  rwa [add_zero, show stopTime θ 0 = 0 from le_antisymm (stopTime_le θ 0) zero_le, add_zero] at h

theorem norm_indicator_one_le (E : Set Ω) (ω : Ω) :
    ‖E.indicator (fun _ => (1 : ℂ)) ω‖ ≤ 1 := by
  by_cases h : ω ∈ E <;> simp [h]

/-- **Restart and stop a martingale clause at a deterministic time.** -/
theorem exists_restart [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℂ}
    {σ : Ω → WithTop ℝ≥0} {N : ℝ≥0 → Ω → ℂ} (hN : Martingale N 𝓖 Q)
    (hNX : ∀ t, N t =ᵐ[Q] stoppedProcess X σ t) (hc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω)
    (a : ℝ≥0) {θ : Ω → WithTop ℝ≥0} (hθ : IsStoppingTime (shiftFil 𝓖 a) θ)
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓖 ρ) (hρσ : ∀ᵐ ω ∂Q, ρ ω ≤ σ ω) {E : Set Ω}
    (hE : MeasurableSet[𝓖 a] E) (hEρ : ∀ᵐ ω ∂Q, ω ∈ E → (a : WithTop ℝ≥0) + θ ω ≤ ρ ω) :
    ∃ N' : ℝ≥0 → Ω → ℂ, Martingale N' (shiftFil 𝓖 a) Q ∧ ∀ u, N' u =ᵐ[Q] fun ω =>
      E.indicator (fun _ => (1 : ℂ)) ω * (X (a + stopTime (θ ω) u) ω - X a ω) := by
  set ρ' : Ω → WithTop ℝ≥0 := fun ω => min ((a : WithTop ℝ≥0) + θ ω) (ρ ω)
  have hρ' : IsStoppingTime 𝓖 ρ' := (isStoppingTime_add hθ).min hρ
  obtain ⟨M, hM, hMX⟩ := exists_martingale_restrict_complex hN hNX hc hρ'
    (by filter_upwards [hρσ] with ω h using (min_le_right _ _).trans h)
    (Eventually.of_forall fun _ => rfl)
  have hS := martingale_shift hM a
  have hS0 := BornStopped.martingale_min hS 0
  have hE0 : MeasurableSet[shiftFil 𝓖 a 0] E := by rw [shiftFil_zero]; exact hE
  have hζ : StronglyMeasurable[shiftFil 𝓖 a 0] (E.indicator fun _ => (1 : ℂ)) :=
    stronglyMeasurable_const.indicator hE0
  refine ⟨fun u ω => E.indicator (fun _ => (1 : ℂ)) ω * (M (a + u) ω - M (a + min u 0) ω),
    martingale_const_mul (hS.sub hS0) hζ (Eventually.of_forall (norm_indicator_one_le E)),
    fun u => ?_⟩
  filter_upwards [hMX (a + u), hMX (a + min u 0), hEρ] with ω h1 h2 h3
  rw [h1, h2, min_eq_right (zero_le : (0 : ℝ≥0) ≤ u), add_zero, stoppedProcess_eq_stopTime,
    stoppedProcess_eq_stopTime]
  by_cases hω : ω ∈ E
  · have hρω : ρ' ω = (a : WithTop ℝ≥0) + θ ω := min_eq_left (h3 hω)
    rw [hρω, stopTime_coe_add, stopTime_coe_add_zero]
  · simp [hω]

/-- **Dominated limit of indicator-localized martingale clauses.** -/
theorem exists_martingale_of_ind [IsProbabilityMeasure Q] {𝓗 : Filtration ℝ≥0 m}
    {E : ℕ → Set Ω} {V : ℝ≥0 → Ω → ℂ}
    (hM : ∀ k, ∃ M : ℝ≥0 → Ω → ℂ, Martingale M 𝓗 Q ∧
      ∀ u, M u =ᵐ[Q] fun ω => (E k).indicator (fun _ => (1 : ℂ)) ω * V u ω)
    (hE : ∀ᵐ ω ∂Q, ∀ᶠ k in atTop, ω ∈ E k) (hbd : ∀ u, ∃ C, ∀ᵐ ω ∂Q, ‖V u ω‖ ≤ C) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓗 Q ∧ ∀ u, N u =ᵐ[Q] V u := by
  choose M hM hMV using hM
  refine exists_martingale_of_tendsto (Y := M)
    (fun u => @StronglyMeasurable.limUnder ℕ Ω ℂ (𝓗 u) _ _ atTop _ (fun k => M k u) _ _
      fun k => (hM k).1 u)
    (fun k u => (((hM k).1 u).mono (𝓗.le u)).aestronglyMeasurable)
    (fun u => ?_) (fun u => ?_) (fun k s t hst B hB => ((hM k).setIntegral_eq hst hB).symm)
  · filter_upwards [ae_all_iff.2 fun k => hMV k u, hE] with ω h hk
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hk] with k hk
    rw [h k, Set.indicator_of_mem hk, one_mul]
  · obtain ⟨C, hC⟩ := hbd u
    refine ⟨C, fun k => ?_⟩
    filter_upwards [hMV k u, hC] with ω h hC
    rw [h, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_indicator_one_le _ _)).trans hC

end BlockBand.SourceProcess.ComplexUnique
