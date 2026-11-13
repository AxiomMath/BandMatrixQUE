module

public import BlockBand.Internal.Contracts.Transmission
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Martingale modifications: closure properties and removal of localization

* `hasMM_congr`, `hasMM_add`, `hasMM_sub`, `hasMM_const_mul`: modifications are stable under
  a.e. equality at each time and linear combinations;
* `hasMM_of_tendsto`: if `Z_m` have martingale modifications, `Z_m(t) → X(t)` a.s. for every `t`,
  and `|Z_m(t)| ≤ C_t` a.s. uniformly in `m`, then `X` has a martingale modification
  (dominated convergence in the set-integral form of the martingale property; used to remove the
  localizing sequence produced by the Itô formula `SemimartingaleItoFormula` on a bounded stopped
  process).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BlockBand.Internal.Contracts.Transmission

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem hasMM_congr {X Y : ℝ≥0 → Ω → ℝ} (h : HasMartingaleModification Q 𝓖 X)
    (hXY : ∀ t, X t =ᵐ[Q] Y t) : HasMartingaleModification Q 𝓖 Y := by
  obtain ⟨M, hM, he⟩ := h
  exact ⟨M, hM, fun t => (he t).trans (hXY t)⟩

theorem hasMM_add {X Y : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X)
    (hY : HasMartingaleModification Q 𝓖 Y) :
    HasMartingaleModification Q 𝓖 (fun t ω => X t ω + Y t ω) := by
  obtain ⟨M, hM, he⟩ := hX
  obtain ⟨M', hM', he'⟩ := hY
  exact ⟨M + M', hM.add hM', fun t => (he t).add (he' t)⟩

theorem hasMM_sub {X Y : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X)
    (hY : HasMartingaleModification Q 𝓖 Y) :
    HasMartingaleModification Q 𝓖 (fun t ω => X t ω - Y t ω) := by
  obtain ⟨M, hM, he⟩ := hX
  obtain ⟨M', hM', he'⟩ := hY
  exact ⟨M - M', hM.sub hM', fun t => (he t).sub (he' t)⟩

theorem hasMM_const_mul (c : ℝ) {X : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X) :
    HasMartingaleModification Q 𝓖 (fun t ω => c * X t ω) := by
  obtain ⟨M, hM, he⟩ := hX
  refine ⟨c • M, hM.smul c, fun t => ?_⟩
  filter_upwards [he t] with ω hω
  simp [hω]

/-- A.e. limits of `m`-strongly measurable real functions are `m`-a.e.-strongly measurable. -/
theorem aestronglyMeasurable_of_tendsto_ae_le {m : MeasurableSpace Ω} {f : ℕ → Ω → ℝ}
    {g : Ω → ℝ} (hf : ∀ n, StronglyMeasurable[m] (f n))
    (lim : ∀ᵐ ω ∂Q, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    AEStronglyMeasurable[m] g Q := by
  refine ⟨fun ω => limUnder atTop (fun n => f n ω),
    @StronglyMeasurable.limUnder ℕ Ω ℝ m _ _ atTop _ _ _ _ hf, ?_⟩
  filter_upwards [lim] with ω hω
  exact hω.limUnder_eq.symm

/-- **Removal of localization by dominated convergence.** -/
theorem hasMM_of_tendsto [IsProbabilityMeasure Q] {Z : ℕ → ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hZ : ∀ m, HasMartingaleModification Q 𝓖 (Z m))
    (hlim : ∀ t, ∀ᵐ ω ∂Q, Tendsto (fun m => Z m t ω) atTop (𝓝 (X t ω)))
    (hdom : ∀ t, ∃ C, ∀ m, ∀ᵐ ω ∂Q, |Z m t ω| ≤ C) :
    HasMartingaleModification Q 𝓖 X := by
  choose M hM hMe using hZ
  have hlimM : ∀ t, ∀ᵐ ω ∂Q, Tendsto (fun m => M m t ω) atTop (𝓝 (X t ω)) := fun t => by
    filter_upwards [hlim t, ae_all_iff.mpr fun m => hMe m t] with ω h1 h2
    simpa [h2] using h1
  have hdomM : ∀ t, ∃ C, ∀ m, ∀ᵐ ω ∂Q, ‖M m t ω‖ ≤ C := fun t => by
    obtain ⟨C, hC⟩ := hdom t
    refine ⟨C, fun m => ?_⟩
    filter_upwards [hC m, hMe m t] with ω h1 h2
    rw [Real.norm_eq_abs, h2]; exact h1
  -- measurability and integrability of the limit
  have hXm : ∀ t, AEStronglyMeasurable[𝓖 t] (X t) Q := fun t =>
    aestronglyMeasurable_of_tendsto_ae_le (fun m => (hM m).stronglyMeasurable t) (hlimM t)
  have hXm' : ∀ t, AEStronglyMeasurable (X t) Q := fun t => (hXm t).mono (𝓖.le t)
  have hXi : ∀ t, Integrable (X t) Q := fun t => by
    obtain ⟨C, hC⟩ := hdomM t
    refine Integrable.of_bound (hXm' t) C ?_
    filter_upwards [hlimM t, ae_all_iff.mpr hC] with ω h1 h2
    exact le_of_tendsto (h1.norm) (Eventually.of_forall h2)
  -- set integrals pass to the limit
  have hset : ∀ t (A : Set Ω), MeasurableSet A →
      Tendsto (fun m => ∫ ω in A, M m t ω ∂Q) atTop (𝓝 (∫ ω in A, X t ω ∂Q)) := by
    intro t A _
    obtain ⟨C, hC⟩ := hdomM t
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun m => ((hM m).integrable t).aestronglyMeasurable.restrict) (integrable_const C)
      (fun m => ae_restrict_of_ae (hC m)) (ae_restrict_of_ae (hlimM t))
  have hmart : ∀ u t, u ≤ t → X u =ᵐ[Q] Q[X t | 𝓖 u] := by
    intro u t hut
    refine ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le u) (hXi t)
      (fun A _ _ => (hXi u).integrableOn) (fun A hA _ => ?_) (hXm u)
    have h1 := hset u A (𝓖.le u A hA)
    have h2 := hset t A (𝓖.le u A hA)
    have heq : ∀ m, ∫ ω in A, M m u ω ∂Q = ∫ ω in A, M m t ω ∂Q := fun m =>
      (hM m).setIntegral_eq hut hA
    simp_rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  refine ⟨fun t => Q[X t | 𝓖 t], ⟨fun t => stronglyMeasurable_condExp, fun u t hut => ?_⟩,
    fun t => (condExp_of_aestronglyMeasurable' (𝓖.le t) (hXm t) (hXi t))⟩
  calc Q[Q[X t | 𝓖 t] | 𝓖 u] =ᵐ[Q] Q[X t | 𝓖 u] := condExp_condExp_of_le (𝓖.mono hut) (𝓖.le t)
    _ =ᵐ[Q] X u := (hmart u t hut).symm
    _ =ᵐ[Q] Q[X u | 𝓖 u] := (condExp_of_aestronglyMeasurable' (𝓖.le u) (hXm u) (hXi u)).symm

end BlockBand.SourceProcess.Stochastic.Dyson
