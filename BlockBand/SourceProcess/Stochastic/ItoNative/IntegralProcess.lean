module
public import BlockBand.SourceProcess.Stochastic.ItoNative.CoordRepBuild
public import BlockBand.SourceProcess.Stochastic.SDE.NativeHorizon
public import BlockBand.SourceProcess.Stochastic.SDE.NativeTools
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The integral process as a coordinate representation

Sample space `DriverSample S κ`, law `P = driverLaw μ`, `ν_T = timeProbMeasure T P`.

Let `g` be an integrand on `(0, T₀]` vanishing at times `> T₀` and depending on time only
through `toNNReal`. Then (`exists_integralProcess`) there is a real process `W` such that:
* it is everywhere continuous, augmented adapted, `W_0 = 0`, and a.s. equal at all times
  to the continuous integral `X^g = nativeAdaptedLimit μ T₀ g` (modification on the
  null set where `X^g` is not continuous);
* it is a `CoordRep` in `ℝ¹` with drift `0` and diffusion `g` (localizer `⊤`), on every
  horizon `T ≥ T₀` (horizon extension `nativeIntegrand_extend`, `nativeAdaptedLimit_extend`);
* for every augmented stopping time `τ` and time `t`, `W_{t∧τ} = I_{T₀}(g 1{s ≤ t ∧ τ})` a.s.
-/

namespace BlockBand.SourceProcess.Stochastic.ItoNative
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.Internal.Contracts.Transmission

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T₀ T : ℝ≥0}

/-- A horizon-`T₀` integrand vanishing after `T₀` is an integrand on every larger
horizon. -/
theorem nativeIntegrand_extend (h : T₀ ≤ T) {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T₀ g) (hsupp : ∀ c p, (T₀ : ℝ) < p.1 → g c p = 0) :
    NativeIntegrand μ T g := by
  intro c
  have hwin : g c =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)]
      (NativeSDE.window S κ T₀).indicator (g c) := by
    filter_upwards [timeProbMeasure_horizon (κ := κ) μ T] with p hp
    by_cases hw : p ∈ NativeSDE.window S κ T₀
    · rw [Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw]
      refine hsupp c p ?_
      by_contra hle
      exact hw ⟨⟨hp.1, le_of_not_gt hle⟩, Set.mem_univ _⟩
  obtain ⟨g', hg'm, hgg'⟩ := (hg c).1
  refine ⟨⟨(NativeSDE.window S κ T₀).indicator g',
    hg'm.indicator (NativeSDE.measurableSet_window_pred T₀), ?_⟩, ?_⟩
  · filter_upwards [hwin, NativeSDE.ae_window_of_ae h hgg'] with p h1 h2
    rw [h1]
    by_cases hw : p ∈ NativeSDE.window S κ T₀
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, h2 hw]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
  · refine MemLp.ae_eq hwin.symm ?_
    rw [memLp_indicator_iff_restrict (NativeSDE.measurableSet_window T₀).nullMeasurableSet,
      NativeSDE.timeProbMeasure_restrict_window h]
    exact (hg c).2

/-- **Horizon extension of the continuous integral**: for an integrand vanishing after `T₀`,
the horizon-`T₀` and horizon-`T` processes agree a.s. at every time. -/
theorem nativeAdaptedLimit_extend (h : T₀ ≤ T) {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T₀ g) (hg' : NativeIntegrand μ T g)
    (hsupp : ∀ c p, (T₀ : ℝ) < p.1 → g c p = 0) (u : ℝ≥0) :
    nativeAdaptedLimit μ T₀ hg.family u =ᵐ[driverLaw (κ := κ) μ]
      nativeAdaptedLimit μ T hg'.family u := by
  by_cases hu : u ≤ T₀
  · exact NativeSDE.nativeAdaptedLimit_horizon h hg hg' hu
  push Not at hu
  rw [nativeAdaptedLimit_after_horizon μ T₀ hg.family hu.le]
  refine (NativeSDE.nativeAdaptedLimit_horizon h hg hg' le_rfl).trans ?_
  have htop := isStoppingTime_top_aug (κ := κ) (μ := μ)
  obtain ⟨hs1, h1⟩ := nativeAdaptedLimit_stopped hg' htop T₀
  obtain ⟨hs2, h2⟩ := nativeAdaptedLimit_stopped hg' htop u
  have hst (X : ℝ≥0 → DriverSample S κ → ℝ) (v : ℝ≥0) :
      stoppedProcess X (fun _ => ⊤) v = X v := by
    funext x
    exact stoppedProcess_eq_of_le le_top
  rw [hst] at h1 h2
  have e : stopIntegrand (fun _ => min (T₀ : WithTop ℝ≥0) ⊤) g =
      stopIntegrand (fun _ => min (u : WithTop ℝ≥0) ⊤) g := by
    funext c p
    simp only [stopIntegrand, min_top_right, WithTop.coe_le_coe]
    by_cases h0 : p.1.toNNReal ≤ T₀
    · rw [ite_eq_left h0, ite_eq_left (h0.trans hu.le)]
    · rw [ite_eq_right h0]
      have hlt : (T₀ : ℝ) < p.1 := by
        have h0' : T₀ < p.1.toNNReal := lt_of_not_ge h0
        exact (Real.lt_toNNReal_iff_coe_lt).1 h0'
      split_ifs <;> simp [hsupp c p hlt]
  rw [Bridges.nativeIntegralOf_congr e hs1 hs2] at h1
  exact h1.trans h2.symm

/-- **The integral process as a coordinate representation.** -/
theorem exists_integralProcess {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T₀ g) (hsupp : ∀ c p, (T₀ : ℝ) < p.1 → g c p = 0)
    (htoNN : ∀ c (p : ℝ × DriverSample S κ), g c ((p.1.toNNReal : ℝ), p.2) = g c p)
    (hprog : ∀ c, IsStronglyProgressive (driverAugmented (κ := κ) μ)
      (fun t x => g c ((t : ℝ), x))) :
    ∃ W : ℝ≥0 → DriverSample S κ → ℝ,
      CoordRep μ (fun t x (_ : Fin 1) => W t x) (fun _ _ _ => 0)
        (fun a t x (_ : Fin 1) => g a ((t : ℝ), x)) ∧
      (∀ x, W 0 x = 0) ∧
      ∀ τ : DriverSample S κ → WithTop ℝ≥0, IsStoppingTime (driverAugmented (κ := κ) μ) τ →
        ∀ t : ℝ≥0, ∃ hs : NativeIntegrand μ T₀
            (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ x)) g),
          stoppedProcess W τ t =ᵐ[driverLaw (κ := κ) μ]
            (nativeIntegralOf hs : DriverSample S κ → ℝ) := by
  set N := nativeAdaptedLimit μ T₀ hg.family with hNdef
  obtain ⟨G, hGm, hG0, hGc⟩ :=
    NativeSDE.exists_good_set μ (nativeAdaptedLimit_continuous_all_ae μ T₀ hg.family)
  set W : ℝ≥0 → DriverSample S κ → ℝ := fun t => G.indicator (N t) with hWdef
  have hWN : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, W t x = N t x := by
    have hmem : ∀ᵐ x ∂driverLaw (κ := κ) μ, x ∈ G := by
      rw [ae_iff]
      exact hG0
    filter_upwards [hmem] with x hx t
    exact Set.indicator_of_mem hx _
  have hWc : ∀ x, Continuous fun t => W t x := by
    intro x
    by_cases hx : x ∈ G
    · simpa only [hWdef, Set.indicator_of_mem hx] using hGc x hx
    · simpa only [hWdef, Set.indicator_of_notMem hx] using continuous_const
  have hWa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (W t) := fun t =>
    (((nativeAdaptedLimit_adapted μ T₀ hg.family t).mono
      (le_augmentedFiltration _ _ t) le_rfl).stronglyMeasurable).indicator
      (NativeSDE.measurableSet_aug_of_full μ hGm hG0 t)
  have hWp : IsStronglyProgressive (driverAugmented (κ := κ) μ) W :=
    StronglyAdapted.isStronglyProgressive_of_continuous hWa hWc
  have hW0 : ∀ x, W 0 x = 0 := fun x => by
    show G.indicator (N 0) x = 0
    rw [hNdef, nativeAdaptedLimit_initial]
    simp
  have hc1 : Continuous fun r : ℝ => (fun _ : Fin 1 => r) := continuous_pi fun _ => continuous_id
  refine ⟨W, ⟨fun t => hc1.comp_stronglyMeasurable (hWa t),
    fun t => hc1.comp_stronglyMeasurable (hWp t), ae_of_all _ fun x => hc1.comp (hWc x),
    isStronglyProgressive_const _ _, fun a t => hc1.comp_stronglyMeasurable (hprog a t),
    ae_of_all _ fun x t i => integrableOn_zero,
    ⟨fun _ _ => ⊤, fun _ => isStoppingTime_top_aug, ae_of_all _ fun _ => tendsto_const_nhds,
      fun n τ hτ i => ?_⟩⟩, hW0, fun τ hτ t => ?_⟩
  · have e1 : (fun x => min ((fun _ _ => (⊤ : WithTop ℝ≥0)) n x) (τ x)) = τ :=
      funext fun x => min_top_left _
    have e2 : functionalIntegrand (coordFun i) (fun a t x (_ : Fin 1) => g a ((t : ℝ), x)) = g :=
      funext fun a => funext fun p => htoNN a p
    have e3 : smCompensated (fun t x (_ : Fin 1) => W t x) (fun _ _ _ => 0) i = W := by
      funext t x
      simp [smCompensated, hW0]
    rw [e1, e2, e3]
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hgT := nativeIntegrand_extend hT hg hsupp
    have hgτ := stopIntegrand_nativeIntegrand hgT hτ
    have hgτ0 := stopIntegrand_nativeIntegrand hg hτ
    have hsupp' : ∀ c p, (T₀ : ℝ) < p.1 → stopIntegrand τ g c p = 0 := fun c p hp => by
      simp only [stopIntegrand, hsupp c p hp]
      split_ifs <;> rfl
    refine ⟨hgτ, fun u _ => ?_⟩
    exact (stoppedProcess_ae_eq_of_indistinguishable hWN τ u).trans
      ((nativeAdaptedLimit_stopIntegrand hg hτ hgτ0 u).symm.trans
        (nativeAdaptedLimit_extend hT hgτ0 hgτ hsupp' u))
  · obtain ⟨hs, h⟩ := nativeAdaptedLimit_stopped hg hτ t
    exact ⟨hs, (stoppedProcess_ae_eq_of_indistinguishable hWN τ t).trans h⟩

end BlockBand.SourceProcess.Stochastic.ItoNative
