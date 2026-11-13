module
public import BlockBand.SourceProcess.Stochastic.ItoNative.Core
public import BlockBand.SourceProcess.Stochastic.SDE.NativeExit
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Localizing the diffusion of `φ(t, X_t)`

Sample space `DriverSample S κ`, law `P = driverLaw μ`, `ν_T = timeProbMeasure T P`,
augmented filtration `G = F_t ∨ N`.

`IsNativeItoProcess.exists_localizer_comp`: let `X` be an Itô process in `E` with diffusion
`σ`, and `A : ℝ × E → (E →L F)` continuous. Then there are augmented stopping times
`τ'_n = τ_n ∧ e_n → ⊤` a.s. (`τ_n` the localizer of `X`, `e_n` the exit time from the ball
of radius `n` of the continuous modification of `X`) such that for every `n`, functional
`ℓ : F →L ℝ` and horizon `T`, `ℓ(A(s, X_s) σ_a(s)) 1{s ≤ τ'_n}` is an integrand on `(0, T]`.

Proof: in a basis `e : E ≃L ℝ^d`, `ℓ(A(q) v) = ∑_i (e v)_i ℓ(A(q) e⁻¹ e_i)`; the first factors are
continuous stopped composites of `(s, X_s)` (a.e. predictable), bounded a.e. on `{s ≤ e_n}` by
compactness of `[0, T] × B̄(0, n)`, and the second factors are integrands by the
localizing clause of `X`.
-/

namespace BlockBand.SourceProcess.Stochastic.ItoNative
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.Bridges

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Expansion of a linear functional in a basis given by `e : E ≃L ℝ^d`. -/
theorem clm_expand {d : ℕ} (e : E ≃L[ℝ] (Fin d → ℝ)) (M : E →L[ℝ] ℝ) (v : E) :
    M v = ∑ i, (e v) i * M (e.symm (Pi.single i 1)) := by
  have hv : e v = ∑ i, (e v) i • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [← e.symm_apply_apply v, hv]
  simp only [map_sum, map_smul, smul_eq_mul]

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- **Localizer for the diffusion `A(t, X_t) σ_a(t)`.** -/
theorem _root_.BlockBand.SourceProcess.Stochastic.IsNativeItoProcess.exists_localizer_comp {X b : ℝ≥0 → DriverSample S κ → E}
    {σ : κ → ℝ≥0 → DriverSample S κ → E} (h : IsNativeItoProcess μ X b σ)
    {A : ℝ × E → (E →L[ℝ] F)} (hA : Continuous A) :
    ∃ τ : ℕ → DriverSample S κ → WithTop ℝ≥0,
      (∀ n, IsStoppingTime (driverAugmented (κ := κ) μ) (τ n)) ∧
      (∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => τ n x) atTop (𝓝 ⊤)) ∧
      ∀ n (ℓ : F →L[ℝ] ℝ) (T : ℝ≥0), NativeIntegrand μ T (stopIntegrand (τ n)
        (functionalIntegrand ℓ (fun a t x => A ((t : ℝ), X t x) (σ a t x)))) := by
  classical
  obtain ⟨τ, hτs, hτlim, hloc⟩ := h.localizing
  obtain ⟨G, hGm, hG0, hGc⟩ := NativeSDE.exists_good_set μ h.continuous
  set Xg : ℝ≥0 → DriverSample S κ → E := fun t => G.indicator (X t) with hXgdef
  have hXga : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Xg t) := fun t =>
    (h.adapted t).indicator (NativeSDE.measurableSet_aug_of_full μ hGm hG0 t)
  have hXgc : ∀ x, Continuous fun t => Xg t x := by
    intro x
    by_cases hx : x ∈ G
    · simpa only [hXgdef, Set.indicator_of_mem hx] using hGc x hx
    · simpa only [hXgdef, Set.indicator_of_notMem hx] using continuous_const
  have hmem : ∀ᵐ x ∂driverLaw (κ := κ) μ, x ∈ G := by
    rw [ae_iff]
    exact hG0
  set ex : ℕ → DriverSample S κ → WithTop ℝ≥0 := fun n => NativeSDE.exitTimeOf Xg n
  have hex : ∀ n, IsStoppingTime (driverAugmented (κ := κ) μ) (ex n) := fun n =>
    NativeSDE.isStoppingTime_exitTimeOf hXga hXgc n
  refine ⟨fun n x => min (τ n x) (ex n x), fun n => (hτs n).min (hex n), ?_, ?_⟩
  · filter_upwards [hτlim] with x hx
    simpa using hx.min (NativeSDE.tendsto_exitTimeOf_top (hXgc x))
  intro n ℓ T
  set d := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  set ρ : DriverSample S κ → WithTop ℝ≥0 := fun x => min (τ n x) (ex n x) with hρdef
  have hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ := (hτs n).min (hex n)
  have hσi : ∀ i : Fin d, NativeIntegrand μ T
      (stopIntegrand ρ (functionalIntegrand ((coordFun i).comp (e : E →L[ℝ] (Fin d → ℝ))) σ)) := by
    intro i
    rw [hρdef, ← stopIntegrand_stopIntegrand]
    exact stopIntegrand_nativeIntegrand (hloc n _ T) (hex n)
  set c : Fin d → ℝ × E → ℝ := fun i q => ℓ (A q (e.symm (Pi.single i 1))) with hcdef
  have hc : ∀ i, Continuous (c i) := fun i =>
    ℓ.continuous.comp (hA.clm_apply continuous_const)
  set Y : ℝ≥0 → DriverSample S κ → ℝ × E := fun t x => ((t : ℝ), X t x) with hYdef
  have hYa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Y t) := fun t =>
    stronglyMeasurable_const.prodMk (h.adapted t)
  have hYc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Y t x := by
    filter_upwards [h.continuous] with x hx
    exact NNReal.continuous_coe.prodMk hx
  set K : Set (ℝ × E) := Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : E) n
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  choose C hC using fun i => hK.exists_bound_of_continuousOn (hc i).continuousOn
  have hexp : ∀ a, stopIntegrand ρ (functionalIntegrand ℓ
      (fun a t x => A ((t : ℝ), X t x) (σ a t x))) a = fun p => ∑ i,
        stoppedComposite ρ (c i) Y p * stopIntegrand ρ (functionalIntegrand
          ((coordFun i).comp (e : E →L[ℝ] (Fin d → ℝ))) σ) a p := by
    intro a
    funext p
    simp only [stopIntegrand, stoppedComposite, functionalIntegrand]
    split_ifs with hp
    · have hx := clm_expand e (ℓ.comp (A ((p.1.toNNReal : ℝ), X p.1.toNNReal p.2)))
        (σ a p.1.toNNReal p.2)
      simp only [ContinuousLinearMap.comp_apply] at hx
      rw [hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hcdef, hYdef, ContinuousLinearMap.comp_apply, coordFun,
        ContinuousLinearMap.proj_apply, ContinuousLinearEquiv.coe_coe]
      ring
    · simp
  intro a
  rw [hexp a]
  refine ⟨NativeSDE.aesm_finset_sum _ fun i _ =>
    (aestronglyMeasurable_stoppedComposite hYa hYc (hc i) hρ).mul (hσi i a).1, ?_⟩
  refine memLp_finsetSum _ fun i _ => ?_
  refine MemLp.of_le_mul (c := C i) (hσi i a).2
    (((aestronglyMeasurable_stoppedComposite hYa hYc (hc i) hρ).mul (hσi i a).1).mono
      (predictableSpace_le _)) ?_
  filter_upwards [timeProbMeasure_horizon (κ := κ) μ T, ae_timeProb_of_ae (T := T) hmem]
    with p hp hpG
  simp only [stopIntegrand, stoppedComposite, norm_mul]
  split_ifs with hle
  · refine mul_le_mul_of_nonneg_right (hC i _ ⟨⟨?_, ?_⟩, ?_⟩) (norm_nonneg _)
    · exact NNReal.coe_nonneg _
    · show ((p.1.toNNReal : ℝ≥0) : ℝ) ≤ T
      rw [Real.coe_toNNReal _ hp.1.le]
      exact hp.2
    · have hpos : 0 < p.1.toNNReal := Real.toNNReal_pos.2 hp.1
      have hb := NativeSDE.norm_le_of_le_exitTimeOf (hXgc p.2) hpos (hle.trans (min_le_right _ _))
      rw [mem_closedBall_zero_iff]
      simpa only [hXgdef, Set.indicator_of_mem hpG] using hb
  · simp

end BlockBand.SourceProcess.Stochastic.ItoNative
