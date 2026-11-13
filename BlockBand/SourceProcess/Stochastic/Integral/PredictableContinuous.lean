module
public import BlockBand.SourceProcess.Stochastic.Integral.PredictableSampling
public import BlockBand.SourceProcess.Stochastic.Ito
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Predictability of stopped continuous-path integrands

Sample space `Ω = DriverSample S κ` with `P = driverLaw μ`; integrand space `L²(ν)`,
`ν = timeProbMeasure T P` (`dt ⊗ P` on `(0,T]`); raw predictable σ-algebra; augmented
filtration `F_t ∨ N` for adaptedness and stopping times. Time is read as `s.toNNReal`.

Let `Y : ℝ≥0 → Ω → E` (any topological space `E`) be `F_t ∨ N`-adapted with a.s. continuous
paths, `φ : E → ℝ` continuous and `τ` an augmented stopping time. Then
`stoppedComposite τ φ Y (s,x) = φ(Y_s x) 1{s ≤ τ x}` is a.e. raw predictable on `ν`
(`aestronglyMeasurable_stoppedComposite`; no integrability needed). Consequently, with
κ-indexed `φ_a`, `Y_a`, the family `stopIntegrand τ (fun a p => φ_a (Y_a p))` is a native
integrand as soon as each coordinate is in `L²(ν)` (`nativeIntegrand_stoppedComposite`) or
bounded (`nativeIntegrand_stoppedComposite_of_bound`); `nativeIntegrand_functionalIntegrand`
is the instance used by `IsNativeItoProcess`.

Route: `V_t = φ(Y_t) 1{t < τ}` is `F_t ∨ N`-measurable and `V_{u_n} → φ(Y_s) 1{s ≤ τ}` along
every `u_n ↑ s` strictly from below (path continuity), so `aestronglyMeasurable_of_leftLimit`
(left-endpoint dyadic sampling, augmented → raw up to null sets, a.e. limits) applies.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}
variable {E : Type*} [TopologicalSpace E]

/-- The stopped composite `(s,x) ↦ φ(Y_s x) 1{s ≤ τ x}`. -/
def stoppedComposite (τ : DriverSample S κ → WithTop ℝ≥0) (φ : E → ℝ)
    (Y : ℝ≥0 → DriverSample S κ → E) (p : ℝ × DriverSample S κ) : ℝ :=
  if ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2 then φ (Y p.1.toNNReal p.2) else 0

omit [MeasurableSpace S] [Fintype κ] [TopologicalSpace E] in
theorem stopIntegrand_composite (τ : DriverSample S κ → WithTop ℝ≥0) (φ : κ → E → ℝ)
    (Y : κ → ℝ≥0 → DriverSample S κ → E) (c : κ) :
    stopIntegrand τ (fun a p => φ a (Y a p.1.toNNReal p.2)) c = stoppedComposite τ (φ c) (Y c) :=
  rfl

/-- A continuous function of an augmented-adapted a.s. continuous process,
stopped at an augmented stopping time, is a.e. raw predictable on `dt ⊗ P` over `(0,T]`. -/
theorem aestronglyMeasurable_stoppedComposite {Y : ℝ≥0 → DriverSample S κ → E}
    (hY : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Y t))
    (hYc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Y t x) {φ : E → ℝ}
    (hφ : Continuous φ) {τ : DriverSample S κ → WithTop ℝ≥0}
    (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ) :
    AEStronglyMeasurable[rawPredictable S κ] (stoppedComposite τ φ Y)
      (timeProbMeasure T (driverLaw (κ := κ) μ)) := by
  classical
  let V : ℝ≥0 → DriverSample S κ → ℝ := fun t =>
    {x | (t : WithTop ℝ≥0) < τ x}.indicator (fun x => φ (Y t x))
  have hV (t : ℝ≥0) : StronglyMeasurable[driverAugmented (κ := κ) μ t] (V t) := by
    have hset : {x | (t : WithTop ℝ≥0) < τ x} = {x | τ x ≤ t}ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    refine (hφ.comp_stronglyMeasurable (hY t)).indicator ?_
    rw [hset]
    exact (hτ t).compl
  refine aestronglyMeasurable_of_leftLimit μ hV ?_
  filter_upwards [ae_timeProb_of_ae (T := T) hYc] with p hp
  intro u hu hlim
  have hpos : 0 < p.1 := (NNReal.coe_nonneg _).trans_lt (hu 0)
  set s : ℝ≥0 := p.1.toNNReal with hsdef
  have hs : (s : ℝ) = p.1 := Real.coe_toNNReal _ hpos.le
  have hlim' : Tendsto u atTop (𝓝 s) := by
    rw [← NNReal.tendsto_coe, hs]
    exact hlim
  have hus (n : ℕ) : u n < s := by
    have h := hu n
    rw [← hs] at h
    exact_mod_cast h
  by_cases hsτ : (s : WithTop ℝ≥0) ≤ τ p.2
  · have hG : stoppedComposite τ φ Y p = φ (Y s p.2) := by
      simp only [stoppedComposite, ← hsdef, hsτ, ite_true]
    rw [hG]
    have hV' (n : ℕ) : V (u n) p.2 = φ (Y (u n) p.2) := by
      have hlt : ((u n : ℝ≥0) : WithTop ℝ≥0) < τ p.2 :=
        lt_of_lt_of_le (WithTop.coe_lt_coe.2 (hus n)) hsτ
      exact Set.indicator_of_mem (show p.2 ∈ {x | ((u n : ℝ≥0) : WithTop ℝ≥0) < τ x} from hlt) _
    simp only [hV']
    exact (hφ.tendsto _).comp ((hp.tendsto s).comp hlim')
  · have hG : stoppedComposite τ φ Y p = 0 := by
      simp only [stoppedComposite, ← hsdef, hsτ, ite_false]
    rw [hG]
    have hlt : τ p.2 < (s : WithTop ℝ≥0) := lt_of_not_ge hsτ
    obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    rw [← hσ, WithTop.coe_lt_coe] at hlt
    apply tendsto_const_nhds.congr'
    filter_upwards [hlim'.eventually (lt_mem_nhds hlt)] with n hn
    have hnot : p.2 ∉ {x | ((u n : ℝ≥0) : WithTop ℝ≥0) < τ x} := by
      simp only [Set.mem_ofPred_eq, ← hσ, WithTop.coe_lt_coe, not_lt]
      exact hn.le
    exact (Set.indicator_of_notMem hnot _).symm

/-- κ-indexed stopped composites with `L²(ν)` coordinates form an integrand. -/
theorem nativeIntegrand_stoppedComposite {Y : κ → ℝ≥0 → DriverSample S κ → E}
    (hY : ∀ c t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Y c t))
    (hYc : ∀ c, ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Y c t x) {φ : κ → E → ℝ}
    (hφ : ∀ c, Continuous (φ c)) {τ : DriverSample S κ → WithTop ℝ≥0}
    (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    (hL2 : ∀ c, MemLp (stoppedComposite τ (φ c) (Y c)) 2
      (timeProbMeasure T (driverLaw (κ := κ) μ))) :
    NativeIntegrand μ T (stopIntegrand τ (fun a p => φ a (Y a p.1.toNNReal p.2))) := fun c =>
  ⟨aestronglyMeasurable_stoppedComposite (hY c) (hYc c) (hφ c) hτ, hL2 c⟩

/-- κ-indexed bounded stopped composites form an integrand. -/
theorem nativeIntegrand_stoppedComposite_of_bound {Y : κ → ℝ≥0 → DriverSample S κ → E}
    (hY : ∀ c t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Y c t))
    (hYc : ∀ c, ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Y c t x) {φ : κ → E → ℝ}
    (hφ : ∀ c, Continuous (φ c)) {τ : DriverSample S κ → WithTop ℝ≥0}
    (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ) {C : ℝ}
    (hC : ∀ c p, |stoppedComposite τ (φ c) (Y c) p| ≤ C) :
    NativeIntegrand μ T (stopIntegrand τ (fun a p => φ a (Y a p.1.toNNReal p.2))) :=
  nativeIntegrand_stoppedComposite hY hYc hφ hτ fun c =>
    MemLp.of_bound ((aestronglyMeasurable_stoppedComposite (T := T) (hY c) (hYc c) (hφ c)
      hτ).mono (predictableSpace_le _)) C (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        exact hC c p)

/-- The stopped diffusion functional `ℓ ∘ σ · 1{s ≤ τ}` of `IsNativeItoProcess` is a native
integrand when each `σ_a` is augmented-adapted with a.s. continuous paths and the stopped
functional is bounded. -/
theorem nativeIntegrand_functionalIntegrand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {σ : κ → ℝ≥0 → DriverSample S κ → F}
    (hσ : ∀ c t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (σ c t))
    (hσc : ∀ c, ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => σ c t x) (ℓ : F →L[ℝ] ℝ)
    {τ : DriverSample S κ → WithTop ℝ≥0}
    (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ) {C : ℝ}
    (hC : ∀ c p, |stoppedComposite τ ℓ (σ c) p| ≤ C) :
    NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand ℓ σ)) :=
  nativeIntegrand_stoppedComposite_of_bound (φ := fun _ => ℓ) hσ hσc (fun _ => ℓ.continuous)
    hτ hC

end BlockBand.SourceProcess.Stochastic.Integral
