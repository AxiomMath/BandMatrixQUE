module

public import BlockBand.SourceProcess.Stochastic.ItoNative.Pair
public import BlockBand.SourceProcess.Stochastic.ItoNative.CoordRepBuild
public import BlockBand.SourceProcess.Stochastic.SDE.NativeTools

/-!
# Sums of Itô processes

The zero process and finite sums of Itô processes are Itô processes.
`isNativeItoProcess_zero`, `isNativeItoProcess_add` (from `IsNativeItoProcess.prod` and
`map_clm`) and `isNativeItoProcess_finsetSum`: drifts and diffusions add.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.Stochastic.Integral BlockBand.SourceProcess.Stochastic.ItoNative

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The zero process. -/
theorem isNativeItoProcess_zero :
    IsNativeItoProcess μ (fun (_ : ℝ≥0) (_ : DriverSample S κ) => (0 : E)) (fun _ _ => 0)
      (fun _ _ _ => 0) := by
  have hz : ∀ (ℓ : E →L[ℝ] ℝ) (τ : DriverSample S κ → WithTop ℝ≥0),
      stopIntegrand τ (functionalIntegrand ℓ (fun (_ : κ) (_ : ℝ≥0) (_ : DriverSample S κ) =>
        (0 : E))) = fun _ _ => 0 := by
    intro ℓ τ
    funext a p
    simp only [stopIntegrand, functionalIntegrand, map_zero]
    split_ifs <;> rfl
  refine ⟨fun t => stronglyMeasurable_const, fun t => stronglyMeasurable_const,
    ae_of_all _ fun x => continuous_const, fun t => stronglyMeasurable_const,
    fun a t => stronglyMeasurable_const, ae_of_all _ fun x t => integrableOn_zero,
    ⟨fun _ _ => ⊤, fun n => isStoppingTime_top, ae_of_all _ fun x => tendsto_const_nhds,
      fun n ℓ T => ?_⟩, ?_⟩
  · rw [hz]; exact nativeIntegrand_zero
  · intro ℓ τ hτ T _ t _
    have hs : NativeIntegrand μ T (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ x))
        (functionalIntegrand ℓ (fun (_ : κ) (_ : ℝ≥0) (_ : DriverSample S κ) => (0 : E)))) := by
      rw [hz]; exact nativeIntegrand_zero
    refine ⟨hs, ?_⟩
    have he : nativeIntegralOf hs = nativeIntegralOf (nativeIntegrand_zero (μ := μ) (T := T)) :=
      nativeIntegralOf_congr _ _ fun c => Eventually.of_forall fun p => by rw [hz]
    rw [he, nativeIntegralOf_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 (driverLaw (κ := κ) μ)] with x hx
    rw [hx]
    have h0 : stoppedDrift τ (fun (_ : ℝ≥0) (_ : DriverSample S κ) => (0 : E)) t x = 0 := by
      unfold stoppedDrift
      beta_reduce
      simp only [ite_self, integral_zero]
    rw [h0]
    simp

variable [FiniteDimensional ℝ E]

/-- **Sum of two Itô processes.** -/
theorem isNativeItoProcess_add
    {X bX Y bY : ℝ≥0 → DriverSample S κ → E} {σX σY : κ → ℝ≥0 → DriverSample S κ → E}
    (hX : IsNativeItoProcess μ X bX σX) (hY : IsNativeItoProcess μ Y bY σY) :
    IsNativeItoProcess μ (fun t x => X t x + Y t x) (fun t x => bX t x + bY t x)
      (fun a t x => σX a t x + σY a t x) :=
  (hX.prod hY).map_clm (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E)

/-- **Finite sums of Itô processes.** -/
theorem isNativeItoProcess_finsetSum {ι : Type*}
    (s : Finset ι) {X b : ι → ℝ≥0 → DriverSample S κ → E}
    {σ : ι → κ → ℝ≥0 → DriverSample S κ → E}
    (h : ∀ i ∈ s, IsNativeItoProcess μ (X i) (b i) (σ i)) :
    IsNativeItoProcess μ (fun t x => ∑ i ∈ s, X i t x) (fun t x => ∑ i ∈ s, b i t x)
      (fun a t x => ∑ i ∈ s, σ i a t x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isNativeItoProcess_zero
  | insert j s hj ih =>
    have h1 := isNativeItoProcess_add (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.sum_insert hj]
    exact h1

end BlockBand.SourceProcess.CoupledFrames
