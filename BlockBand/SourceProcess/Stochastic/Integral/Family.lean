module
public import BlockBand.SourceProcess.Stochastic.Integral.Increment
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Augmented events, stopped integrands and integrands from families

* `exists_raw_ae_eq`: an event of the augmented filtration `F_t ∨ N` differs from a raw
  `F_t` event by a `driverLaw μ`-null set.
* `stopFn ρ g`: the integrand `g · 1{s ≤ ρ}` for a finite random time `ρ`; it is
  `stopIntegrand` for `ρ` coerced to `WithTop ℝ≥0`.
* `nativeIntegrand_of_family`: a family `G` a.e. equal (coordinatewise, for
  `dt ⊗ driverLaw μ`) to the representatives of an element `F` of `PredictableFamily T`
  is an integrand with `family = F`.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem good_of_generateMeasurable (t : ℝ≥0) {C : Set (Set (DriverSample S κ))}
    (hC : ∀ s ∈ C, ∃ B, MeasurableSet[commonWienerFiltration S κ t] B ∧
      s =ᵐ[driverLaw (κ := κ) μ] B)
    {s : Set (DriverSample S κ)} (hs : MeasurableSpace.GenerateMeasurable C s) :
    ∃ B, MeasurableSet[commonWienerFiltration S κ t] B ∧ s =ᵐ[driverLaw (κ := κ) μ] B := by
  induction hs with
  | basic s h => exact hC s h
  | empty => exact ⟨∅, @MeasurableSet.empty _ (commonWienerFiltration S κ t), EventuallyEq.rfl⟩
  | compl s _ ih =>
    obtain ⟨B, hB, h⟩ := ih
    exact ⟨Bᶜ, hB.compl, EventuallyEqSet.compl h⟩
  | iUnion f _ ih =>
    choose B hB h using ih
    exact ⟨⋃ i, B i, MeasurableSet.iUnion hB, EventuallyEqSet.countable_iUnion h⟩

omit [IsProbabilityMeasure μ] in
/-- Augmented events are raw events up to `driverLaw μ`-null sets. -/
theorem exists_raw_ae_eq {t : ℝ≥0} {A : Set (DriverSample S κ)}
    (hA : MeasurableSet[driverAugmented (κ := κ) μ t] A) :
    ∃ B, MeasurableSet[commonWienerFiltration S κ t] B ∧ A =ᵐ[driverLaw (κ := κ) μ] B := by
  refine good_of_generateMeasurable μ t ?_ hA
  rintro s (hs | hs)
  · exact ⟨s, hs, EventuallyEq.rfl⟩
  · refine good_of_generateMeasurable μ t ?_ hs
    rintro N ⟨_, hN⟩
    exact ⟨∅, @MeasurableSet.empty _ (commonWienerFiltration S κ t), ae_eq_empty.2 hN⟩

/-- The integrand `g · 1{s ≤ ρ}` for a finite random time `ρ`. -/
def stopFn (ρ : DriverSample S κ → ℝ≥0) (g : κ → ℝ × DriverSample S κ → ℝ) :
    κ → ℝ × DriverSample S κ → ℝ :=
  fun a p => if p.1.toNNReal ≤ ρ p.2 then g a p else 0

omit [MeasurableSpace S] [Fintype κ] in
theorem stopIntegrand_coe (ρ : DriverSample S κ → ℝ≥0) (g : κ → ℝ × DriverSample S κ → ℝ) :
    stopIntegrand (fun x => (ρ x : WithTop ℝ≥0)) g = stopFn ρ g := by
  funext a p
  simp only [stopIntegrand, stopFn, WithTop.coe_le_coe]

variable {μ}

omit [IsProbabilityMeasure μ] in
/-- A family a.e. equal to the representatives of a predictable family is an integrand,
and its `L²` family is that predictable family. -/
theorem nativeIntegrand_of_family {T : ℝ≥0} {G : κ → ℝ × DriverSample S κ → ℝ}
    (F : PredictableFamily (S := S) (κ := κ) (μ := μ) T)
    (hF : ∀ a, (((F a : ScalarPredictable (κ := κ) μ T) :
      Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ)
        =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] G a) :
    ∃ hs : NativeIntegrand μ T G, hs.family = F := by
  have hs : NativeIntegrand μ T G := fun a =>
    ⟨(lpMeas.aestronglyMeasurable (F a)).congr (hF a), (Lp.memLp _).ae_eq (hF a)⟩
  refine ⟨hs, ?_⟩
  apply PiLp.ext
  intro a
  apply Subtype.ext
  apply Lp.ext
  change ((MemLp.toLp (G a) (hs a).2 : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) :
    ℝ × DriverSample S κ → ℝ) =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] _
  exact (MemLp.coeFn_toLp (f := G a) (hs a).2).trans (hF a).symm

omit [IsProbabilityMeasure μ] in
theorem nativeIntegrand_family_coeFn {T : ℝ≥0} {G : κ → ℝ × DriverSample S κ → ℝ}
    (hs : NativeIntegrand μ T G) (a : κ) :
    (((hs.family a : ScalarPredictable (κ := κ) μ T) :
      Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ)
        =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] G a :=
  MemLp.coeFn_toLp (f := G a) (hs a).2

/-- A `driverLaw μ`-a.e. property of the sample holds `dt ⊗ driverLaw μ`-a.e. -/
theorem ae_timeProb_of_ae {T : ℝ≥0} {q : DriverSample S κ → Prop}
    (hq : ∀ᵐ x ∂driverLaw (κ := κ) μ, q x) :
    ∀ᵐ p ∂timeProbMeasure T (driverLaw (κ := κ) μ), q p.2 :=
  (Measure.quasiMeasurePreserving_snd).ae hq

end BlockBand.SourceProcess.Stochastic.Integral
