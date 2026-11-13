module
public import BlockBand.SourceProcess.Stochastic.Integral.Family
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# From augmented to raw measurability

Generic facts, then their instances on the driver space `DriverSample S κ` with law
`driverLaw μ`, raw filtration `F = commonWienerFiltration S κ` and augmented filtration
`F_t ∨ N` (`driverAugmented μ`).

* `aestronglyMeasurable_sub_of_tendsto_ae`: for any sub-σ-algebra `m`, an a.e. limit of
  `AEStronglyMeasurable[m]` real functions is `AEStronglyMeasurable[m]` (Mathlib only has the
  ambient case).
* `aestronglyMeasurable_of_ae_sets`: if every `m'`-set is a.e. equal to an `m`-set, every
  `m'`-strongly measurable real function is `AEStronglyMeasurable[m]`.
* `augmentedContinuousFiltration μ`: `F_t ∨ N` in the `ContinuousFiltration` API, with predictable
  σ-algebra `predictableSpace (augmentedContinuousFiltration μ)` (the *augmented predictable*
  σ-algebra). Its sets are `dt ⊗ driverLaw μ`-a.e. raw predictable sets
  (`exists_rawPredictable_ae_eq`), hence augmented-predictable functions are a.e. raw predictable
  (`aestronglyMeasurable_rawPredictable_of_augmented`) on `timeProbMeasure T (driverLaw μ)`.
* `exists_raw_bounded_version`: a bounded `F_t ∨ N`-measurable real function has a raw
  `F_t`-measurable version with the same bound, equal to it `driverLaw μ`-a.e.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

section Generic
variable {α : Type*}

/-- An a.e. limit of `AEStronglyMeasurable[m]` real functions is `AEStronglyMeasurable[m]`,
for an arbitrary σ-algebra `m` (not necessarily the ambient one). -/
theorem aestronglyMeasurable_sub_of_tendsto_ae {m m₀ : MeasurableSpace α} {ν : Measure[m₀] α}
    {f : ℕ → α → ℝ}
    {g : α → ℝ} (hf : ∀ n, AEStronglyMeasurable[m] (f n) ν)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    AEStronglyMeasurable[m] g ν := by
  choose f' hf' hff' using hf
  refine ⟨fun x => limUnder atTop (fun n => f' n x), ?_, ?_⟩
  · exact @StronglyMeasurable.limUnder ℕ α ℝ m _ _ atTop _ f' _ _ hf'
  · filter_upwards [hlim, ae_all_iff.2 hff'] with x hx hx'
    have he : (fun n => f n x) = fun n => f' n x := funext hx'
    rw [he] at hx
    exact hx.limUnder_eq.symm

theorem aestronglyMeasurable_simpleFunc_of_ae_sets
    {m m₀ : MeasurableSpace α} {ν : Measure[m₀] α} [m' : MeasurableSpace α]
    (hsets : ∀ A, MeasurableSet[m'] A → ∃ B, MeasurableSet[m] B ∧ A =ᵐ[ν] B)
    (f : SimpleFunc α ℝ) : AEStronglyMeasurable[m] (⇑f) ν := by
  classical
  induction f using SimpleFunc.induction with
  | const c hs =>
    rename_i s
    obtain ⟨B, hB, hsB⟩ := hsets s hs
    refine ⟨B.indicator (fun _ => c), stronglyMeasurable_const.indicator hB, ?_⟩
    filter_upwards [hsB] with x hx
    have hx' : x ∈ s ↔ x ∈ B := Iff.of_eq hx
    rw [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_const]
    by_cases hxs : x ∈ s
    · rw [Set.piecewise_eq_of_mem _ _ _ hxs, Set.indicator_of_mem (hx'.1 hxs)]
      rfl
    · rw [Set.piecewise_eq_of_notMem _ _ _ hxs,
        Set.indicator_of_notMem (fun h => hxs (hx'.2 h))]
      rfl
  | add _ hf hg =>
    rw [SimpleFunc.coe_add]
    exact hf.add hg

/-- If every `m'`-measurable set is `ν`-a.e. equal to an `m`-measurable set, then every
`m'`-strongly measurable real function is `AEStronglyMeasurable[m]` for `ν`. -/
theorem aestronglyMeasurable_of_ae_sets {m m₀ : MeasurableSpace α}
    {ν : Measure[m₀] α} [m' : MeasurableSpace α]
    (hsets : ∀ A, MeasurableSet[m'] A → ∃ B, MeasurableSet[m] B ∧ A =ᵐ[ν] B)
    {f : α → ℝ} (hf : StronglyMeasurable[m'] f) : AEStronglyMeasurable[m] f ν :=
  aestronglyMeasurable_sub_of_tendsto_ae
    (fun n => aestronglyMeasurable_simpleFunc_of_ae_sets hsets (hf.approx n))
    (Eventually.of_forall hf.tendsto_approx)

theorem aestronglyMeasurable_of_ae_sets_ae {m m' m₀ : MeasurableSpace α} {ν : Measure[m₀] α}
    (hsets : ∀ A, MeasurableSet[m'] A → ∃ B, MeasurableSet[m] B ∧ A =ᵐ[ν] B)
    {f : α → ℝ} (hf : AEStronglyMeasurable[m'] f ν) : AEStronglyMeasurable[m] f ν := by
  obtain ⟨g, hg, hfg⟩ := hf
  exact (@aestronglyMeasurable_of_ae_sets α m m₀ ν m' hsets g hg).congr hfg.symm

end Generic

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ]

/-- The augmented filtration `F_t ∨ N` in the `ContinuousFiltration` API. -/
def augmentedContinuousFiltration : ContinuousFiltration (DriverSample S κ) where
  space := driverAugmented (κ := κ) μ
  mono_space := (driverAugmented (κ := κ) μ).mono'
  le_ambient := (driverAugmented (κ := κ) μ).le

/-- The augmented predictable σ-algebra on `ℝ × DriverSample S κ`. -/
abbrev augPredictable : MeasurableSpace (ℝ × DriverSample S κ) :=
  predictableSpace (augmentedContinuousFiltration (κ := κ) μ)

/-- Augmented predictable sets are raw predictable up to `dt ⊗ driverLaw μ`-null sets. -/
theorem exists_rawPredictable_ae_eq (T : ℝ≥0) {R : Set (ℝ × DriverSample S κ)}
    (hR : MeasurableSet[augPredictable (κ := κ) μ] R) :
    ∃ R', MeasurableSet[rawPredictable S κ] R' ∧
      R =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] R' := by
  induction hR with
  | basic s h =>
    rcases h with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
    · obtain ⟨B, hB, hAB⟩ := exists_raw_ae_eq μ hA
      refine ⟨({0} : Set ℝ) ×ˢ B, MeasurableSpace.measurableSet_generateFrom
        (Or.inl ⟨B, hB, rfl⟩), ?_⟩
      filter_upwards [ae_timeProb_of_ae (T := T) hAB] with p hp
      change (p.1 ∈ ({0} : Set ℝ) ∧ p.2 ∈ A) = (p.1 ∈ ({0} : Set ℝ) ∧ p.2 ∈ B)
      rw [show (p.2 ∈ A) = (p.2 ∈ B) from hp]
    · obtain ⟨B, hB, hAB⟩ := exists_raw_ae_eq μ hA
      refine ⟨Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B, MeasurableSpace.measurableSet_generateFrom
        (Or.inr ⟨s, t, B, hB, rfl⟩), ?_⟩
      filter_upwards [ae_timeProb_of_ae (T := T) hAB] with p hp
      change (p.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) ∧ p.2 ∈ A) = (p.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) ∧ p.2 ∈ B)
      rw [show (p.2 ∈ A) = (p.2 ∈ B) from hp]
  | empty => exact ⟨∅, @MeasurableSet.empty _ (rawPredictable S κ), EventuallyEq.rfl⟩
  | compl s _ ih =>
    obtain ⟨B, hB, h⟩ := ih
    exact ⟨Bᶜ, hB.compl, EventuallyEqSet.compl h⟩
  | iUnion f _ ih =>
    choose B hB h using ih
    exact ⟨⋃ i, B i, MeasurableSet.iUnion hB, EventuallyEqSet.countable_iUnion h⟩

/-- An a.e. augmented-predictable real function is a.e. raw predictable on
`timeProbMeasure T (driverLaw μ)`. -/
theorem aestronglyMeasurable_rawPredictable_of_augmented {T : ℝ≥0}
    {f : ℝ × DriverSample S κ → ℝ}
    (hf : AEStronglyMeasurable[augPredictable (κ := κ) μ] f
      (timeProbMeasure T (driverLaw (κ := κ) μ))) :
    AEStronglyMeasurable[rawPredictable S κ] f (timeProbMeasure T (driverLaw (κ := κ) μ)) :=
  aestronglyMeasurable_of_ae_sets_ae (fun _ hA => exists_rawPredictable_ae_eq μ T hA) hf

omit [IsProbabilityMeasure μ] in
/-- An `F_t ∨ N`-strongly measurable real function is a.e. raw `F_t`-strongly measurable. -/
theorem aestronglyMeasurable_raw_of_augmented {t : ℝ≥0} {f : DriverSample S κ → ℝ}
    (hf : StronglyMeasurable[driverAugmented (κ := κ) μ t] f) :
    AEStronglyMeasurable[commonWienerFiltration S κ t] f (driverLaw (κ := κ) μ) :=
  @aestronglyMeasurable_of_ae_sets _ _ _ _ (driverAugmented (κ := κ) μ t)
    (fun _ hA => exists_raw_ae_eq μ hA) f hf

omit [IsProbabilityMeasure μ] in
/-- A bounded `F_t ∨ N`-measurable real function has a raw `F_t`-measurable version with the
same bound. -/
theorem exists_raw_bounded_version {t : ℝ≥0} {H : DriverSample S κ → ℝ}
    (hH : StronglyMeasurable[driverAugmented (κ := κ) μ t] H) {C : ℝ}
    (hC : ∀ x, |H x| ≤ C) :
    ∃ H' : DriverSample S κ → ℝ, Measurable[commonWienerFiltration S κ t] H' ∧
      (∀ x, |H' x| ≤ C) ∧ H =ᵐ[driverLaw (κ := κ) μ] H' := by
  obtain ⟨G, hG, hHG⟩ := aestronglyMeasurable_raw_of_augmented μ hH
  refine ⟨fun x => max (-C) (min C (G x)), ?_, fun x => ?_, ?_⟩
  · exact measurable_const.max (measurable_const.min hG.measurable)
  · have h0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · filter_upwards [hHG] with x hx
    rw [← hx]
    have h := abs_le.1 (hC x)
    rw [min_eq_right h.2, max_eq_right h.1]

end BlockBand.SourceProcess.Stochastic.Integral
