module
public import BlockBand.SourceProcess.Stochastic.Integral.BracketDrift
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Adaptedness of time integrals of predictable integrands

Raw filtration `F = commonWienerFiltration S κ`, raw predictable σ-algebra on `ℝ × Ω`,
`P = driverLaw μ`, `ν = timeProbMeasure T P`.

* `measurableSet_restrict_of_rawPredictable`: for a raw predictable set `A` and `u ≥ 0`,
  `((0,u] × Ω) ∩ A` is measurable for `Borel(ℝ) ⊗ F_u` (raw predictable ⇒ progressive).
* `stronglyMeasurable_integral_Ioc`: for a raw predictable `G`, `x ↦ ∫_{(0,u]} G(s,x) ds` is
  `F_u`-strongly measurable.
* `exists_adapted_integral_Ioc`: for `G` a.e. raw predictable on `ν` and `u ≤ T`, the same
  pathwise integral is `P`-a.e. equal to an `F_u`-strongly measurable function.
* `exists_adapted_bracketDrift`: the bracket drift at time `t` has a raw `F_{t ∧ T}`-measurable
  version.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]

/-- `Borel(ℝ) ⊗ F_u` on `ℝ × DriverSample S κ`. -/
abbrev progSpace (S κ : Type*) [MeasurableSpace S] (u : ℝ≥0) :
    MeasurableSpace (ℝ × DriverSample S κ) :=
  @Prod.instMeasurableSpace ℝ (DriverSample S κ) _ (commonWienerFiltration S κ u)

omit [Fintype κ] in
/-- Raw predictable sets restricted to `(0,u] × Ω` are `Borel ⊗ F_u`-measurable. -/
theorem measurableSet_restrict_of_rawPredictable (u : ℝ≥0) {A : Set (ℝ × DriverSample S κ)}
    (hA : MeasurableSet[rawPredictable S κ] A) :
    MeasurableSet[progSpace S κ u]
      ((Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (DriverSample S κ))) ∩ A) := by
  have hK : MeasurableSet[progSpace S κ u]
      (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (DriverSample S κ))) :=
    @MeasurableSet.prod ℝ (DriverSample S κ) _ (commonWienerFiltration S κ u) _ _
      measurableSet_Ioc (@MeasurableSet.univ _ (commonWienerFiltration S κ u))
  induction hA with
  | basic s hs =>
    rcases hs with ⟨B, _, rfl⟩ | ⟨a, b, B, hB, rfl⟩
    · have he : (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (DriverSample S κ))) ∩
          (({0} : Set ℝ) ×ˢ B) = ∅ := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true,
          Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h3 _
        rw [h3] at h1
        exact lt_irrefl _ h1.1
      rw [he]
      exact @MeasurableSet.empty _ (progSpace S κ u)
    · rw [Set.prod_inter_prod, Set.univ_inter]
      by_cases hau : a ≤ u
      · exact @MeasurableSet.prod ℝ (DriverSample S κ) _ (commonWienerFiltration S κ u) _ _
          (measurableSet_Ioc.inter measurableSet_Ioc) ((commonWienerFiltration S κ).mono hau B hB)
      · have he : Set.Ioc (0 : ℝ) u ∩ Set.Ioc (a : ℝ) (b : ℝ) = ∅ := by
          ext s
          simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false, not_and]
          intro h1 h2 _
          have : (u : ℝ) < a := by exact_mod_cast lt_of_not_ge hau
          linarith [h1.2]
        rw [he, Set.empty_prod]
        exact @MeasurableSet.empty _ (progSpace S κ u)
  | empty =>
    rw [Set.inter_empty]
    exact @MeasurableSet.empty _ (progSpace S κ u)
  | compl A _ ih =>
    have he : (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (DriverSample S κ))) ∩ Aᶜ =
        (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (DriverSample S κ))) \
          ((Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (DriverSample S κ))) ∩ A) := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff, not_and]
      tauto
    rw [he]
    exact hK.diff ih
  | iUnion f _ ih =>
    rw [Set.inter_iUnion]
    exact MeasurableSet.iUnion ih

omit [Fintype κ] in
/-- A raw predictable function cut off outside `(0,u] × Ω` is `Borel ⊗ F_u`-measurable. -/
theorem stronglyMeasurable_restrict_of_rawPredictable (u : ℝ≥0)
    {G : ℝ × DriverSample S κ → ℝ} (hG : StronglyMeasurable[rawPredictable S κ] G) :
    StronglyMeasurable[progSpace S κ u]
      ((Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (DriverSample S κ))).indicator G) := by
  have hK : MeasurableSet[progSpace S κ u]
      (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (DriverSample S κ))) :=
    @MeasurableSet.prod ℝ (DriverSample S κ) _ (commonWienerFiltration S κ u) _ _
      measurableSet_Ioc (@MeasurableSet.univ _ (commonWienerFiltration S κ u))
  apply @Measurable.stronglyMeasurable _ _ _ (progSpace S κ u)
  intro U hU
  rw [Set.indicator_preimage, Set.ite, Set.inter_comm]
  refine (measurableSet_restrict_of_rawPredictable u (hG.measurable hU)).union ?_
  exact (@measurable_const _ _ _ (progSpace S κ u) (0 : ℝ) _ hU).diff hK

omit [Fintype κ] in
/-- The pathwise integral over `(0,u]` of a raw predictable function is `F_u`-measurable. -/
theorem stronglyMeasurable_integral_Ioc (u : ℝ≥0) {G : ℝ × DriverSample S κ → ℝ}
    (hG : StronglyMeasurable[rawPredictable S κ] G) :
    StronglyMeasurable[commonWienerFiltration S κ u]
      (fun x => ∫ s in Set.Ioc (0 : ℝ) u, G (s, x)) := by
  have h := @StronglyMeasurable.integral_prod_left' ℝ (DriverSample S κ) ℝ _
    (commonWienerFiltration S κ u) volume _ _ _ _ (stronglyMeasurable_restrict_of_rawPredictable u hG)
  have he : (fun x => ∫ s in Set.Ioc (0 : ℝ) u, G (s, x)) = fun y =>
      ∫ s, (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (DriverSample S κ))).indicator G (s, y) := by
    funext y
    simp only [indicator_prod_univ_apply]
    exact (integral_indicator measurableSet_Ioc).symm
  rw [he]
  exact h

variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

/-- For `G` a.e. raw predictable on `dt ⊗ P` over `(0,T]` and `u ≤ T`, the pathwise integral
`x ↦ ∫_{(0,u]} G(s,x) ds` is `P`-a.e. equal to an `F_u`-strongly measurable function. -/
theorem exists_adapted_integral_Ioc {G : ℝ × DriverSample S κ → ℝ}
    (hG : AEStronglyMeasurable[rawPredictable S κ] G (timeProbMeasure T (driverLaw (κ := κ) μ)))
    {u : ℝ≥0} (huT : u ≤ T) :
    ∃ D : DriverSample S κ → ℝ, StronglyMeasurable[commonWienerFiltration S κ u] D ∧
      (fun x => ∫ s in Set.Ioc (0 : ℝ) u, G (s, x)) =ᵐ[driverLaw (κ := κ) μ] D := by
  obtain ⟨G', hG', hGG'⟩ := hG
  refine ⟨fun x => ∫ s in Set.Ioc (0 : ℝ) u, G' (s, x),
    stronglyMeasurable_integral_Ioc u hG', ?_⟩
  filter_upwards [ae_ae_of_ae_timeProb hGG'] with x hx
  apply setIntegral_congr_ae measurableSet_Ioc
  have hx' := (ae_restrict_iff' measurableSet_Ioc).1 hx
  filter_upwards [hx'] with s hs hsu
  exact hs (Set.Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 huT) hsu)

/-- The bracket drift at time `t` has a raw `F_{t ∧ T}`-measurable version. -/
theorem exists_adapted_bracketDrift {g h : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) (t : ℝ≥0) :
    ∃ D : DriverSample S κ → ℝ, StronglyMeasurable[commonWienerFiltration S κ (min t T)] D ∧
      bracketDrift T g h t =ᵐ[driverLaw (κ := κ) μ] D :=
  exists_adapted_integral_Ioc (aestronglyMeasurable_bracketDensity hg hh) (min_le_right t T)

end BlockBand.SourceProcess.Stochastic.Integral
