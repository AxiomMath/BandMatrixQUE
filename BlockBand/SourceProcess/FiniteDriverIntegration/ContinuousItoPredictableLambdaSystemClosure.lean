
module

public import BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousItoAdaptedRectangleDensity

/-!
# Predictable λ-system closure and elementary density

The sets whose unit indicators lie in the closed span of adapted rectangles form a
Dynkin system.  The generator calculation from
`ContinuousItoAdaptedRectangleDensity`, followed by Dynkin's π-λ theorem, therefore
places every predictable indicator in that closed span.  This gives density of the
elementary adapted rectangles in predictable `L²` (`elementaryPredictableSubmodule_dense`) and
the extension of continuous-linear identities from them (`continuousLinearMap_eq_of_eq_on_elementary`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousItoPredictableLambdaSystemClosure

open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open ContinuousIto ContinuousItoDensityClosure
open ContinuousItoAdaptedRectangleDensity

theorem predictableIndicatorL2_empty_mem {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)] :
    predictableIndicatorL2 ℱ T P
      (@MeasurableSet.empty (ℝ × Ω) (predictableSpace ℱ)) 1 ∈
      GridGeneratedPredictableL2 ℱ T P := by
  have hz : predictableIndicatorL2 ℱ T P
        (@MeasurableSet.empty (ℝ × Ω) (predictableSpace ℱ)) 1 = 0 := by
    apply (predictableL2_eq_iff_ae_eq _ _).2
    simp [predictableIndicatorL2]
  rw [hz]
  exact (GridGeneratedPredictableL2 ℱ T P).zero_mem

theorem predictableIndicatorL2_univ_mem {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)] :
    predictableIndicatorL2 ℱ T P
      (MeasurableSet.univ : MeasurableSet[predictableSpace ℱ] (Set.univ : Set (ℝ × Ω))) 1 ∈
      GridGeneratedPredictableL2 ℱ T P := by
  let e := elementaryPredictableL2 ℱ T P
    (s := 0) (t := T) (A := Set.univ) MeasurableSet.univ 1
  have he : e ∈ GridGeneratedPredictableL2 ℱ T P :=
    (elementaryPredictableSubmodule ℱ T P).le_topologicalClosure
      (elementaryPredictableL2_mem_submodule ℱ T P MeasurableSet.univ 1)
  have hsupport : ∀ᵐ x ∂timeProbMeasure T P,
      x.1 ∈ Set.Ioc (0 : ℝ) (T : ℝ) := by
    unfold timeProbMeasure
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Ioc)).2
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Filter.Eventually.of_forall (fun _ => ht)
  have hEq : predictableIndicatorL2 ℱ T P
      (MeasurableSet.univ : MeasurableSet[predictableSpace ℱ]
        (Set.univ : Set (ℝ × Ω))) 1 = e := by
    apply (predictableL2_eq_iff_ae_eq _ _).2
    unfold e elementaryPredictableL2 predictableIndicatorL2
    have heLp : MemLp (elementaryPredictable (0 : ℝ≥0) T
        (Set.univ : Set Ω) 1) 2 (timeProbMeasure T P) := by
      apply MemLp.of_bound
        ((stronglyMeasurable_elementaryPredictable ℱ MeasurableSet.univ 1).mono
          (predictableSpace_le ℱ) |>.aestronglyMeasurable) 1
      filter_upwards with x
      simp only [elementaryPredictable]
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ (Set.univ : Set Ω) <;>
        simp [hx]
    filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (μ := timeProbMeasure T P)
        (s := (Set.univ : Set (ℝ × Ω))) (c := (1 : ℝ)),
      heLp.coeFn_toLp, hsupport] with x hconst helem hx
    rw [hconst, helem]
    simp [elementaryPredictable, hx]
  rwa [hEq]

theorem predictableIndicatorL2_compl_mem {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)]
    {s : Set (ℝ × Ω)} (hs : MeasurableSet[predictableSpace ℱ] s)
    (hmem : predictableIndicatorL2 ℱ T P hs 1 ∈ GridGeneratedPredictableL2 ℱ T P) :
    predictableIndicatorL2 ℱ T P hs.compl 1 ∈ GridGeneratedPredictableL2 ℱ T P := by
  have hU := predictableIndicatorL2_univ_mem ℱ T P
  have hsub := (GridGeneratedPredictableL2 ℱ T P).sub_mem hU hmem
  have hEq : predictableIndicatorL2 ℱ T P hs.compl 1 =
      predictableIndicatorL2 ℱ T P
        (MeasurableSet.univ : MeasurableSet[predictableSpace ℱ]
          (Set.univ : Set (ℝ × Ω))) 1 -
        predictableIndicatorL2 ℱ T P hs 1 := by
    apply (predictableL2_eq_iff_ae_eq _ _).2
    change ((predictableIndicatorL2 ℱ T P hs.compl 1 : PredictableL2 ℱ T P) :
        Lp ℝ 2 (timeProbMeasure T P)) =ᵐ[timeProbMeasure T P]
      (((predictableIndicatorL2 ℱ T P
          (MeasurableSet.univ : MeasurableSet[predictableSpace ℱ]
            (Set.univ : Set (ℝ × Ω))) 1 : PredictableL2 ℱ T P) :
            Lp ℝ 2 (timeProbMeasure T P)) -
        ((predictableIndicatorL2 ℱ T P hs 1 : PredictableL2 ℱ T P) :
          Lp ℝ 2 (timeProbMeasure T P)) : Lp ℝ 2 (timeProbMeasure T P))
    have hsubcoe := Lp.coeFn_sub
      ((predictableIndicatorL2 ℱ T P
        (MeasurableSet.univ : MeasurableSet[predictableSpace ℱ]
          (Set.univ : Set (ℝ × Ω))) 1 : PredictableL2 ℱ T P) :
          Lp ℝ 2 (timeProbMeasure T P))
      ((predictableIndicatorL2 ℱ T P hs 1 : PredictableL2 ℱ T P) :
          Lp ℝ 2 (timeProbMeasure T P))
    filter_upwards [hsubcoe, indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (μ := timeProbMeasure T P) (s := sᶜ) (c := (1 : ℝ)),
      indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (μ := timeProbMeasure T P) (s := (Set.univ : Set (ℝ × Ω))) (c := (1 : ℝ)),
      indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (μ := timeProbMeasure T P) (s := s) (c := (1 : ℝ))]
      with x hsubx hc hu hsx
    rw [hsubx]
    simp only [Pi.sub_apply]
    dsimp only [predictableIndicatorL2]
    rw [hc, hu, hsx]
    by_cases hx : x ∈ s <;> simp [hx]
  rwa [hEq]

theorem predictableIndicatorL2_disjoint_union_mem {Ω : Type*}
    [MeasurableSpace Ω] (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)]
    {s t : Set (ℝ × Ω)} (hs : MeasurableSet[predictableSpace ℱ] s)
    (ht : MeasurableSet[predictableSpace ℱ] t) (hdisj : Disjoint s t)
    (hsmem : predictableIndicatorL2 ℱ T P hs 1 ∈ GridGeneratedPredictableL2 ℱ T P)
    (htmem : predictableIndicatorL2 ℱ T P ht 1 ∈ GridGeneratedPredictableL2 ℱ T P) :
    predictableIndicatorL2 ℱ T P (hs.union ht) 1 ∈
      GridGeneratedPredictableL2 ℱ T P := by
  have hadd := (GridGeneratedPredictableL2 ℱ T P).add_mem hsmem htmem
  have hEq : predictableIndicatorL2 ℱ T P (hs.union ht) 1 =
      predictableIndicatorL2 ℱ T P hs 1 + predictableIndicatorL2 ℱ T P ht 1 := by
    apply (predictableL2_eq_iff_ae_eq _ _).2
    change ((predictableIndicatorL2 ℱ T P (hs.union ht) 1 : PredictableL2 ℱ T P) :
        Lp ℝ 2 (timeProbMeasure T P)) =ᵐ[timeProbMeasure T P]
      (((predictableIndicatorL2 ℱ T P hs 1 : PredictableL2 ℱ T P) :
          Lp ℝ 2 (timeProbMeasure T P)) +
        ((predictableIndicatorL2 ℱ T P ht 1 : PredictableL2 ℱ T P) :
          Lp ℝ 2 (timeProbMeasure T P)) : Lp ℝ 2 (timeProbMeasure T P))
    have haddcoe := Lp.coeFn_add
      ((predictableIndicatorL2 ℱ T P hs 1 : PredictableL2 ℱ T P) :
        Lp ℝ 2 (timeProbMeasure T P))
      ((predictableIndicatorL2 ℱ T P ht 1 : PredictableL2 ℱ T P) :
        Lp ℝ 2 (timeProbMeasure T P))
    filter_upwards [haddcoe,
      indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (μ := timeProbMeasure T P) (s := s ∪ t) (c := (1 : ℝ)),
      indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (μ := timeProbMeasure T P) (s := s) (c := (1 : ℝ)),
      indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (μ := timeProbMeasure T P) (s := t) (c := (1 : ℝ))]
      with x haddx hu hsx htx
    rw [haddx]
    simp only [Pi.add_apply]
    dsimp only [predictableIndicatorL2]
    rw [hu, hsx, htx]
    have hnotboth : ¬(x ∈ s ∧ x ∈ t) := by
      intro hx
      exact Set.disjoint_left.1 hdisj hx.1 hx.2
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt] at *
  rwa [hEq]

theorem predictableIndicatorL2_iUnion_mem {Ω : Type*}
    [MeasurableSpace Ω] (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)]
    (f : ℕ → Set (ℝ × Ω))
    (hf : ∀ n, MeasurableSet[predictableSpace ℱ] (f n))
    (hdisj : Pairwise (Function.onFun Disjoint f))
    (hmem : ∀ n, predictableIndicatorL2 ℱ T P (hf n) 1 ∈
      GridGeneratedPredictableL2 ℱ T P) :
    predictableIndicatorL2 ℱ T P (MeasurableSet.iUnion hf) 1 ∈
      GridGeneratedPredictableL2 ℱ T P := by
  let a : ℕ → Set (ℝ × Ω) := fun n => Set.accumulate f n
  have ha_meas : ∀ n, MeasurableSet[predictableSpace ℱ] (a n) := by
    intro n
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hf i
  have ha_mem : ∀ n, predictableIndicatorL2 ℱ T P (ha_meas n) 1 ∈
      GridGeneratedPredictableL2 ℱ T P := by
    intro n
    induction n with
    | zero =>
        have heq : a 0 = f 0 := by
          ext x
          simp [a, Set.accumulate]
        simpa only [heq] using hmem 0
    | succ n ih =>
        have heq : a (n + 1) = a n ∪ f (n + 1) := by
          ext x
          simp only [a, Set.accumulate, mem_iUnion, mem_union]
          constructor
          · rintro ⟨i, hi, hxi⟩
            by_cases hin : i ≤ n
            · exact Or.inl ⟨i, hin, hxi⟩
            · right
              have : i = n + 1 := by omega
              simpa [this] using hxi
          · rintro (⟨i, hi, hxi⟩ | hxi)
            · exact ⟨i, by omega, hxi⟩
            · exact ⟨n + 1, le_rfl, hxi⟩
        have hd : Disjoint (a n) (f (n + 1)) := by
          apply Set.disjoint_left.2
          intro x hx hxf
          change x ∈ Set.accumulate f n at hx
          rcases mem_iUnion.1 hx with ⟨i, hx⟩
          rcases mem_iUnion.1 hx with ⟨hi, hxi⟩
          exact Set.disjoint_left.1
            (hdisj (ne_of_lt (lt_of_le_of_lt hi (Nat.lt_succ_self n)))) hxi hxf
        simpa only [heq] using
          (predictableIndicatorL2_disjoint_union_mem ℱ T P
            (ha_meas n) (hf (n + 1)) hd ih (hmem (n + 1)))
  let g : ℕ → PredictableL2 ℱ T P := fun n =>
    predictableIndicatorL2 ℱ T P (ha_meas n) 1
  let glim : PredictableL2 ℱ T P :=
    predictableIndicatorL2 ℱ T P (MeasurableSet.iUnion hf) 1
  have ha_subset (n : ℕ) : a n ⊆ ⋃ i, f i := by
    intro x hx
    change x ∈ Set.accumulate f n at hx
    rcases mem_iUnion.1 hx with ⟨i, hx⟩
    rcases mem_iUnion.1 hx with ⟨hi, hxi⟩
    exact mem_iUnion.2 ⟨i, hxi⟩
  have hmeasure : Tendsto
      (fun n => timeProbMeasure T P (symmDiff (a n) (⋃ i, f i))) atTop (nhds 0) := by
    have hbelow : Tendsto (fun n => timeProbMeasure T P (a n)) atTop
        (nhds (timeProbMeasure T P (⋃ i, f i))) := by
      simpa [a] using
        (tendsto_measure_iUnion_accumulate
          (μ := timeProbMeasure T P) (s := f))
    have hfin : timeProbMeasure T P (⋃ i, f i) ≠ ∞ := measure_ne_top _ _
    have hsub : Tendsto
        (fun n => timeProbMeasure T P (⋃ i, f i) - timeProbMeasure T P (a n))
        atTop (nhds 0) := by
      simpa using (ENNReal.Tendsto.sub tendsto_const_nhds hbelow (Or.inl hfin))
    apply hsub.congr'
    filter_upwards with n
    have hsymm : symmDiff (a n) (⋃ i, f i) = (⋃ i, f i) \ a n := by
      ext x
      simp [symmDiff_def]
      aesop
    rw [hsymm]
    exact (measure_sdiff (μ := timeProbMeasure T P) (ha_subset n) ((predictableSpace_le ℱ) (a n) (ha_meas n)).nullMeasurableSet
      (measure_ne_top (timeProbMeasure T P) (a n))).symm
  have hLp : Tendsto
      (fun n => (g n : Lp ℝ 2 (timeProbMeasure T P))) atTop
      (nhds (glim : Lp ℝ 2 (timeProbMeasure T P))) := by
    dsimp only [g, glim, predictableIndicatorL2]
    exact tendsto_indicatorConstLp_set (p := (2 : ℝ≥0∞)) (c := (1 : ℝ))
      (by norm_num) hmeasure
  have hg : Tendsto g atTop (nhds glim) := tendsto_subtype_rng.2 hLp
  exact (elementaryPredictableSubmodule ℱ T P).isClosed_topologicalClosure.mem_of_tendsto
    hg (Filter.Eventually.of_forall ha_mem)

/-- Unit-indicator membership, together with predictable measurability, is a Dynkin
system.  Complement closure is linear subtraction from the unit indicator; countable
disjoint-union closure is the `L²` limit of the finite accumulated unions. -/
def indicatorDynkinSystem {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)] :
    MeasurableSpace.DynkinSystem (ℝ × Ω) where
  Has s := ∃ hs : MeasurableSet[predictableSpace ℱ] s,
    predictableIndicatorL2 ℱ T P hs 1 ∈ GridGeneratedPredictableL2 ℱ T P
  has_empty := ⟨@MeasurableSet.empty (ℝ × Ω) (predictableSpace ℱ),
    predictableIndicatorL2_empty_mem ℱ T P⟩
  has_compl := by
    rintro s ⟨hs, hmem⟩
    exact ⟨hs.compl, predictableIndicatorL2_compl_mem ℱ T P hs hmem⟩
  has_iUnion_nat := by
    intro f hdisj hmem
    choose hf hfmem using hmem
    exact ⟨MeasurableSet.iUnion hf,
      predictableIndicatorL2_iUnion_mem ℱ T P f hf hdisj hfmem⟩

theorem generator_unitIndicator_mem {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)]
    (S : Set (ℝ × Ω)) (hS : S ∈ predictableGenerators ℱ) :
    (indicatorDynkinSystem ℱ T P).Has S := by
  have hSmeas : MeasurableSet[predictableSpace ℱ] S :=
    MeasurableSpace.measurableSet_generateFrom hS
  refine ⟨hSmeas, ?_⟩
  rcases predictableGenerator_is_zeroFace_or_elementary ℱ T P S hS with
    ⟨A, hA, rfl, hzero⟩ | ⟨s, t, A, hA, rfl⟩
  · let hempty : MeasurableSet[predictableSpace ℱ] (∅ : Set (ℝ × Ω)) :=
      @MeasurableSet.empty (ℝ × Ω) (predictableSpace ℱ)
    have hEq : predictableIndicatorL2 ℱ T P hSmeas 1 =
        predictableIndicatorL2 ℱ T P hempty 1 := by
      apply (predictableL2_eq_iff_ae_eq _ _).2
      have hnot : ∀ᵐ x ∂timeProbMeasure T P,
          x ∉ ({0} : Set ℝ) ×ˢ A := compl_mem_ae_iff.2 hzero
      unfold predictableIndicatorL2
      filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
          (μ := timeProbMeasure T P) (s := ({0} : Set ℝ) ×ˢ A) (c := (1 : ℝ)),
        indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
          (μ := timeProbMeasure T P) (s := (∅ : Set (ℝ × Ω))) (c := (1 : ℝ)),
        hnot] with x hxS hxempty hxs
      rw [hxS, hxempty]
      simp [hxs]
    rw [hEq]
    exact predictableIndicatorL2_empty_mem ℱ T P
  · let e := elementaryPredictableL2 ℱ T P (t := t) hA 1
    have he : e ∈ GridGeneratedPredictableL2 ℱ T P :=
      (elementaryPredictableSubmodule ℱ T P).le_topologicalClosure
        (elementaryPredictableL2_mem_submodule ℱ T P (t := t) hA 1)
    have hEq : predictableIndicatorL2 ℱ T P hSmeas 1 = e := by
      apply (predictableL2_eq_iff_ae_eq _ _).2
      unfold e elementaryPredictableL2 predictableIndicatorL2
      have heLp : MemLp (elementaryPredictable s t A 1) 2
          (timeProbMeasure T P) := by
        apply MemLp.of_bound
          ((stronglyMeasurable_elementaryPredictable ℱ hA 1).mono
            (predictableSpace_le ℱ) |>.aestronglyMeasurable) 1
        filter_upwards with x
        simp only [elementaryPredictable]
        by_cases hx : x ∈ Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A <;> simp [hx]
      filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
          (μ := timeProbMeasure T P)
          (s := Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A) (c := (1 : ℝ)),
        heLp.coeFn_toLp] with x hind helem
      rw [hind, helem]
      rfl
    rwa [hEq]

/-- Dynkin's π-λ theorem upgrades generator membership to every predictable set. -/
theorem predictable_unitIndicator_mem_gridGenerated {Ω : Type*}
    [MeasurableSpace Ω] (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)]
    (s : Set (ℝ × Ω)) (hs : MeasurableSet[predictableSpace ℱ] s) :
    predictableIndicatorL2 ℱ T P hs 1 ∈ GridGeneratedPredictableL2 ℱ T P := by
  let D := indicatorDynkinSystem ℱ T P
  have hle : MeasurableSpace.DynkinSystem.generate (predictableGenerators ℱ) ≤ D :=
    MeasurableSpace.DynkinSystem.generate_le D
      (generator_unitIndicator_mem ℱ T P)
  have hgen : (MeasurableSpace.DynkinSystem.generate
      (predictableGenerators ℱ)).Has s := by
    have hmeas : MeasurableSet[
        (MeasurableSpace.DynkinSystem.generate (predictableGenerators ℱ)).toMeasurableSpace
          (fun _ _ => MeasurableSpace.DynkinSystem.generate_inter
            (predictableGenerators_isPiSystem ℱ))] s := by
      rw [← MeasurableSpace.DynkinSystem.generateFrom_eq
        (predictableGenerators_isPiSystem ℱ)]
      exact hs
    exact hmeas
  rcases hle s hgen with ⟨hs', hmem⟩
  convert hmem using 1

/-- Every constant predictable indicator belongs to the closed elementary span. -/
theorem predictableIndicator_mem_gridGenerated {Ω : Type*}
    [MeasurableSpace Ω] (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)]
    (s : Set (ℝ × Ω)) (hs : MeasurableSet[predictableSpace ℱ] s) (c : ℝ) :
    predictableIndicatorL2 ℱ T P hs c ∈ GridGeneratedPredictableL2 ℱ T P := by
  have hone := predictable_unitIndicator_mem_gridGenerated ℱ T P s hs
  have hsmul := (GridGeneratedPredictableL2 ℱ T P).smul_mem c hone
  have hEq : predictableIndicatorL2 ℱ T P hs c =
      c • predictableIndicatorL2 ℱ T P hs 1 := by
    apply (predictableL2_eq_iff_ae_eq _ _).2
    have hcast :
        ((c • predictableIndicatorL2 ℱ T P hs 1 : PredictableL2 ℱ T P) :
          Lp ℝ 2 (timeProbMeasure T P)) =
        c • ((predictableIndicatorL2 ℱ T P hs 1 : PredictableL2 ℱ T P) :
          Lp ℝ 2 (timeProbMeasure T P)) := rfl
    rw [hcast]
    have hsmulcoe := Lp.coeFn_smul c
      ((predictableIndicatorL2 ℱ T P hs 1 : PredictableL2 ℱ T P) :
        Lp ℝ 2 (timeProbMeasure T P))
    filter_upwards [hsmulcoe,
      indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (μ := timeProbMeasure T P) (s := s) (c := c),
      indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (μ := timeProbMeasure T P) (s := s) (c := (1 : ℝ))]
      with x hsmulx hcx h1x
    rw [hsmulx]
    simp only [Pi.smul_apply, smul_eq_mul]
    dsimp only [predictableIndicatorL2]
    rw [hcx, h1x]
    by_cases hx : x ∈ s <;> simp [hx]
  rwa [hEq]

/-- Finite linear combinations of adapted rectangles are dense in all
predictable `L²`. -/
theorem elementaryPredictableSubmodule_dense {Ω : Type*}
    [MeasurableSpace Ω] (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)] :
    Dense (elementaryPredictableSubmodule ℱ T P : Set (PredictableL2 ℱ T P)) := by
  exact elementary_dense_of_indicator_mem_closure ℱ T P
    (predictableIndicator_mem_gridGenerated ℱ T P)

/-- An identity between continuous linear maps which holds on elementary adapted
rectangles holds on every predictable `L²` integrand, unconditionally under the
standard finite product-measure hypotheses. -/
theorem continuousLinearMap_eq_of_eq_on_elementary {Ω : Type*}
    [MeasurableSpace Ω] (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω)
    [SFinite P] [IsFiniteMeasure (timeProbMeasure T P)]
    {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F] [T2Space F]
    (A B : PredictableL2 ℱ T P →L[ℝ] F)
    (hAB : ∀ x ∈ elementaryPredictableSubmodule ℱ T P, A x = B x) :
    A = B := by
  exact ContinuousItoDensityClosure.continuousLinearMap_eq_of_eq_on_elementary
    ℱ T P (predictableIndicator_mem_gridGenerated ℱ T P) A B hAB

end BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousItoPredictableLambdaSystemClosure
