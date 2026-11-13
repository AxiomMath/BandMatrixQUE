module

public import BlockBand.Model.Construction.SpectralProfiles
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.PiSystem

/-!
# Measurable singletons of the Giry mark space

On a countably generated measurable space, singletons of probability measures are measurable in
the Giry σ-algebra; in particular the space `MassProfile` of torus mass profiles has measurable
singletons and is Hausdorff.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open MeasureTheory MeasurableSpace

/-- Closing a countable measurable generator under finite intersections yields a countable
determining π-system generating the same σ-algebra. -/
theorem exists_countable_measurable_generatingPiSystem (X : Type*) [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] :
    ∃ C : Set (Set X), C.Countable ∧ IsPiSystem C ∧
      MeasurableSpace.generateFrom C = (inferInstance : MeasurableSpace X) ∧
      ∀ s ∈ C, MeasurableSet s := by
  classical
  let G := MeasurableSpace.countableGeneratingSet X
  have hg : G.Countable := MeasurableSpace.countable_countableGeneratingSet
  let : Countable G := hg.to_subtype
  let F : Finset G → Set X := fun t => ⋂ g ∈ t, (g : Set X)
  let C : Set (Set X) := Set.range F
  have hc : C.Countable := Set.countable_range F
  have hm : ∀ s ∈ C, MeasurableSet s := by
    rintro s ⟨t, rfl⟩
    exact MeasurableSet.iInter fun g => MeasurableSet.iInter fun _ =>
      MeasurableSpace.measurableSet_countableGeneratingSet g.property
  have hp : IsPiSystem C := by
    rintro s ⟨t, rfl⟩ u ⟨r, rfl⟩ _
    refine ⟨t ∪ r, ?_⟩
    ext x
    simp only [F, Set.mem_iInter, Finset.mem_union, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩
    · rintro ⟨ht, hr⟩ g (h | h)
      · exact ht g h
      · exact hr g h
  have hgc : G ⊆ C := by
    intro s hs
    refine ⟨{⟨s, hs⟩}, ?_⟩
    ext x
    simp only [F, Set.mem_iInter, Finset.mem_singleton]
    constructor
    · intro h
      exact h ⟨s, hs⟩ rfl
    · intro h g hg
      subst g
      exact h
  have hgen : MeasurableSpace.generateFrom C = (inferInstance : MeasurableSpace X) := by
    apply le_antisymm
    · exact MeasurableSpace.generateFrom_le hm
    · rw [← MeasurableSpace.generateFrom_countableGeneratingSet (α := X)]
      exact MeasurableSpace.generateFrom_mono hgc
  exact ⟨C, hc, hp, hgen, hm⟩

/-- Probability-measure singletons are measurable in the Giry σ-algebra whenever the
underlying measurable space is countably generated. -/
theorem probabilityMeasure_measurableSingletonClass (X : Type*) [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] :
    MeasurableSingletonClass (ProbabilityMeasure X) := by
  classical
  obtain ⟨C, hc, hp, hgen, hm⟩ := exists_countable_measurable_generatingPiSystem X
  let : Countable C := hc.to_subtype
  let e : ProbabilityMeasure X → C → ENNReal := fun μ s => (μ : Measure X) s.1
  have he : Measurable e := measurable_pi_iff.mpr fun s =>
    (Measure.measurable_coe (hm s.1 s.2)).comp measurable_subtype_coe
  have hi : Function.Injective e := by
    intro μ ν hμν
    have : IsFiniteMeasure μ.val := by
      constructor
      rw [(isProbabilityMeasure_iff).mp μ.property]
      norm_num
    apply Subtype.ext
    apply ext_of_generate_finite C hgen.symm hp
    · intro s hs
      exact congrFun hμν ⟨s, hs⟩
    · simp
  constructor
  intro μ
  have hs : ({μ} : Set (ProbabilityMeasure X)) = e ⁻¹' {e μ} := by
    ext ν
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact hi.eq_iff.symm
  rw [hs]
  exact (measurableSet_singleton (e μ)).preimage he

/-- The mark space `MassProfile` has Giry-measurable singletons (needed by `integral_dirac`
for marked compactly supported continuous tests). -/
theorem massProfile_measurableSingletonClass : MeasurableSingletonClass MassProfile :=
  probabilityMeasure_measurableSingletonClass Torus

/-- The torus probability mark space is Hausdorff for its weak topology. -/
theorem massProfile_t2Space : T2Space MassProfile := inferInstance

end BlockBand.Model.Construction
