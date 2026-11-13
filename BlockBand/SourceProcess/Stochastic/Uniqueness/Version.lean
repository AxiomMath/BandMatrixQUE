module
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Metrizable.Basic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Jointly measurable versions of a.s. continuous processes

A measurability tool for the Gronwall estimates of the uniqueness argument. The process itself is
not modified: the version is only used inside `dt ⊗ P`-integrals and a.s. pathwise identities.

* **`exists_good_set`**: for an a.s. continuous process with measurable marginals there is a
  measurable full-measure set `A` of continuous paths.
* `jointVersion V A (r, ω) = 1_A(ω) V_{r⁺}(ω)`; **`measurable_jointVersion`**: it is jointly
  Borel measurable on `ℝ × Ω`, and it equals `V` on `A` at every time.
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory Filter Topology Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [TopologicalSpace E] [Zero E]

omit [Zero E] in
/-- A measurable full-measure set of continuous paths. -/
theorem exists_good_set {P : Measure Ω} {V : ℝ≥0 → Ω → E}
    (hc : ∀ᵐ ω ∂P, Continuous fun t => V t ω) :
    ∃ A : Set Ω, MeasurableSet A ∧ P Aᶜ = 0 ∧ ∀ ω ∈ A, Continuous fun t => V t ω := by
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hc)
  refine ⟨Nᶜ, hNm.compl, by rwa [compl_compl], fun ω hω => ?_⟩
  by_contra h
  exact hω (hN h)

/-- The jointly measurable version `1_A(ω) V_{r⁺}(ω)`. -/
def jointVersion (V : ℝ≥0 → Ω → E) (A : Set Ω) (p : ℝ × Ω) : E :=
  open Classical in if p.2 ∈ A then V p.1.toNNReal p.2 else 0

variable [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]

theorem measurable_jointVersion {V : ℝ≥0 → Ω → E} (hV : ∀ t, Measurable (V t)) {A : Set Ω}
    (hA : MeasurableSet A) (hAc : ∀ ω ∈ A, Continuous fun t => V t ω) :
    Measurable (jointVersion V A) := by
  have : Function.uncurry (fun (r : ℝ) (ω : Ω) => jointVersion V A (r, ω)) = jointVersion V A :=
    funext fun p => rfl
  rw [← this]
  refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun r => ?_)
  · by_cases hω : ω ∈ A
    · simp only [jointVersion, hω, ite_true]
      exact (hAc ω hω).comp continuous_real_toNNReal
    · simp only [jointVersion, hω, ite_false]
      exact continuous_const
  · exact Measurable.ite hA (hV r.toNNReal) measurable_const

omit [MeasurableSpace Ω] [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
  [MeasurableSpace E] [BorelSpace E] in
theorem jointVersion_of_mem {V : ℝ≥0 → Ω → E} {A : Set Ω} {ω : Ω} (hω : ω ∈ A) (r : ℝ) :
    jointVersion V A (r, ω) = V r.toNNReal ω := by
  simp [jointVersion, hω]

end BlockBand.SourceProcess.Stochastic.Uniqueness
