module

public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# A tight sequence whose integrals all converge has a weak limit

`exists_weak_limit_of_tight`: on a Hausdorff Borel space, if a sequence of probability measures is
tight and the integrals of every bounded continuous function converge, then some probability
measure `ν` is the weak limit of the sequence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory Filter Topology Set

/-- **Weak limit of a tight sequence with convergent integrals.** -/
theorem exists_weak_limit_of_tight {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [T2Space X] [BorelSpace X] (μ : ℕ → ProbabilityMeasure X)
    (ht : IsTightMeasureSet (Set.range fun n => (μ n : Measure X)))
    (hL : ∀ f : BoundedContinuousFunction X ℝ, ∃ L : ℝ,
      Tendsto (fun n => ∫ x, f x ∂(μ n : Measure X)) atTop (𝓝 L)) :
    ∃ ν : ProbabilityMeasure X, ∀ f : BoundedContinuousFunction X ℝ,
      Tendsto (fun n => ∫ x, f x ∂(μ n : Measure X)) atTop (𝓝 (∫ x, f x ∂(ν : Measure X))) := by
  have hS : {((ν : ProbabilityMeasure X) : Measure X) | ν ∈ Set.range μ} =
      Set.range fun n => (μ n : Measure X) := by
    ext ρ
    simp only [mem_ofPred_eq, mem_range, exists_exists_eq_and]
  have hC := isCompact_closure_of_isTightMeasureSet (S := Set.range μ) (hS ▸ ht)
  have hle : map μ atTop ≤ 𝓟 (closure (Set.range μ)) := by
    rw [le_principal_iff, mem_map]
    exact univ_mem' fun n => subset_closure (mem_range_self n)
  obtain ⟨ν, -, hν⟩ := hC (f := map μ atTop) hle
  refine ⟨ν, fun f => ?_⟩
  obtain ⟨L, hLf⟩ := hL f
  have hcont := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (X := X) f
  have hcl : ClusterPt (∫ x, f x ∂(ν : Measure X)) (𝓝 L) :=
    hν.map hcont.continuousAt (by simpa [Function.comp_def] using hLf)
  have heq : ∫ x, f x ∂(ν : Measure X) = L := by
    by_contra hne
    exact hcl.ne (disjoint_iff.1 (disjoint_nhds_nhds.2 hne))
  rw [heq]
  exact hLf

end BlockBand.SourceProcess.ComplexConstruct
