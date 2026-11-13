module

public import BlockBand.Endpoints.LaplaceDetermination

/-!
# Laplace-functional determination of marked point-process laws

A law-space ingredient of the uniqueness clause of the critical theorem (which also needs
inhabited critical sequences and uniqueness of weak limits, e.g. from the Hausdorff law space
`markedPointMeasureLaw_t2Space`). This file gives the Laplace-functional route on the marked
space, and identifies Laplace-encoded invariance with law invariance. The state space
`MarkedPointMeasure` carries the topology induced by
`ξ ↦ ξ.marked ∈ VaguePointMeasure (ℝ × P(𝕋))` and its Borel σ-algebra. A probability law on it
is determined by its marked Laplace functional `f ↦ E exp (-∫ f dξ.marked)` on nonnegative
`f ∈ C_c(ℝ × P(𝕋))`, the functional used by `IsSpectrallyStationary` and
`IsMarkRotationInvariant`.

Proof: the Borel σ-algebra of `MarkedPointMeasure` is the comap of the vague Borel
σ-algebra under `ξ ↦ ξ.marked` (the topology is induced), so a law is determined by
its image law on `VaguePointMeasure (ℝ × P(𝕋))`, which is determined by its Laplace
functional (`BlockBand.Endpoints.vaguePointMeasureLaw_eq_of_laplace`, for the locally
compact, second-countable, Hausdorff Borel space `ℝ × P(𝕋)`; Borelness of the
Giry σ-algebra on `P(𝕋)` is
`BlockBand.Model.Construction.markedSpectralSpace_borelSpace`). No cited input.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.LawSpace

open MeasureTheory

/-- The Borel σ-algebra of `MarkedPointMeasure` is the comap of the Borel
σ-algebra of `VaguePointMeasure (ℝ × P(𝕋))` under `ξ ↦ ξ.marked`. Both sides are the
`borel` instances. -/
theorem markedPointMeasure_measurableSpace_eq_comap :
    borel MarkedPointMeasure =
      MeasurableSpace.comap (fun ξ : MarkedPointMeasure => ξ.marked)
        (borel (VaguePointMeasure MarkedSpectralSpace)) :=
  borel_comap

/-- The marked-measure map `MarkedPointMeasure → VaguePointMeasure (ℝ × P(𝕋))` is
measurable for the Borel σ-algebras. -/
theorem measurable_marked : Measurable (fun ξ : MarkedPointMeasure => ξ.marked) :=
  (continuous_induced_dom : Continuous fun ξ : MarkedPointMeasure => ξ.marked).measurable

/-- Two measures on `MarkedPointMeasure` with the same image under `ξ ↦ ξ.marked`
are equal (no finiteness needed). -/
theorem measure_eq_of_map_marked_eq {μ ν : Measure MarkedPointMeasure}
    (h : μ.map (fun ξ : MarkedPointMeasure => ξ.marked) =
      ν.map (fun ξ : MarkedPointMeasure => ξ.marked)) : μ = ν := by
  ext s hs
  have hs' : MeasurableSet[MeasurableSpace.comap (fun ξ : MarkedPointMeasure => ξ.marked)
      (borel (VaguePointMeasure MarkedSpectralSpace))] s := by
    rw [← markedPointMeasure_measurableSpace_eq_comap]; exact hs
  obtain ⟨t, ht, rfl⟩ := hs'
  rw [← Measure.map_apply measurable_marked ht, ← Measure.map_apply measurable_marked ht, h]

/-- **Laplace-functional determination on marked point measures.** Two probability
laws `μ, ν` on `MarkedPointMeasure` (vague Borel σ-algebra) are equal as
soon as `∫ exp (-∫ f dξ.marked) dμ = ∫ exp (-∫ f dξ.marked) dν` for every nonnegative
compactly supported continuous `f` on `ℝ × P(𝕋)` (weak topology on `P(𝕋)`). -/
theorem markedPointMeasureLaw_eq_of_laplace (μ ν : ProbabilityMeasure MarkedPointMeasure)
    (h : ∀ f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ, (∀ z, 0 ≤ f z) →
      ∫ ξ, Real.exp (-∫ z, f z ∂ξ.marked.measure) ∂(μ : Measure MarkedPointMeasure) =
        ∫ ξ, Real.exp (-∫ z, f z ∂ξ.marked.measure) ∂(ν : Measure MarkedPointMeasure)) :
    μ = ν := by
  have := BlockBand.Model.Construction.markedSpectralSpace_borelSpace
  have hmap := BlockBand.Endpoints.vaguePointMeasureLaw_eq_of_laplace
    (μ.map (fun ξ => ξ.marked)) (ν.map (fun ξ => ξ.marked)) (fun f hf => by
      have hF : Measurable (fun η : VaguePointMeasure MarkedSpectralSpace =>
          Real.exp (-∫ z, f z ∂η.measure)) :=
        Real.continuous_exp.measurable.comp (BlockBand.Endpoints.measurable_coordinate f).neg
      change ∫ η, _ ∂((μ : Measure MarkedPointMeasure).map _) =
        ∫ η, _ ∂((ν : Measure MarkedPointMeasure).map _)
      rw [integral_map measurable_marked.aemeasurable hF.aestronglyMeasurable,
        integral_map measurable_marked.aemeasurable hF.aestronglyMeasurable]
      exact h f hf)
  apply ProbabilityMeasure.toMeasure_injective
  apply measure_eq_of_map_marked_eq
  exact congrArg (fun P : ProbabilityMeasure (VaguePointMeasure MarkedSpectralSpace) =>
    (P : Measure (VaguePointMeasure MarkedSpectralSpace))) hmap

end BlockBand.LawSpace
