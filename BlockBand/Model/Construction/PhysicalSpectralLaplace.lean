module
public import BlockBand.Model.Construction.PhysicalSpectralStationarity
public import BlockBand.Model.Construction.PhysicalCanonicalLaw
public import BlockBand.PointProcess.LawProperties

/-!
# Spectral stationarity of every critical physical marked weak limit

Every weak subsequential limit of the physical marked laws along a critical sequence is
spectrally stationary (`IsSpectrallyStationary`), tested against the Laplace functionals
`ξ ↦ exp(-⟨ξ, f⟩)` of nonnegative compactly supported marked tests.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Filter
open scoped Topology

/-- A nonnegative compactly supported marked test gives the continuous Laplace test
`ξ ↦ exp(-⟨ξ, f⟩)`, bounded by one. -/
def markedLaplaceTest (f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ)
    (hf : ∀ z, 0 ≤ f z) : BoundedContinuousFunction MarkedPointMeasure ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ => Real.exp (-ξ.marked.coordinate f))
    (Real.continuous_exp.comp (((continuous_vaguePointMeasure_coordinate f).comp
      (show Continuous (fun ξ : MarkedPointMeasure=>ξ.marked) from continuous_induced_dom)).neg))
    1 (fun ξ => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (integral_nonneg hf)))

theorem criticalSequence_marked_weakLimit_spectrallyStationary {τ : ℝ}
    (s : CriticalSequence τ) (hτ : 0<τ) (b E : ℝ) (hb : 0<b) (hb' : b<1/2) (hE : E^2<4)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (ν : ProbabilityMeasure MarkedPointMeasure)
    (hlim : Tendsto (fun j=>(R (φ j)).markedLaw E) atTop (𝓝 ν)) :
    IsSpectrallyStationary ν := by
  have heqlaw : (fun j=>(R (φ j)).markedLaw E) =
      fun j=>criticalPhysicalMarkedLaws s b E hb hb' (φ j) := by
    funext j
    exact finiteRealization_markedLaw_eq_constructed (R (φ j)) E
  rw [heqlaw] at hlim
  intro t f hf
  let g := markedLaplaceTest f hf
  have h := criticalSequence_marked_weakLimit_spectral_integral_eq
    s hτ b E hb hb' hE φ hφ ν hlim t g
  have hm : (∫ ξ, g ξ ∂(globalMarkedTranslationLaw t ν : Measure MarkedPointMeasure)) =
      ∫ ξ, g (globalMarkedTranslation t ξ) ∂(ν : Measure MarkedPointMeasure) :=
    integral_map (measurable_globalMarkedTranslation t).aemeasurable g.continuous.aestronglyMeasurable
  rw [hm] at h
  have hg (ξ : MarkedPointMeasure) : g (globalMarkedTranslation t ξ) =
      Real.exp (-∫ z, f (z.1+t,z.2) ∂ξ.marked.measure) := by
    change Real.exp (-∫ z, f z ∂(globalMarkedTranslation t ξ).marked.measure) = _
    rw [globalMarkedTranslation_integral]
    rfl
  simp_rw [hg] at h
  exact h.symm

end BlockBand.Model.Construction
