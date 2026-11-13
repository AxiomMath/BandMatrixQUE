module
public import BlockBand.Model.Construction.PhysicalSpectralLaplace
public import BlockBand.Model.Construction.MarkedStateTopologyConsequences

/-!
# Translation invariance of every critical marked subsequential limit

Every weak subsequential limit `ν` of the physical marked laws along a critical sequence is
invariant, as a whole law, under every global spectral translation:
`globalMarkedTranslationLaw t ν = ν`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Filter
open scoped Topology

theorem criticalSequence_marked_weakLimit_spectral_law_invariant {τ : ℝ}
    (s : CriticalSequence τ) (hτ : 0<τ) (b E : ℝ) (hb : 0<b) (hb' : b<1/2) (hE : E^2<4)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (ν : ProbabilityMeasure MarkedPointMeasure)
    (hlim : Tendsto (fun j=>(R (φ j)).markedLaw E) atTop (𝓝 ν)) (t : ℝ) :
    globalMarkedTranslationLaw t ν = ν := by
  have heqlaw : (fun j=>(R (φ j)).markedLaw E) =
      fun j=>criticalPhysicalMarkedLaws s b E hb hb' (φ j) := by
    funext j
    exact finiteRealization_markedLaw_eq_constructed (R (φ j)) E
  rw [heqlaw] at hlim
  apply markedPointMeasureLaw_eq_of_integrals
  intro f
  exact (criticalSequence_marked_weakLimit_spectral_integral_eq
    s hτ b E hb hb' hE φ hφ ν hlim t f).symm

end BlockBand.Model.Construction
