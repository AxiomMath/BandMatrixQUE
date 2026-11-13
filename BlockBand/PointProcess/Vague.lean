module

public import BlockBand.Prelude

/-!
# Locally finite point measures and the vague topology

The topology is induced by integration against real compactly supported
continuous functions. This is the ordinary vague topology. Integer-valued
counts are stored on relatively compact Borel sets and are required to agree
with the underlying measure.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand

open MeasureTheory
open scoped ENNReal NNReal Topology

/-- A Borel set with compact closure. -/
structure RelativelyCompactBorelSet (X : Type*) [TopologicalSpace X]
    [MeasurableSpace X] where
  carrier : Set X
  measurable : MeasurableSet carrier
  compact_closure : IsCompact (closure carrier)

instance {X : Type*} [TopologicalSpace X] [MeasurableSpace X] :
    Coe (RelativelyCompactBorelSet X) (Set X) :=
  ⟨RelativelyCompactBorelSet.carrier⟩

/-- A locally finite integer-valued Borel measure. Multiplicities are allowed. -/
structure VaguePointMeasure (X : Type*) [TopologicalSpace X]
    [MeasurableSpace X] where
  measure : Measure X
  finite_on_compact : ∀ K : Set X, IsCompact K → measure K < ∞
  integer_valued :
    ∀ A : Set X, MeasurableSet A →
      measure A = ∞ ∨ ∃ n : ℕ, measure A = (n : ENNReal)
  count : RelativelyCompactBorelSet X → ℕ
  measure_eq_count : ∀ A, measure A.carrier = (count A : ENNReal)

instance {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (ξ : VaguePointMeasure X) : IsFiniteMeasureOnCompacts ξ.measure :=
  ⟨ξ.finite_on_compact⟩

/-- Vague coordinate given by integration against a compactly supported
continuous real test. -/
def VaguePointMeasure.coordinate
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (ξ : VaguePointMeasure X)
    (f : CompactlySupportedContinuousMap X ℝ) : ℝ :=
  ∫ x, f x ∂ξ.measure

/-- The ordinary vague topology, initial with respect to all compactly
supported continuous integral coordinates. -/
instance {X : Type*} [TopologicalSpace X] [MeasurableSpace X] :
    TopologicalSpace (VaguePointMeasure X) :=
  TopologicalSpace.induced
    (fun ξ : VaguePointMeasure X => fun f => ξ.coordinate f) inferInstance

instance {X : Type*} [TopologicalSpace X] [MeasurableSpace X] :
    MeasurableSpace (VaguePointMeasure X) :=
  borel (VaguePointMeasure X)

instance {X : Type*} [TopologicalSpace X] [MeasurableSpace X] :
    BorelSpace (VaguePointMeasure X) :=
  ⟨rfl⟩

/-- The unit torus of the paper. -/
abbrev Torus := AddCircle (1 : ℝ)

/-- The mass-profile mark space `P(T)` of the paper, with its weak topology. -/
abbrev MassProfile := ProbabilityMeasure Torus

/-- Spectral location together with a mass-profile mark. -/
abbrev MarkedSpectralSpace := ℝ × MassProfile

/-- A marked point measure together with its uniquely constrained spectral
pushforward. Its topology below is induced by the marked measure alone, hence
is exactly the ordinary vague topology on `ℝ × P(T)`; the redundant spectral
field does not strengthen that topology. -/
structure MarkedPointMeasure where
  marked : VaguePointMeasure MarkedSpectralSpace
  spectral : VaguePointMeasure ℝ
  spectral_eq :
    spectral.measure = Measure.map Prod.fst marked.measure

instance : TopologicalSpace MarkedPointMeasure :=
  TopologicalSpace.induced
    (fun ξ : MarkedPointMeasure => ξ.marked) inferInstance

instance : MeasurableSpace MarkedPointMeasure :=
  borel MarkedPointMeasure

instance : BorelSpace MarkedPointMeasure :=
  ⟨rfl⟩

/-- Forget all profile marks. -/
def MarkedPointMeasure.spectralProjection
    (ξ : MarkedPointMeasure) : VaguePointMeasure ℝ :=
  ξ.spectral

/-- Spectral projection of a law on marked point measures. -/
def spectralProjectionLaw
    (law : ProbabilityMeasure MarkedPointMeasure) :
    ProbabilityMeasure (VaguePointMeasure ℝ) :=
  law.map MarkedPointMeasure.spectralProjection

/-- A point measure has no repeated spectral locations. -/
def IsSimplePointMeasure (ξ : VaguePointMeasure ℝ) : Prop :=
  ∀ x : ℝ, ξ.measure {x} ≤ 1

end BlockBand
