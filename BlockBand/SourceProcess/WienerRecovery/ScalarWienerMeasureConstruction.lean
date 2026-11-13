module

public import BlockBand.SourceProcess.WienerRecovery.ScalarWienerRealizationClosure
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

/-!
# Measure-extension reduction for scalar Wiener measure

This module carries Mathlib's Brownian finite-dimensional projective family through
the Carathéodory-extension and continuous-path pushforward steps.

The analytic input consists of two statements.  First, the Brownian cylinder content
is continuous at the empty set on decreasing sequences of cylinders
(`BrownianCylinderContinuityAtEmpty`, proved as `brownianCylinderContinuityAtEmpty`);
this is the tightness step in the Kolmogorov extension theorem.  Second, the resulting
canonical raw-path process admits a measurable continuous modification, with fixed-time
almost-everywhere agreement (`BrownianContinuousModificationExists`, a hypothesis here);
this is the Kolmogorov–Chentsov conclusion.  One cannot ask that the canonical
uncountable product coordinate path itself be continuous almost surely: measurable
full-measure sets in the product sigma-algebra depend on only countably many
coordinates.  Mathlib contains the definition of a Kolmogorov process, but no theorem
proving either conclusion for the Brownian Gaussian family.

From these two statements, this file constructs the raw product measure by
Carathéodory, proves all its Brownian finite-dimensional marginals and probability
property, chooses a measurable continuous-path representative, and proves
`ScalarWienerMeasureExists` (`scalarWienerMeasureExists_of_extension_and_continuity`).
The unconditional proof is `scalarWienerMeasureExists`, through compact horizons.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped NNReal Topology
open Filter MeasureTheory ProbabilityTheory

namespace ScalarWienerMeasureConstruction

open ScalarWienerRealizationClosure

/-- The unrestricted scalar path space on which the cylinder content lives. -/
abbrev BrownianRawPath := NNReal → ℝ

/-- The canonical coordinate process on unrestricted scalar paths. -/
def rawCoordinateProcess (t : NNReal) (ω : BrownianRawPath) : ℝ :=
  ω t

/-- The tightness/extension condition: the Brownian cylinder content is continuous at
the empty set along decreasing sequences of measurable cylinders. It is proved as
`brownianCylinderContinuityAtEmpty`. -/
def BrownianCylinderContinuityAtEmpty : Prop :=
  ∀ (A : ℕ → Set BrownianRawPath),
    (∀ n, A n ∈ measurableCylinders (fun _ : NNReal => ℝ)) →
    Antitone A →
    (⋂ n, A n) = ∅ →
    Tendsto (fun n => brownianCylinderContent (A n)) atTop (𝓝 0)

/-- Continuity at the empty set supplies the sigma-subadditivity required by
Carathéodory's extension theorem. -/
theorem brownianCylinderContent_isSigmaSubadditive
    (hcont : BrownianCylinderContinuityAtEmpty) :
    brownianCylinderContent.IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders ?_
  exact addContent_iUnion_eq_sum_of_tendsto_zero
    isSetRing_measurableCylinders brownianCylinderContent
    (fun _ _ => projectiveFamilyContent_ne_top
      BrownianReal.isProjectiveMeasureFamily_projectiveFamily)
    hcont

/-- The canonical Carathéodory extension of the Brownian cylinder content to the
product sigma-algebra on unrestricted paths. -/
def brownianRawMeasure (hcont : BrownianCylinderContinuityAtEmpty) :
    Measure BrownianRawPath :=
  brownianCylinderContent.measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge
    (brownianCylinderContent_isSigmaSubadditive hcont)

/-- The raw extension agrees with the Brownian projective family on every finite
coordinate marginal. -/
theorem brownianRawMeasure_map_restrict
    (hcont : BrownianCylinderContinuityAtEmpty) (I : Finset NNReal) :
    Measure.map I.restrict (brownianRawMeasure hcont) =
      BrownianReal.projectiveFamily I := by
  refine Measure.ext fun S hS => ?_
  have hrestrict : Measurable (I.restrict : BrownianRawPath → (I → ℝ)) := by
    apply Measurable.of_eval
    intro t
    exact measurable_pi_apply (t : NNReal)
  rw [Measure.map_apply hrestrict hS]
  change brownianRawMeasure hcont (cylinder I S) =
    BrownianReal.projectiveFamily I S
  rw [brownianRawMeasure, brownianCylinderContent.measure_eq
    isSetSemiring_measurableCylinders generateFrom_measurableCylinders.symm
    (brownianCylinderContent_isSigmaSubadditive hcont)]
  · exact brownianCylinderContent_cylinder I S hS
  · exact (mem_measurableCylinders _).2 ⟨I, S, hS, rfl⟩

/-- The raw Carathéodory measure is the projective limit of Mathlib's Brownian
finite-dimensional family. -/
theorem isProjectiveLimit_brownianRawMeasure
    (hcont : BrownianCylinderContinuityAtEmpty) :
    IsProjectiveLimit (brownianRawMeasure hcont)
      BrownianReal.projectiveFamily :=
  brownianRawMeasure_map_restrict hcont

/-- In particular the raw extension is automatically a probability measure. -/
theorem isProbabilityMeasure_brownianRawMeasure
    (hcont : BrownianCylinderContinuityAtEmpty) :
    IsProbabilityMeasure (brownianRawMeasure hcont) :=
  (isProjectiveLimit_brownianRawMeasure hcont).isProbabilityMeasure

/-- The coordinate process of the raw extension has exactly the pre-Brownian
finite-dimensional laws. -/
theorem isPreBrownianReal_rawCoordinateProcess
    (hcont : BrownianCylinderContinuityAtEmpty) :
    IsPreBrownianReal rawCoordinateProcess (brownianRawMeasure hcont) := by
  refine IsPreBrownianReal.mk' fun I => ?_
  refine ⟨?_, ?_⟩
  · apply Measurable.aemeasurable
    apply Measurable.of_eval
    intro t
    exact measurable_pi_apply (t : NNReal)
  · simpa [rawCoordinateProcess] using
      brownianRawMeasure_map_restrict hcont I

/-- The canonical raw coordinate process admits a measurable continuous-path
modification which agrees almost everywhere at each fixed time.  This is the
Kolmogorov–Chentsov conclusion; it makes no claim of simultaneous agreement at
uncountably many times. -/
def BrownianContinuousModificationExists
    (hcont : BrownianCylinderContinuityAtEmpty) : Prop :=
  ∃ F : BrownianRawPath → ScalarContinuousPath,
    Measurable F ∧
      ∀ t, (fun ω => F ω t) =ᵐ[brownianRawMeasure hcont]
        rawCoordinateProcess t

/-- A chosen measurable continuous modification of the raw coordinate process. -/
def brownianContinuousPathRepresentative
    (hcont : BrownianCylinderContinuityAtEmpty)
    (hmod : BrownianContinuousModificationExists hcont) :
    BrownianRawPath → ScalarContinuousPath :=
  Classical.choose hmod

/-- The continuous-path representative is measurable. -/
theorem measurable_brownianContinuousPathRepresentative
    (hcont : BrownianCylinderContinuityAtEmpty)
    (hmod : BrownianContinuousModificationExists hcont) :
    Measurable (brownianContinuousPathRepresentative hcont hmod) :=
  (Classical.choose_spec hmod).1

/-- At every fixed time, the representative agrees almost everywhere with the
corresponding raw coordinate. -/
theorem brownianContinuousPathRepresentative_ae_eq_at
    (hcont : BrownianCylinderContinuityAtEmpty)
    (hmod : BrownianContinuousModificationExists hcont) (t : NNReal) :
    (fun ω => brownianContinuousPathRepresentative hcont hmod ω t)
      =ᵐ[brownianRawMeasure hcont] rawCoordinateProcess t :=
  (Classical.choose_spec hmod).2 t

/-- Push the canonical raw Brownian measure to continuous path space. -/
def constructedScalarWienerMeasure
    (hcont : BrownianCylinderContinuityAtEmpty)
    (hmod : BrownianContinuousModificationExists hcont) :
    Measure ScalarContinuousPath :=
  Measure.map (brownianContinuousPathRepresentative hcont hmod)
    (brownianRawMeasure hcont)

/-- The constructed continuous-path law has every Brownian finite-dimensional
marginal. -/
theorem isScalarWienerMeasure_constructed
    (hcont : BrownianCylinderContinuityAtEmpty)
    (hmod : BrownianContinuousModificationExists hcont) :
    IsScalarWienerMeasure (constructedScalarWienerMeasure hcont hmod) := by
  intro I
  unfold constructedScalarWienerMeasure
  rw [Measure.map_map]
  · have hae :
        ((fun path : ScalarContinuousPath =>
          I.restrict fun t => coordinateProcess t path) ∘
            brownianContinuousPathRepresentative hcont hmod)
          =ᵐ[brownianRawMeasure hcont] I.restrict := by
      have hfinite : ∀ᵐ ω ∂(brownianRawMeasure hcont), ∀ t : I,
          brownianContinuousPathRepresentative hcont hmod ω t = ω t :=
        ae_all_iff.2 fun t =>
          brownianContinuousPathRepresentative_ae_eq_at hcont hmod t
      filter_upwards [hfinite] with ω hω
      funext t
      exact hω t
    rw [Measure.map_congr hae]
    exact brownianRawMeasure_map_restrict hcont I
  · apply Measurable.of_eval
    intro (t : I)
    simpa [coordinateProcess] using
      (ContinuousMap.measurable_eval (t : NNReal))
  · exact measurable_brownianContinuousPathRepresentative hcont hmod

/-- Carathéodory tightness plus Brownian Kolmogorov–Chentsov continuity proves
the scalar Wiener-measure existence proposition `ScalarWienerMeasureExists`. -/
theorem scalarWienerMeasureExists_of_extension_and_continuity
    (hcont : BrownianCylinderContinuityAtEmpty)
    (hmod : BrownianContinuousModificationExists hcont) :
    ScalarWienerMeasureExists :=
  ⟨⟨constructedScalarWienerMeasure hcont hmod,
    isScalarWienerMeasure_constructed hcont hmod⟩⟩

end ScalarWienerMeasureConstruction

end BlockBand.SourceProcess.WienerRecovery.CEH
