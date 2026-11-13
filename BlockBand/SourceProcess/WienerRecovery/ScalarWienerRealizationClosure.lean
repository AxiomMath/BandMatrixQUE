module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Process.Adapted
public import BlockBand.SourceProcess.WienerRecovery.MeasurableContinuousPathModification
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

/-!
# Scalar Wiener measure on continuous paths and its coordinate process

Mathlib provides the Brownian finite-dimensional Gaussian projective family,
its projectivity, and uniqueness/probability consequences for a supplied
projective limit.  It does not provide an existence theorem placing that family on
continuous path space.  This module sets up the scalar realization:

* it states the Wiener-measure specification `IsScalarWienerMeasure` and the
  existence proposition `ScalarWienerMeasureExists` (proved as
  `scalarWienerMeasureExists`);
* it constructs the Brownian cylinder content `brownianCylinderContent` from the
  projective family;
* it proves that a measure on `C(ℝ≥0, ℝ)` with those cylinder marginals has a
  Brownian coordinate process (`isBrownianReal_coordinateProcess`);
* it constructs the natural filtration and proves adaptedness
  (`adapted_coordinateProcess`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped NNReal Topology
open MeasureTheory ProbabilityTheory

namespace ScalarWienerRealizationClosure

open BlockBand.SourceProcess.WienerRecovery.MomentFlowMeasurablePathModification

/-- The scalar continuous-path sample space. -/
abbrev ScalarContinuousPath := C(NNReal, ℝ)

/-- Coordinate evaluation on scalar continuous paths. -/
def coordinateProcess (t : NNReal) (ω : ScalarContinuousPath) : ℝ :=
  ω t

/-- The exact finite-dimensional-law specification for Wiener measure on
continuous path space. -/
def IsScalarWienerMeasure (μ : Measure ScalarContinuousPath) : Prop :=
  ∀ I : Finset NNReal,
    Measure.map (fun ω : ScalarContinuousPath =>
      I.restrict fun t => coordinateProcess t ω) μ =
      BrownianReal.projectiveFamily I

/-- Existence of scalar Wiener measure on continuous paths. It is proved as
`scalarWienerMeasureExists`. -/
def ScalarWienerMeasureExists : Prop :=
  Nonempty {μ : Measure ScalarContinuousPath // IsScalarWienerMeasure μ}

/-- The Brownian finite-dimensional family yields a canonical additive
content on measurable cylinders of the unrestricted path product. -/
def brownianCylinderContent :
    AddContent ENNReal
      (measurableCylinders (fun _ : NNReal => ℝ)) :=
  projectiveFamilyContent BrownianReal.isProjectiveMeasureFamily_projectiveFamily

/-- The Brownian cylinder content has exactly the Gaussian value on every measurable
finite-dimensional cylinder. -/
theorem brownianCylinderContent_cylinder
    (I : Finset NNReal) (S : Set (I → ℝ)) (hS : MeasurableSet S) :
    brownianCylinderContent (cylinder I S) =
      BrownianReal.projectiveFamily I S := by
  exact projectiveFamilyContent_cylinder
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily hS

/-- A continuous-path measure with the Brownian finite-dimensional marginals
makes its coordinate process a pre-Brownian motion. -/
theorem isPreBrownianReal_coordinateProcess
    {μ : Measure ScalarContinuousPath} (hμ : IsScalarWienerMeasure μ) :
    IsPreBrownianReal coordinateProcess μ := by
  refine IsPreBrownianReal.mk' fun I => ?_
  refine ⟨?_, hμ I⟩
  apply Measurable.aemeasurable
  apply Measurable.of_eval
  intro (t : I)
  simpa [coordinateProcess] using
    (ContinuousMap.measurable_eval (t : NNReal))

/-- Such a measure is automatically a probability measure. -/
theorem isProbabilityMeasure_of_isScalarWienerMeasure
    {μ : Measure ScalarContinuousPath} (hμ : IsScalarWienerMeasure μ) :
    IsProbabilityMeasure μ :=
  (isPreBrownianReal_coordinateProcess hμ).isGaussianProcess.isProbabilityMeasure

/-- Continuity is pointwise automatic because samples themselves are
continuous maps.  Hence the coordinate process is a Brownian motion. -/
theorem isBrownianReal_coordinateProcess
    {μ : Measure ScalarContinuousPath} (hμ : IsScalarWienerMeasure μ) :
    IsBrownianReal coordinateProcess μ := by
  refine ⟨isPreBrownianReal_coordinateProcess hμ, ?_⟩
  exact Filter.Eventually.of_forall fun ω => ω.continuous

/-- Prefix of a continuous path through time `t`. -/
def pathPrefix (t : NNReal) :
    ScalarContinuousPath → (Set.Iic t → ℝ) :=
  fun ω s => ω s.1

/-- Every continuous-path prefix is measurable. -/
theorem measurable_pathPrefix (t : NNReal) :
    Measurable (pathPrefix t) := by
  apply Measurable.of_eval
  intro s
  exact ContinuousMap.measurable_eval s.1

/-- Natural coordinate filtration on continuous path space. -/
def naturalFiltration :
    Filtration NNReal
      (inferInstance : MeasurableSpace ScalarContinuousPath) where
  seq t := MeasurableSpace.comap (pathPrefix t)
    (inferInstance : MeasurableSpace (Set.Iic t → ℝ))
  mono' := by
    intro s t hst
    let restrict : (Set.Iic t → ℝ) → (Set.Iic s → ℝ) :=
      fun x u => x ⟨u.1, u.2.trans hst⟩
    have hr : Measurable restrict := by
      apply Measurable.of_eval
      intro u
      exact measurable_pi_apply
        (⟨u.1, u.2.trans hst⟩ : Set.Iic t)
    have heq : pathPrefix s = restrict ∘ pathPrefix t := rfl
    change MeasurableSpace.comap (pathPrefix s) _ ≤
      MeasurableSpace.comap (pathPrefix t) _
    have hm : @Measurable ScalarContinuousPath (Set.Iic s → ℝ)
        (MeasurableSpace.comap (pathPrefix t)
          (inferInstance : MeasurableSpace (Set.Iic t → ℝ)))
        (inferInstance : MeasurableSpace (Set.Iic s → ℝ))
        (pathPrefix s) := by
      rw [heq]
      exact hr.comp (comap_measurable (pathPrefix t))
    exact hm.comap_le
  le' t := (measurable_pathPrefix t).comap_le

/-- The coordinate process is adapted to its natural filtration. -/
theorem adapted_coordinateProcess :
    Adapted naturalFiltration coordinateProcess := by
  intro t
  change @Measurable ScalarContinuousPath ℝ
    (MeasurableSpace.comap (pathPrefix t)
      (inferInstance : MeasurableSpace (Set.Iic t → ℝ)))
    inferInstance (coordinateProcess t)
  change @Measurable ScalarContinuousPath ℝ
    (MeasurableSpace.comap (pathPrefix t)
      (inferInstance : MeasurableSpace (Set.Iic t → ℝ)))
    inferInstance
    ((fun x : (Set.Iic t → ℝ) =>
      x ⟨t, Set.mem_Iic.mpr le_rfl⟩) ∘ pathPrefix t)
  exact (measurable_pi_apply
    (⟨t, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic t)).comp
      (comap_measurable (pathPrefix t))

end ScalarWienerRealizationClosure
end BlockBand.SourceProcess.WienerRecovery.CEH
