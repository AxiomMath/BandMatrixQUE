module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Measurable continuous-path modifications

A process with almost-everywhere continuous sample paths and almost-everywhere
measurable fixed-time evaluations canonically yields a measurable random variable in
the compact-open continuous-path space.  The construction first uses
`ContinuousMap.mkD` to replace discontinuous exceptional samples by a supplied default
path, proves null measurability from all evaluation maps, and then chooses a measurable
representative.  The resulting representative agrees with the original process at
**all times simultaneously** outside one null set.

The scalar specialization turns Mathlib's `IsBrownianReal` process into an everywhere
continuous, path-space measurable Brownian modification.  No independence between
several coordinates, matrix assembly, Ornstein–Uhlenbeck equation, eigenvalue law, or
noncollision estimate is asserted here.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.MomentFlowMeasurablePathModification

open scoped NNReal Topology
open Filter MeasureTheory ProbabilityTheory

/-- The `mkD` path-valued version of a process, before choosing a measurable
representative.  Discontinuous exceptional samples are sent to `default`. -/
def mkDProcess
    {T E Ω : Type*} [TopologicalSpace T] [TopologicalSpace E]
    (default : C(T, E)) (X : T → Ω → E) (ω : Ω) : C(T, E) :=
  ContinuousMap.mkD (fun t => X t ω) default

/-- Pointwise AE measurability plus AE sample continuity makes the `mkD` process
AE-measurable as a compact-open path-valued map. -/
theorem aemeasurable_mkDProcess
    {T E Ω : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [LocallyCompactSpace T] [TopologicalSpace E] [SecondCountableTopology E]
    [RegularSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (P : Measure Ω)
    (default : C(T, E)) (X : T → Ω → E)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcontinuous : ∀ᵐ ω ∂P, Continuous fun t => X t ω) :
    AEMeasurable (mkDProcess default X) P := by
  apply NullMeasurable.aemeasurable
  change @Measurable (NullMeasurableSpace Ω P) C(T, E) _ _
    (mkDProcess default X)
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  have heval : AEMeasurable (fun ω => mkDProcess default X ω t) P :=
    (hX t).congr (hcontinuous.mono fun ω hω =>
      (ContinuousMap.mkD_apply_of_continuous hω).symm)
  exact heval.nullMeasurable.measurable'

/-- A measurable continuous-path modification.  The chosen representative is applied
only after the path-valued `mkD` process has been proved AE-measurable. -/
def measurableContinuousPathModification
    {T E Ω : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [LocallyCompactSpace T] [TopologicalSpace E] [SecondCountableTopology E]
    [RegularSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (P : Measure Ω)
    (default : C(T, E)) (X : T → Ω → E)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcontinuous : ∀ᵐ ω ∂P, Continuous fun t => X t ω) : Ω → C(T, E) :=
  (aemeasurable_mkDProcess P default X hX hcontinuous).mk
    (mkDProcess default X)

/-- The continuous-path modification is measurable for the original
measurable structure on the sample space. -/
theorem measurable_measurableContinuousPathModification
    {T E Ω : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [LocallyCompactSpace T] [TopologicalSpace E] [SecondCountableTopology E]
    [RegularSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (P : Measure Ω)
    (default : C(T, E)) (X : T → Ω → E)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcontinuous : ∀ᵐ ω ∂P, Continuous fun t => X t ω) :
    Measurable (measurableContinuousPathModification P default X hX hcontinuous) :=
  (aemeasurable_mkDProcess P default X hX hcontinuous).measurable_mk

/-- Outside one null set, the measurable modification agrees with the original
process simultaneously at every time. -/
theorem measurableContinuousPathModification_ae_eq
    {T E Ω : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [LocallyCompactSpace T] [TopologicalSpace E] [SecondCountableTopology E]
    [RegularSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (P : Measure Ω)
    (default : C(T, E)) (X : T → Ω → E)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcontinuous : ∀ᵐ ω ∂P, Continuous fun t => X t ω) :
    ∀ᵐ ω ∂P, ∀ t,
      measurableContinuousPathModification P default X hX hcontinuous ω t = X t ω := by
  let hpath := aemeasurable_mkDProcess P default X hX hcontinuous
  filter_upwards [hcontinuous, hpath.ae_eq_mk] with ω hω heq
  intro t
  calc
    measurableContinuousPathModification P default X hX hcontinuous ω t =
        mkDProcess default X ω t := congrArg (fun f : C(T, E) => f t) heq.symm
    _ = X t ω := ContinuousMap.mkD_apply_of_continuous hω

/-- Canonical zero-default measurable continuous modification of a real Brownian
process. -/
def brownianContinuousModification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) : Ω → C(ℝ≥0, ℝ) :=
  measurableContinuousPathModification P 0 B
    (fun t => hB.toIsPreBrownianReal.aemeasurable t) hB.cont

/-- The Brownian continuous-path modification is measurable. -/
theorem measurable_brownianContinuousModification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    Measurable (brownianContinuousModification hB) :=
  measurable_measurableContinuousPathModification P 0 B
    (fun t => hB.toIsPreBrownianReal.aemeasurable t) hB.cont

/-- The Brownian modification agrees with the original Brownian process at every time
simultaneously outside one null set. -/
theorem brownianContinuousModification_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t, brownianContinuousModification hB ω t = B t ω :=
  measurableContinuousPathModification_ae_eq P 0 B
    (fun t => hB.toIsPreBrownianReal.aemeasurable t) hB.cont

/-- Evaluating the path-valued modification again gives a Brownian process. -/
theorem isBrownianReal_brownianContinuousModification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    IsBrownianReal (fun t ω => brownianContinuousModification hB ω t) P := by
  apply IsBrownianReal.mk
  · apply hB.toIsPreBrownianReal.congr
    intro t
    exact (brownianContinuousModification_ae_eq hB).mono fun ω hω => (hω t).symm
  · exact Filter.Eventually.of_forall fun ω =>
      (brownianContinuousModification hB ω).continuous

/-- Every fixed-time evaluation of the Brownian modification retains the centered
Gaussian law with variance `t`. -/
theorem hasLaw_brownianContinuousModification_eval
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (t : ℝ≥0) :
    HasLaw (fun ω => brownianContinuousModification hB ω t)
      (gaussianReal 0 t) P :=
  (isBrownianReal_brownianContinuousModification hB).toIsPreBrownianReal.hasLaw_eval t

end BlockBand.SourceProcess.WienerRecovery.MomentFlowMeasurablePathModification
