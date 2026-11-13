module

public import BlockBand.SourceProcess.WienerRecovery.BrownianCanonicalDyadicEvalClosure
public import BlockBand.SourceProcess.WienerRecovery.ScalarWienerRealizationClosure

/-!
# Unconditional Wiener measure on all nonnegative continuous paths

The dyadic construction gives, for every positive compact
horizon, a measurable continuous modification of the canonical Brownian
cylinder process.  We choose these modifications at the integer horizons
`n + 1`.  Any two choices agree almost surely on their common interval: it is
enough to intersect the fixed-time almost-sure equalities along a countable
dense sequence, then use continuity.  A countable intersection makes all
compact modifications compatible simultaneously.

At a time `t`, choose any integer horizon containing `t` and evaluate its
compact modification.  On the simultaneous compatibility event this scalar
process is locally one of the continuous compact paths, hence is continuous.
Every fixed-time coordinate is still almost surely the raw Brownian
coordinate.  The measurable continuous-path modification
(`measurableContinuousPathModification`) then produces a measurable
`C(NNReal, ℝ)`-valued map.  Pushing forward the raw Brownian measure gives exactly
Mathlib's centered Gaussian projective family with covariance `min s t`
(`scalarWienerMeasureExists`).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery

open scoped NNReal Topology
open Filter MeasureTheory ProbabilityTheory

namespace ScalarWienerMeasureAllPathExistence

open CEH.ScalarWienerRealizationClosure
open CEH.ScalarWienerMeasureConstruction
open CEH.BrownianCylinderContinuityAtEmptyClosure
open CEH.BrownianDyadicCompactExtension
open CEH.BrownianCanonicalDyadicEvalClosure
open MomentFlowMeasurablePathModification

/-- The positive integer horizon used for the `n`-th compact modification. -/
def integerHorizon (n : ℕ) : NNReal := n + 1

@[simp] theorem integerHorizon_pos (n : ℕ) : 0 < integerHorizon n := by
  simp [integerHorizon]

/-- A measurable compact-horizon Brownian modification at time `n + 1`. -/
def compactBrownianPath (n : ℕ) : BrownianRawPath → CompactPath (integerHorizon n) :=
  Classical.choose
    (exists_measurable_compactPath_modification
      brownianCylinderContinuityAtEmpty (integerHorizon n) (integerHorizon_pos n))

/-- Each chosen integer-horizon modification is measurable. -/
theorem measurable_compactBrownianPath (n : ℕ) :
    Measurable (compactBrownianPath n) :=
  (Classical.choose_spec
    (exists_measurable_compactPath_modification
      brownianCylinderContinuityAtEmpty (integerHorizon n) (integerHorizon_pos n))).1

/-- Each fixed coordinate of an integer-horizon modification agrees almost
surely with the raw Brownian coordinate. -/
theorem compactBrownianPath_ae_eq (n : ℕ)
    (t : Set.Icc (0 : NNReal) (integerHorizon n)) :
    (fun ω => compactBrownianPath n ω t) =ᵐ[
      brownianRawMeasure brownianCylinderContinuityAtEmpty]
      rawCoordinateProcess t.1 :=
  (Classical.choose_spec
    (exists_measurable_compactPath_modification
      brownianCylinderContinuityAtEmpty (integerHorizon n) (integerHorizon_pos n))).2.2 t

/-- The common compact interval of two integer horizons. -/
def commonInterval (n m : ℕ) : Set NNReal :=
  Set.Icc 0 (min (integerHorizon n) (integerHorizon m))

/-- Inclusion of the common interval into the `n`-th compact interval. -/
def commonToLeft (n m : ℕ) :
    commonInterval n m → Set.Icc (0 : NNReal) (integerHorizon n) :=
  fun t => ⟨t.1, t.2.1, t.2.2.trans (min_le_left _ _)⟩

/-- Inclusion of the common interval into the `m`-th compact interval. -/
def commonToRight (n m : ℕ) :
    commonInterval n m → Set.Icc (0 : NNReal) (integerHorizon m) :=
  fun t => ⟨t.1, t.2.1, t.2.2.trans (min_le_right _ _)⟩

/-- Almost surely, any two compact modifications agree throughout their common
interval.  Fixed-time equality is intersected only over a countable dense
sequence; continuity then supplies every time. -/
theorem compactBrownianPath_ae_agree (n m : ℕ) :
    ∀ᵐ ω ∂brownianRawMeasure brownianCylinderContinuityAtEmpty,
      ∀ t : commonInterval n m,
        compactBrownianPath n ω (commonToLeft n m t) =
          compactBrownianPath m ω (commonToRight n m t) := by
  let _ : Nonempty (commonInterval n m) :=
    ⟨⟨0, by simp [commonInterval]⟩⟩
  let d : ℕ → commonInterval n m := TopologicalSpace.denseSeq (commonInterval n m)
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq (commonInterval n m)
  have hae : ∀ k : ℕ, ∀ᵐ ω ∂brownianRawMeasure brownianCylinderContinuityAtEmpty,
      compactBrownianPath n ω (commonToLeft n m (d k)) =
        compactBrownianPath m ω (commonToRight n m (d k)) := by
    intro k
    filter_upwards [compactBrownianPath_ae_eq n (commonToLeft n m (d k)),
      compactBrownianPath_ae_eq m (commonToRight n m (d k))] with ω hn hm
    exact hn.trans hm.symm
  filter_upwards [ae_all_iff.2 hae] with ω hω
  intro t
  have hncont : Continuous (fun s : commonInterval n m =>
      compactBrownianPath n ω (commonToLeft n m s)) :=
    (compactBrownianPath n ω).continuous.comp
      (continuous_subtype_val.subtype_mk fun s =>
        ⟨s.2.1, s.2.2.trans (min_le_left _ _)⟩)
  have hmcont : Continuous (fun s : commonInterval n m =>
      compactBrownianPath m ω (commonToRight n m s)) :=
    (compactBrownianPath m ω).continuous.comp
      (continuous_subtype_val.subtype_mk fun s =>
        ⟨s.2.1, s.2.2.trans (min_le_right _ _)⟩)
  have heq := hd.equalizer hncont hmcont (funext hω)
  exact congrFun heq t

/-- All integer-horizon modifications are simultaneously compatible outside
one null set. -/
theorem compactBrownianPath_ae_all_agree :
    ∀ᵐ ω ∂brownianRawMeasure brownianCylinderContinuityAtEmpty,
      ∀ n m, ∀ t : commonInterval n m,
        compactBrownianPath n ω (commonToLeft n m t) =
          compactBrownianPath m ω (commonToRight n m t) := by
  exact ae_all_iff.2 fun n => ae_all_iff.2 fun m => compactBrownianPath_ae_agree n m

/-- A chosen integer horizon containing a given nonnegative time. -/
def containingIndex (t : NNReal) : ℕ :=
  Nat.find (exists_nat_ge t)

/-- The chosen integer horizon contains the time. -/
theorem le_integerHorizon_containingIndex (t : NNReal) :
    t ≤ integerHorizon (containingIndex t) := by
  have h : t ≤ (containingIndex t : NNReal) := by
    simpa [containingIndex] using Nat.find_spec (exists_nat_ge t)
  change t ≤ (containingIndex t : NNReal) + 1
  exact h.trans (le_add_of_nonneg_right zero_le_one)

/-- Evaluation of the chosen compact modification at an arbitrary time. -/
def compactCoordinateProcess (t : NNReal) (ω : BrownianRawPath) : ℝ :=
  compactBrownianPath (containingIndex t) ω
    ⟨t, bot_le, le_integerHorizon_containingIndex t⟩

/-- Every fixed coordinate of the glued scalar process is measurable. -/
theorem measurable_compactCoordinateProcess (t : NNReal) :
    Measurable (compactCoordinateProcess t) := by
  exact (ContinuousMap.measurable_eval
    (⟨t, bot_le, le_integerHorizon_containingIndex t⟩ :
      Set.Icc (0 : NNReal) (integerHorizon (containingIndex t)))).comp
    (measurable_compactBrownianPath (containingIndex t))

/-- Every fixed coordinate retains the canonical raw Brownian value almost
surely. -/
theorem compactCoordinateProcess_ae_eq (t : NNReal) :
    compactCoordinateProcess t =ᵐ[
      brownianRawMeasure brownianCylinderContinuityAtEmpty]
      rawCoordinateProcess t := by
  exact compactBrownianPath_ae_eq (containingIndex t)
    ⟨t, bot_le, le_integerHorizon_containingIndex t⟩

/-- On the simultaneous compatibility event, the chosen-coordinate process is
continuous on all of `NNReal`. -/
theorem continuous_compactCoordinateProcess_of_all_agree
    (ω : BrownianRawPath)
    (hω : ∀ n m, ∀ t : commonInterval n m,
      compactBrownianPath n ω (commonToLeft n m t) =
        compactBrownianPath m ω (commonToRight n m t)) :
    Continuous fun t => compactCoordinateProcess t ω := by
  rw [continuous_iff_continuousAt]
  intro t
  let N : ℕ := containingIndex t + 1
  have htN : t < integerHorizon N := by
    have hle := le_integerHorizon_containingIndex t
    exact lt_of_le_of_lt hle (by simp [N, integerHorizon])
  let clamp : NNReal → Set.Icc (0 : NNReal) (integerHorizon N) :=
    fun s => ⟨min s (integerHorizon N), bot_le, min_le_right _ _⟩
  have hclamp : Continuous clamp :=
    (continuous_id.min continuous_const).subtype_mk _
  let localPath : NNReal → ℝ := fun s => compactBrownianPath N ω (clamp s)
  have hlocal : Continuous localPath := (compactBrownianPath N ω).continuous.comp hclamp
  have hnhds : Set.Iio (integerHorizon N) ∈ 𝓝 t :=
    Iio_mem_nhds htN
  have heq : (fun s => compactCoordinateProcess s ω) =ᶠ[𝓝 t] localPath := by
    filter_upwards [hnhds] with s hs
    have hsN : s ≤ integerHorizon N := hs.le
    let u : commonInterval (containingIndex s) N :=
      ⟨s, bot_le, le_min (le_integerHorizon_containingIndex s) hsN⟩
    have h := hω (containingIndex s) N u
    simpa [compactCoordinateProcess, localPath, clamp, commonToLeft,
      commonToRight, u, min_eq_left hsN] using h
  exact hlocal.continuousAt.congr_of_eventuallyEq heq

/-- The glued scalar process has almost surely continuous sample paths. -/
theorem compactCoordinateProcess_ae_continuous :
    ∀ᵐ ω ∂brownianRawMeasure brownianCylinderContinuityAtEmpty,
      Continuous fun t => compactCoordinateProcess t ω := by
  filter_upwards [compactBrownianPath_ae_all_agree] with ω hω
  exact continuous_compactCoordinateProcess_of_all_agree ω hω

/-- A measurable all-time continuous-path modification of the canonical raw
Brownian coordinate process. -/
def allTimeBrownianPath : BrownianRawPath → ScalarContinuousPath :=
  measurableContinuousPathModification
    (brownianRawMeasure brownianCylinderContinuityAtEmpty) 0
    compactCoordinateProcess
    (fun t => (measurable_compactCoordinateProcess t).aemeasurable)
    compactCoordinateProcess_ae_continuous

/-- The all-time continuous-path modification is measurable. -/
theorem measurable_allTimeBrownianPath : Measurable allTimeBrownianPath :=
  measurable_measurableContinuousPathModification
    (brownianRawMeasure brownianCylinderContinuityAtEmpty) 0
    compactCoordinateProcess
    (fun t => (measurable_compactCoordinateProcess t).aemeasurable)
    compactCoordinateProcess_ae_continuous

/-- At every fixed time, the all-time path agrees almost surely with the raw
Brownian coordinate. -/
theorem allTimeBrownianPath_ae_eq (t : NNReal) :
    (fun ω => allTimeBrownianPath ω t) =ᵐ[
      brownianRawMeasure brownianCylinderContinuityAtEmpty]
      rawCoordinateProcess t := by
  filter_upwards [measurableContinuousPathModification_ae_eq
      (brownianRawMeasure brownianCylinderContinuityAtEmpty) 0
      compactCoordinateProcess
      (fun s => (measurable_compactCoordinateProcess s).aemeasurable)
      compactCoordinateProcess_ae_continuous,
    compactCoordinateProcess_ae_eq t] with ω hpath hraw
  exact (hpath t).trans hraw

/-- The unconditional standard Wiener measure on all nonnegative continuous
paths. -/
def standardScalarWienerMeasure : Measure ScalarContinuousPath :=
  Measure.map allTimeBrownianPath
    (brownianRawMeasure brownianCylinderContinuityAtEmpty)

/-- The constructed measure has exactly the centered Gaussian finite-dimensional
laws with covariance `min s t`. -/
theorem isScalarWienerMeasure_standardScalarWienerMeasure :
    IsScalarWienerMeasure standardScalarWienerMeasure := by
  intro I
  unfold standardScalarWienerMeasure
  rw [Measure.map_map]
  · have hae :
        ((fun path : ScalarContinuousPath =>
          I.restrict fun t => coordinateProcess t path) ∘ allTimeBrownianPath)
          =ᵐ[brownianRawMeasure brownianCylinderContinuityAtEmpty] I.restrict := by
      have hfinite : ∀ᵐ ω ∂brownianRawMeasure brownianCylinderContinuityAtEmpty,
          ∀ t : I, allTimeBrownianPath ω t = ω t :=
        ae_all_iff.2 fun t => allTimeBrownianPath_ae_eq t
      filter_upwards [hfinite] with ω hω
      funext t
      exact hω t
    rw [Measure.map_congr hae]
    exact brownianRawMeasure_map_restrict brownianCylinderContinuityAtEmpty I
  · apply Measurable.of_eval
    intro (t : I)
    simpa [coordinateProcess] using ContinuousMap.measurable_eval (t : NNReal)
  · exact measurable_allTimeBrownianPath

/-- **Existence of scalar Wiener measure.**  There exists a probability measure
on `C(NNReal, ℝ)` whose coordinates are centered Gaussian with covariance
`min s t` (the proposition `ScalarWienerMeasureExists`). -/
theorem scalarWienerMeasureExists : ScalarWienerMeasureExists :=
  ⟨⟨standardScalarWienerMeasure,
    isScalarWienerMeasure_standardScalarWienerMeasure⟩⟩

end ScalarWienerMeasureAllPathExistence
end BlockBand.SourceProcess.WienerRecovery
