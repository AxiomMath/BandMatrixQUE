module

public import BlockBand.SourceProcess.CapCond.Count
public import BlockBand.SourceProcess.ClosedReduce.Entrance
public import BlockBand.SourceProcess.ClosedSum.Retained
public import BlockBand.SourceProcess.SourcePins.AtomLimit
public import BlockBand.Transmission.LawDuality.TightAbsorbed

/-!
# The cap test and its two sides

`capTest a c K` is the bounded continuous test `ν ↦ max(0, min(1, K + 1 - ∫ cutWeight a c dν))` on
`Fin 1 → FiniteMeasure [0,1]` (first coordinate), the form consumed by `IsTransmissionLimit.fdd`.

* Finite width (`W ≥ 1`, a.s.): `μ_W(s)` is the trace measure of the transmission sequence
  `physTseq` (`ae_transmissionProcess_eq_seq`, `isTransmissionSequence_physTseq`).
* Limit (a.s.): `μ(s)` is the trace measure of a transmission sequence (`entranceAtomic_of`).

On both sides `capTest` is then compared with the cap indicator through the counting bounds
`integral_cutWeight_le` and `lt_of_integral_cutWeight_lt`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedIdent BlockBand.SourceProcess.ClosedPath
open scoped ENNReal

/-- The clamp `r ↦ max 0 (min 1 (K + 1 - r))`. -/
def capClamp (K : ℕ) (r : ℝ) : ℝ := max 0 (min 1 ((K : ℝ) + 1 - r))

theorem capClamp_nonneg (K : ℕ) (r : ℝ) : 0 ≤ capClamp K r := le_max_left _ _

theorem capClamp_le_one (K : ℕ) (r : ℝ) : capClamp K r ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem capClamp_eq_one {K : ℕ} {r : ℝ} (h : r ≤ K) : capClamp K r = 1 := by
  unfold capClamp
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem lt_of_capClamp_pos {K : ℕ} {r : ℝ} (h : 0 < capClamp K r) : r < K + 1 := by
  by_contra hr
  have : min 1 ((K : ℝ) + 1 - r) ≤ 0 := (min_le_right _ _).trans (by linarith)
  unfold capClamp at h
  rw [max_eq_left this] at h
  exact lt_irrefl _ h

theorem continuous_capClamp (K : ℕ) : Continuous (capClamp K) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_id))

/-- The cap test on `Fin 1 → FiniteMeasure [0,1]`. -/
def capTest (a c : ℝ) (ha : 0 < a) (K : ℕ) :
    BoundedContinuousFunction (Fin 1 → FiniteMeasure unitInterval) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun v => capClamp K (∫ y, cutWeight a c y ∂(v 0 : Measure unitInterval)),
      (continuous_capClamp K).comp ((FiniteMeasure.continuous_integral_boundedContinuousFunction
        (BoundedContinuousFunction.mkOfCompact ⟨cutWeight a c, continuous_cutWeight ha c⟩)).comp
          (continuous_apply 0))⟩ 1
    (fun v w => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := capClamp_nonneg K (∫ y, cutWeight a c y ∂(v 0 : Measure unitInterval))
      have h2 := capClamp_le_one K (∫ y, cutWeight a c y ∂(v 0 : Measure unitInterval))
      have h3 := capClamp_nonneg K (∫ y, cutWeight a c y ∂(w 0 : Measure unitInterval))
      have h4 := capClamp_le_one K (∫ y, cutWeight a c y ∂(w 0 : Measure unitInterval))
      rw [abs_le]; constructor <;> linarith)

theorem capTest_apply (a c : ℝ) (ha : 0 < a) (K : ℕ) (v : Fin 1 → FiniteMeasure unitInterval) :
    capTest a c ha K v = capClamp K (∫ y, cutWeight a c y ∂(v 0 : Measure unitInterval)) := rfl

theorem capTest_nonneg (a c : ℝ) (ha : 0 < a) (K : ℕ) (v : Fin 1 → FiniteMeasure unitInterval) :
    0 ≤ capTest a c ha K v := capClamp_nonneg _ _

theorem capTest_le_one (a c : ℝ) (ha : 0 < a) (K : ℕ) (v : Fin 1 → FiniteMeasure unitInterval) :
    capTest a c ha K v ≤ 1 := capClamp_le_one _ _

/-- On a trace measure with `t_K < a` the test is `1`. -/
theorem capTest_eq_one {a c : ℝ} (ha : 0 < a) (hac : a < c) {K : ℕ}
    {v : Fin 1 → FiniteMeasure unitInterval} {t : ℕ → ℝ}
    (hν : (v 0 : Measure unitInterval) = seqTraceMeasure t) (ht : IsTransmissionSequence t)
    (hK : t K < a) : capTest a c ha K v = 1 :=
  capClamp_eq_one (integral_cutWeight_le (v 0) hν ht ha hac hK)

/-- On a trace measure where the test is positive, `t_K < c`. -/
theorem lt_of_capTest_pos {a c : ℝ} (ha : 0 < a) (hac : a < c) {K : ℕ}
    {v : Fin 1 → FiniteMeasure unitInterval} {t : ℕ → ℝ}
    (hν : (v 0 : Measure unitInterval) = seqTraceMeasure t) (ht : IsTransmissionSequence t)
    (hpos : 0 < capTest a c ha K v) : t K < c :=
  lt_of_integral_cutWeight_lt (v 0) hν ht ha hac (lt_of_capClamp_pos hpos)

/-- **Finite width**: a.s. `μ_W(s)` is the trace measure of the transmission sequence `physTseq`. -/
theorem ae_transmissionProcess_seq {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {W : ℕ} (hW : 1 ≤ W) (s : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, IsTransmissionSequence (physTseq b E s W ω) ∧
      (transmissionProcess b E (fun _ => 0) W s ω : Measure unitInterval) =
        seqTraceMeasure (physTseq b E s W ω) := by
  filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
    ClosedReduce.ae_transmissionProcess_eq_seq hb hE1 hE2 hW s] with ω hU he
  exact ⟨ClosedSum.isTransmissionSequence_physTseq (hU _).1, he⟩

/-- The finite-width test is integrable. -/
theorem integrable_capTest_W {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ}
    (s a c : ℝ) (ha : 0 < a) (K : ℕ) :
    Integrable (fun ω => capTest a c ha K (fun _ => transmissionProcess b E (fun _ => 0) W s ω))
      (growthPathLaw W b) := by
  have hae := Transmission.LawDuality.aemeasurable_transmissionProcess (W := W) (κ := fun _ => 0)
    (fun _ => le_rfl) (b := b) (by linarith) hE1 hE2 s
  have hX : AEMeasurable (fun ω => fun _ : Fin 1 => transmissionProcess b E (fun _ => 0) W s ω)
      (growthPathLaw W b) := AEMeasurable.of_eval fun _ => hae
  refine Integrable.of_bound ((capTest a c ha K).continuous.measurable.comp_aemeasurable
    hX).aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [capTest_nonneg a c ha K (fun _ => transmissionProcess b E
    (fun _ => 0) W s ω), capTest_le_one a c ha K (fun _ => transmissionProcess b E
    (fun _ => 0) W s ω)]

/-- The limit test is integrable. -/
theorem integrable_capTest_lim {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {μ : ℝ → Ω → FiniteMeasure unitInterval} {s : ℝ} (hμ : Measurable (μ s)) (a c : ℝ)
    (ha : 0 < a) (K : ℕ) :
    Integrable (fun ω => capTest a c ha K (fun _ => μ s ω)) P := by
  have hX : Measurable fun ω => (fun _ : Fin 1 => μ s ω) := Measurable.of_eval fun _ => hμ
  refine Integrable.of_bound ((capTest a c ha K).continuous.measurable.comp
    hX).aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [capTest_nonneg a c ha K (fun _ => μ s ω),
    capTest_le_one a c ha K (fun _ => μ s ω)]

/-- The entrance law of a measurable set of trace measures. -/
theorem entranceLaw_apply {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {μ : ℝ → Ω → FiniteMeasure unitInterval} {s : ℝ} (hμ : Measurable (μ s))
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) :
    entranceLaw P μ s S = P {ω | (μ s ω : Measure unitInterval) ∈ S} :=
  Measure.map_apply (measurable_subtype_coe.comp hμ) hS

theorem measurableSet_extract_lt (K : ℕ) (x : ℝ) :
    MeasurableSet {ν : Measure unitInterval | seqExtract ν K < x} :=
  measurableSet_lt ((measurable_pi_apply K).comp measurable_seqExtract) measurable_const

theorem measurableSet_extract_eq (K : ℕ) (x : ℝ) :
    MeasurableSet {ν : Measure unitInterval | seqExtract ν K = x} :=
  measurableSet_eq_fun ((measurable_pi_apply K).comp measurable_seqExtract) measurable_const

end BlockBand.SourceProcess.CapCond
