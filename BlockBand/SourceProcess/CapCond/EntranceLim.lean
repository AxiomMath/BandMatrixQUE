module

public import BlockBand.SourceProcess.CapCond.Weighted

/-!
# The entrance on the cap event: weighted integrals

Definitions and integrability facts for `tendsto_capWeighted`: for a homogeneous transmission
limit, `s > 0`, `h > 0` with `P(t_K(μ(s)) = h²) = 0`, and a bounded continuous weight `w ≥ 0` on
`FiniteMeasure [0,1]`, `E_W[1_{physCapEvent} w(μ_W(s))] → E[1{μ(s) ∈ capSet K h} w(μ(s))]`. Here
`finInt` is the finite-width weighted integral and `limInt` its limit-side counterpart.
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

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {b E : ℝ} {w : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ}

/-- The limit-side weighted integral over a set of trace measures. -/
def limInt (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval) (s : ℝ)
    (w : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ) (S : Set (Measure unitInterval)) :
    ℝ :=
  ∫ ω, {ω | (μ s ω : Measure unitInterval) ∈ S}.indicator (fun ω => w (μ s ω)) ω ∂P

theorem integrable_limInd [IsFiniteMeasure P] {s : ℝ} (hμ : Measurable (μ s))
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) :
    Integrable ({ω | (μ s ω : Measure unitInterval) ∈ S}.indicator (fun ω => w (μ s ω))) P :=
  (Integrable.of_bound (w.continuous.measurable.comp hμ).aestronglyMeasurable ‖w‖
    (Eventually.of_forall fun _ => w.norm_coe_le_norm _)).indicator
    ((measurable_subtype_coe.comp hμ) hS)

/-- `limInt S' − limInt S ≤ ‖w‖ (ent S' − ent S)` for `S ⊆ S'`. -/
theorem limInt_sub_le [IsFiniteMeasure P] {s : ℝ} (hμ : Measurable (μ s))
    {S S' : Set (Measure unitInterval)} (hS : MeasurableSet S) (hS' : MeasurableSet S')
    (hSS : S ⊆ S') :
    limInt P μ s w S' - limInt P μ s w S ≤
      ‖w‖ * ((entranceLaw P μ s S').toReal - (entranceLaw P μ s S).toReal) := by
  have := isFiniteMeasure_entranceLaw P μ s
  have hm : MeasurableSet {ω | (μ s ω : Measure unitInterval) ∈ S' \ S} :=
    (measurable_subtype_coe.comp hμ) (hS'.diff hS)
  have e : ∀ ω, {ω | (μ s ω : Measure unitInterval) ∈ S'}.indicator (fun ω => w (μ s ω)) ω -
      {ω | (μ s ω : Measure unitInterval) ∈ S}.indicator (fun ω => w (μ s ω)) ω =
      {ω | (μ s ω : Measure unitInterval) ∈ S' \ S}.indicator (fun ω => w (μ s ω)) ω := by
    intro ω
    simp only [Set.indicator, Set.mem_ofPred_eq, Set.mem_sdiff]
    by_cases h1 : (μ s ω : Measure unitInterval) ∈ S
    · simp [h1, hSS h1]
    · by_cases h2 : (μ s ω : Measure unitInterval) ∈ S' <;> simp [h1, h2]
  rw [limInt, limInt, ← integral_sub (integrable_limInd hμ hS') (integrable_limInd hμ hS)]
  simp only [e]
  have hle : ∫ ω, {ω | (μ s ω : Measure unitInterval) ∈ S' \ S}.indicator (fun ω => w (μ s ω)) ω ∂P
      ≤ ∫ ω, {ω | (μ s ω : Measure unitInterval) ∈ S' \ S}.indicator (fun _ => ‖w‖) ω ∂P :=
    integral_mono (integrable_limInd hμ (hS'.diff hS)) ((integrable_const _).indicator hm)
      fun ω => Set.indicator_le_indicator ((le_abs_self _).trans (w.norm_coe_le_norm _))
  refine hle.trans (le_of_eq ?_)
  rw [integral_indicator_const _ hm, smul_eq_mul, mul_comm, measureReal_def,
    ← entranceLaw_apply P hμ (hS'.diff hS), measure_sdiff hSS hS.nullMeasurableSet
      (measure_ne_top _ _), ENNReal.toReal_sub_of_le (measure_mono hSS) (measure_ne_top _ _)]

/-- The finite-width weighted integral (Borel cap event). -/
def finInt (b E s h : ℝ) (K W : ℕ) (w : BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ) :
    ℝ :=
  ∫ ω, (physCapEventM b E s h K W).indicator
    (fun ω => w (transmissionProcess b E (fun _ => 0) W s ω)) ω ∂growthPathLaw W b

theorem aemeasurable_tp (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (W : ℕ) (s : ℝ) :
    AEMeasurable (fun ω => fun _ : Fin 1 => transmissionProcess b E (fun _ => 0) W s ω)
      (growthPathLaw W b) :=
  AEMeasurable.of_eval fun _ => Transmission.LawDuality.aemeasurable_transmissionProcess (W := W)
    (κ := fun _ => 0) (fun _ => le_rfl) (b := b) (by linarith) hE1 hE2 s

theorem integrable_finInd (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ} (s h : ℝ)
    (K : ℕ) : Integrable ((physCapEventM b E s h K W).indicator
      (fun ω => w (transmissionProcess b E (fun _ => 0) W s ω))) (growthPathLaw W b) := by
  have hae := Transmission.LawDuality.aemeasurable_transmissionProcess (W := W)
    (κ := fun _ => 0) (fun _ => le_rfl) (b := b) (by linarith) hE1 hE2 s
  exact (Integrable.of_bound (w.continuous.measurable.comp_aemeasurable hae).aestronglyMeasurable
    ‖w‖ (Eventually.of_forall fun _ => w.norm_coe_le_norm _)).indicator
    (measurableSet_physCapEventM b E s h K W)

theorem integrable_wTest_W (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ} (s a c : ℝ)
    (ha : 0 < a) (K : ℕ) :
    Integrable (fun ω => wTest a c ha K w (fun _ => transmissionProcess b E (fun _ => 0) W s ω))
      (growthPathLaw W b) :=
  Integrable.of_bound ((wTest a c ha K w).continuous.measurable.comp_aemeasurable
    (aemeasurable_tp hb hE1 hE2 W s)).aestronglyMeasurable _
    (Eventually.of_forall fun _ => (wTest a c ha K w).norm_coe_le_norm _)

theorem integrable_wTest_lim [IsFiniteMeasure P] {s : ℝ} (hμ : Measurable (μ s)) (a c : ℝ)
    (ha : 0 < a) (K : ℕ) : Integrable (fun ω => wTest a c ha K w (fun _ => μ s ω)) P :=
  Integrable.of_bound ((wTest a c ha K w).continuous.measurable.comp
    (Measurable.of_eval fun _ => hμ)).aestronglyMeasurable _
    (Eventually.of_forall fun _ => (wTest a c ha K w).norm_coe_le_norm _)

end BlockBand.SourceProcess.CapCond
