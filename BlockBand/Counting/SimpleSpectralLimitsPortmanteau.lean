module
public import BlockBand.Counting.SimpleSpectralLimitsTopology

/-!
# Two-point bounds pass to weak limits

The event that an open interval contains two spectral points is open in the vague topology
of marked configurations, so by the Portmanteau theorem a uniform bound on its probability
passes to every weak limit.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

def markedIntervalTestEncoding (a b : ℝ) (ξ : MarkedPointMeasure) : ℕ → ℝ :=
  fun n => ξ.spectral.coordinate (openIntervalApprox a b n)

theorem continuous_markedIntervalTestEncoding (a b : ℝ) :
    Continuous (markedIntervalTestEncoding a b) := by
  apply continuous_pi
  intro n
  exact (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate _).comp
    continuous_markedSpectralProjection

def twoPointEncodingEvent : Set (ℕ → ℝ) := {z | ∃ n, (1 : ℝ) < z n}

theorem isOpen_twoPointEncodingEvent : IsOpen twoPointEncodingEvent := by
  have he : twoPointEncodingEvent = ⋃ n : ℕ, {z : ℕ → ℝ | (1 : ℝ) < z n} := by
    ext z
    simp [twoPointEncodingEvent]
  rw [he]
  exact isOpen_iUnion fun n => isOpen_lt continuous_const (continuous_apply n)

theorem markedIntervalTestEncoding_preimage (a b : ℝ) :
    markedIntervalTestEncoding a b ⁻¹' twoPointEncodingEvent =
      {ξ : MarkedPointMeasure | (1 : ℝ≥0∞) < ξ.spectral.measure (Ioo a b)} := by
  ext ξ
  exact (vague_Ioo_twoPoint_iff_exists_approx ξ.spectral a b).symm

/-- Weak convergence of laws in the vague topology preserves a uniform bound on the
probability of the two-point interval event. -/
theorem marked_Ioo_twoPoint_le_of_weakLimit
    (laws : ℕ → ProbabilityMeasure MarkedPointMeasure) (μ : ProbabilityMeasure MarkedPointMeasure)
    (hlim : Tendsto laws atTop (𝓝 μ)) (a b : ℝ) (q : ℝ≥0∞)
    (hbound : ∀ j, (laws j : Measure MarkedPointMeasure)
      {ξ | (1 : ℝ≥0∞) < ξ.spectral.measure (Ioo a b)} ≤ q) :
    (μ : Measure MarkedPointMeasure) {ξ | (1 : ℝ≥0∞) < ξ.spectral.measure (Ioo a b)} ≤ q := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws μ hlim
    (continuous_markedIntervalTestEncoding a b)
  have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht isOpen_twoPointEncodingEvent
  have he (ν : ProbabilityMeasure MarkedPointMeasure) :
      (ν.map (markedIntervalTestEncoding a b) : Measure (ℕ → ℝ)) twoPointEncodingEvent =
      (ν : Measure MarkedPointMeasure) {ξ | (1 : ℝ≥0∞) < ξ.spectral.measure (Ioo a b)} := by
    change Measure.map (markedIntervalTestEncoding a b) (ν : Measure MarkedPointMeasure)
      twoPointEncodingEvent = _
    rw [Measure.map_apply (continuous_markedIntervalTestEncoding a b).measurable
      isOpen_twoPointEncodingEvent.measurableSet, markedIntervalTestEncoding_preimage]
  simp_rw [he] at hp
  apply hp.trans
  exact Filter.liminf_le_of_frequently_le' (Frequently.of_forall hbound)

end BlockBand.Counting
