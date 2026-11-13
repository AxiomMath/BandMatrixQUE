module

public import BlockBand.SourceProcess.ComplexConstruct.Interface
public import BlockBand.SourceProcess.ComplexSourceLaw.MomentsLimit
public import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Tightness of the finite-width source-data laws from the raw tag moments

`complexSourceTight_of_raw : RawTagMoments → ComplexSourceTight`. The finite-width bound
`lintegral_sourceDataMoment_le` at `p = 1` (constant from `RawTagMoments` at margin
`min(2+E, 2-E)` and length bound `max(T,0)`) bounds `E Σ|entries|` for all large `W`. The sup norm
of the source data is at most `Σ|entries|`, so Markov gives `limsup_W μ_W{‖y‖ > r} ≤ B/r`, and
Mathlib's `isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt` concludes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.SourceProcess.ComplexSourceLaw
open scoped ENNReal

/-- The Borel structure of the source data (product topology). -/
instance borelSpace_sourceData (np : ℕ) : BorelSpace (SourceData np) :=
  inferInstanceAs (BorelSpace (Fin 4 → Fin np → Fin np → ℂ))

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_le_sourceDataMoment_one {np : ℕ} (y : SourceData np) :
    ‖y‖ ≤ sourceDataMoment 1 y := by
  have h0 := sourceDataMoment_nonneg 1 y
  refine (pi_norm_le_iff_of_nonneg h0).2 fun r => (Matrix.norm_le_iff h0).2 fun i j => ?_
  unfold sourceDataMoment
  simp only [Real.rpow_one]
  have hij : ‖y r i j‖ ≤ ∑ j', ‖y r i j'‖ :=
    Finset.single_le_sum (f := fun j' => ‖y r i j'‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)
  have hi : ∑ j', ‖y r i j'‖ ≤ ∑ i', ∑ j', ‖y r i' j'‖ :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖y r i' j'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hr : ∑ i', ∑ j', ‖y r i' j'‖ ≤ ∑ r', ∑ i', ∑ j', ‖y r' i' j'‖ :=
    Finset.single_le_sum (f := fun r' => ∑ i', ∑ j', ‖y r' i' j'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ r)
  linarith

instance isProbabilityMeasure_physLaw (b E T : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W : ℕ) :
    IsProbabilityMeasure (physLaw b E T τ m W) :=
  by unfold physLaw; infer_instance

/-- Markov at `p = 1`: `μ_W{‖y‖ > r} ≤ E Σ|entries| / r`. -/
theorem physLaw_norm_gt_le (b E T : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W : ℕ) {r : ℝ}
    (hr : 0 < r) : physLaw b E T τ m W {y | r < ‖y‖} ≤
      (∫⁻ x, ENNReal.ofReal (sourceDataMoment 1 (complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m x))
        ∂probedPathLaw W np b) / ENNReal.ofReal r := by
  have hX := measurable_complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m
  have hg : Measurable fun y : SourceData np => ENNReal.ofReal (sourceDataMoment 1 y) :=
    ENNReal.measurable_ofReal.comp (measurable_sourceDataMoment 1)
  have hsub : {y : SourceData np | r < ‖y‖} ⊆
      {y | ENNReal.ofReal r ≤ ENNReal.ofReal (sourceDataMoment 1 y)} := fun y hy =>
    ENNReal.ofReal_le_ofReal ((Set.mem_ofPred_eq ▸ hy).le.trans (norm_le_sourceDataMoment_one y))
  refine (measure_mono hsub).trans ?_
  unfold physLaw
  rw [Measure.map_apply hX (measurableSet_le measurable_const hg)]
  exact meas_ge_le_lintegral_div (hg.comp hX).aemeasurable (by simpa using hr)
    ENNReal.ofReal_ne_top

/-- **`ComplexSourceTight` from `RawTagMoments`.** -/
theorem complexSourceTight_of_raw (hR : RawTagMoments) : ComplexSourceTight := by
  intro b E np τ m T hD
  obtain ⟨hb0, hb1, hE0, hE1, -, -, hm, -⟩ := hD
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  obtain ⟨C, W₀, hC⟩ := hR b hb0 hb1 κ hκ (max T 0) 1 le_rfl
  have hη := Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE0 hE1
  set B := momentBound (etaZ b E) 1 C m
  have hB : B ≠ ⊤ := momentBound_ne_top _ _ _ _
  have hmom : ∀ W, W₀ ≤ W → ∫⁻ x, ENNReal.ofReal (sourceDataMoment 1
      (complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m x)) ∂probedPathLaw W np b ≤ B := fun W hW =>
    lintegral_sourceDataMoment_le b E hη _ τ m hm le_rfl
      (hC W hW E hEκ _ (floor_le_max_mul le_rfl))
  have hBo : BorelSpace (Fin 4 → Fin np → Fin np → ℂ) := inferInstance
  have hPr : ProperSpace (Fin 4 → Fin np → Fin np → ℂ) := inferInstance
  refine @isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt (SourceData np) _ _ hBo hPr
    (physLaw b E T τ m) (by intro W; exact (inferInstance : IsFiniteMeasure (physLaw b E T τ m W)))
    ?_
  have hlim : Tendsto (fun r : ℝ => B / ENNReal.ofReal r) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_div ENNReal.tendsto_ofReal_atTop (Or.inr hB)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop W₀] with W hW
  exact (physLaw_norm_gt_le b E T τ m W hr).trans (ENNReal.div_le_div_right (hmom W hW) _)

end BlockBand.SourceProcess.ComplexConstruct
