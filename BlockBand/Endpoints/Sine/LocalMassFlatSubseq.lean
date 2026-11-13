module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Endpoints.Response.EdgeClockMoments
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Subsequential limits and the inverse moment of the rescaled clock

* `lmf_eventually_integral_le_of_subseqLimits`: for tight probability laws `ν_j` on `ℝ` and a
  bounded continuous `f`, if every subsequential limit `μ` has `∫ f dμ ≤ B`, then
  `∀ ε > 0`, eventually `∫ f dν_j ≤ B + ε` (Prokhorov, Mathlib
  `isCompact_closure_of_isTightMeasureSet`, sequential compactness of `ProbabilityMeasure ℝ`).
* `lmf_isTightSeq_rescaledClock`: tightness of `M_W = h*Yh/(nW)` from tightness of
  `T_W = h*Yh/W²` (`NegativeClockContract.tight`), since `M_W = T_W · W/n` and `W/n` is bounded.
* `lmf_invSqTest`, `lmf_integral_invSqTest_le`: `f_t` and `∫ f_t dμ ≤ ∫ x^{-2} dμ` when
  `μ(-∞,0] = 0`.
* `lmf_eventually_invSq_le`: the prelimit inverse moment of `M_W`, under the probed path law
  `probedClockLaw`.

The hypotheses are `NegativeClockContract` and `ClockSmallBallContract`, and the measurability of
the two clocks (stated as hypotheses).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers
open scoped BoundedContinuousFunction ENNReal

/-!
## Prelimit bounds from bounds on subsequential limits
-/

/-- For tight probability laws `ν_j` on `ℝ` and a bounded continuous `f`: if every
subsequential weak limit `μ` satisfies `∫ f dμ ≤ B`, then `∀ ε > 0`, eventually
`∫ f dν_j ≤ B + ε` (i.e. `limsup_j ∫ f dν_j ≤ B`). -/
theorem lmf_eventually_integral_le_of_subseqLimits {ν : ℕ → Measure ℝ}
    (hprob : ∀ j, IsProbabilityMeasure (ν j)) (htight : IsTightSeq ν) (f : ℝ →ᵇ ℝ) (B : ℝ)
    (hB : ∀ μ, IsSubsequentialLimit ν μ → ∫ x, f x ∂μ ≤ B) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∫ x, f x ∂ν j ≤ B + ε := by
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨φ, hφ, hφP⟩ :=
    Filter.extraction_of_frequently_atTop (hcon.mono fun j hj => lt_of_not_ge hj)
  let μs : ℕ → ProbabilityMeasure ℝ := fun j => ⟨ν (φ j), hprob _⟩
  have htS : IsTightMeasureSet
      {x | ∃ μ ∈ Set.range μs, ((μ : ProbabilityMeasure ℝ) : Measure ℝ) = x} := by
    apply isTightMeasureSet_of_tendsto_measure_norm_gt
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    obtain ⟨R, hR⟩ := htight (min δ 1).toReal
      (ENNReal.toReal_pos (lt_min hδ one_pos).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
        (min_le_right _ _)))
    filter_upwards [eventually_ge_atTop R] with r hr
    apply iSup₂_le
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    calc (ν (φ j)) {x | r < ‖x‖} ≤ ν (φ j) {x | R < |x|} :=
          measure_mono fun x hx => lt_of_le_of_lt hr (by simpa [Real.norm_eq_abs] using hx)
      _ ≤ ENNReal.ofReal (min δ 1).toReal := hR _
      _ ≤ δ := by
          rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
          exact min_le_left _ _
  have hcomp := isCompact_closure_of_isTightMeasureSet htS
  obtain ⟨μ, -, ψ, hψ, hlim⟩ := hcomp.isSeqCompact (fun j => subset_closure ⟨j, rfl⟩)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hlim
  have hsub : IsSubsequentialLimit ν (μ : Measure ℝ) :=
    ⟨inferInstance, φ ∘ ψ, hφ.comp hψ, fun g => hlim g⟩
  have h1 := hB _ hsub
  have h2 : B + ε ≤ ∫ x, f x ∂(μ : Measure ℝ) :=
    ge_of_tendsto (hlim f) (Eventually.of_forall fun j => (hφP (ψ j)).le)
  linarith

/-!
## Tightness of the rescaled clock
-/

/-- `M_W = T_W · (W/n)` pointwise (also for `n = 0`, by `x/0 = 0`). -/
theorem lmf_rescaledClock_eq (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ)
    (x : GrowthPath (s.W j) × (Fin 2 × Fin (s.W j) → ℂ)) :
    rescaledClock b s j x = scaledClock b s j x * ((s.W j : ℝ) / (s.n j : ℝ)) := by
  have hW : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  unfold rescaledClock scaledClock
  rcases Nat.eq_zero_or_pos (s.n j) with hn | hn
  · simp [hn]
  · have hn' : (0 : ℝ) < s.n j := by exact_mod_cast hn
    field_simp

/-- The ratio `W/n` is bounded along a clock sequence with `τ > 0`. -/
theorem lmf_exists_ratio_bound {τ E : ℝ} (hτ : 0 < τ) (s : ClockSequence τ E) :
    ∃ K : ℝ, 0 < K ∧ ∀ j, (s.W j : ℝ) / (s.n j : ℝ) ≤ K := by
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (s.ratio_tendsto.eventually_const_lt (half_lt_self hτ))
  have hnn : ∀ j, 0 ≤ (s.W j : ℝ) / (s.n j : ℝ) := fun j => by positivity
  refine ⟨∑ j ∈ Finset.range j₀, (s.W j : ℝ) / (s.n j : ℝ) + 2 / τ,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => hnn j) (by positivity), fun j => ?_⟩
  rcases lt_or_ge j j₀ with hj | hj
  · have := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_range.2 hj)
    have : 0 ≤ 2 / τ := by positivity
    linarith
  · have h := hj₀ j hj
    have hpos : 0 < (s.n j : ℝ) / (s.W j : ℝ) := lt_trans (half_pos hτ) h
    have hle : (s.W j : ℝ) / (s.n j : ℝ) ≤ 2 / τ := by
      rw [← inv_div, show (2 : ℝ) / τ = (τ / 2)⁻¹ by rw [inv_div]]
      exact inv_anti₀ (half_pos hτ) h.le
    have := Finset.sum_nonneg (s := Finset.range j₀) fun i _ => hnn i
    linarith

/-- Tightness of `M_W = h*Yh/(nW)` from tightness of `T_W = h*Yh/W²` (`τ > 0`). -/
theorem lmf_isTightSeq_rescaledClock (b : ℝ) {τ E : ℝ} (hτ : 0 < τ) (s : ClockSequence τ E)
    (hT : ∀ j, Measurable (scaledClock b s j)) (hM : ∀ j, Measurable (rescaledClock b s j))
    (htight : IsTightSeq (fun j => clockLaw (s.W j) b (scaledClock b s j))) :
    IsTightSeq (fun j => clockLaw (s.W j) b (rescaledClock b s j)) := by
  obtain ⟨K, hK, hKj⟩ := lmf_exists_ratio_bound hτ s
  intro ε hε
  obtain ⟨R, hR⟩ := htight ε hε
  refine ⟨max R 0 * K, fun j => ?_⟩
  have hmeas : MeasurableSet {x : ℝ | max R 0 * K < |x|} :=
    measurableSet_lt measurable_const measurable_abs
  have hmeas' : MeasurableSet {x : ℝ | R < |x|} := measurableSet_lt measurable_const measurable_abs
  refine le_trans ?_ (hR j)
  simp only [clockLaw]
  rw [Measure.map_apply (hM j) hmeas, Measure.map_apply (hT j) hmeas']
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
  rw [lmf_rescaledClock_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤
    (s.W j : ℝ) / (s.n j : ℝ))] at hx
  have h1 : |scaledClock b s j x| * ((s.W j : ℝ) / (s.n j : ℝ)) ≤ |scaledClock b s j x| * K :=
    mul_le_mul_of_nonneg_left (hKj j) (abs_nonneg _)
  have h2 : max R 0 < |scaledClock b s j x| := lt_of_mul_lt_mul_right (hx.trans_le h1) hK.le
  exact lt_of_le_of_lt (le_max_left _ _) h2

/-!
## The bounded inverse-square test
-/

/-- `f_t(x) = (max(x,t))^{-2}`, a bounded continuous function (bound `t^{-2}`). -/
def lmf_invSqTest (t : ℝ) (ht : 0 < t) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ((max x t) ^ 2)⁻¹)
    (Continuous.inv₀ (by fun_prop) fun x =>
      pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ht (le_max_right x t))))
    (t ^ 2)⁻¹ fun x => by
      have hpos : 0 < (max x t) ^ 2 := pow_pos (lt_of_lt_of_le ht (le_max_right x t)) 2
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
      exact inv_anti₀ (pow_pos ht 2) (pow_le_pow_left₀ ht.le (le_max_right x t) 2)

@[simp] theorem lmf_invSqTest_apply (t : ℝ) (ht : 0 < t) (x : ℝ) :
    lmf_invSqTest t ht x = ((max x t) ^ 2)⁻¹ := rfl

theorem lmf_invSqTest_nonneg (t : ℝ) (ht : 0 < t) (x : ℝ) : 0 ≤ lmf_invSqTest t ht x := by
  rw [lmf_invSqTest_apply]; positivity

/-- If `μ(-∞,0] = 0` and `∫ x^{-2} dμ ≤ C` (`C ≥ 0`), then `∫ f_t dμ ≤ C`. -/
theorem lmf_integral_invSqTest_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {C t : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (h0 : μ (Set.Iic 0) = 0)
    (hC : ∫⁻ x, ENNReal.ofReal (x ^ (-(2 : ℝ))) ∂μ ≤ ENNReal.ofReal C) :
    ∫ x, lmf_invSqTest t ht x ∂μ ≤ C := by
  have hpos : ∀ᵐ x ∂μ, 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
    simpa using hx
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (lmf_invSqTest_nonneg t ht))
    (lmf_invSqTest t ht).continuous.aestronglyMeasurable]
  have hle : ∫⁻ x, ENNReal.ofReal (lmf_invSqTest t ht x) ∂μ ≤ ENNReal.ofReal C := by
    refine le_trans (lintegral_mono_ae ?_) hC
    filter_upwards [hpos] with x hx
    apply ENNReal.ofReal_le_ofReal
    rw [lmf_invSqTest_apply, Real.rpow_neg hx.le, Real.rpow_two]
    exact inv_anti₀ (pow_pos hx 2) (pow_le_pow_left₀ hx.le (le_max_left x t) 2)
  calc (∫⁻ x, ENNReal.ofReal (lmf_invSqTest t ht x) ∂μ).toReal ≤ (ENNReal.ofReal C).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = C := ENNReal.toReal_ofReal hC0

/-!
## The prelimit inverse-moment bound of `M_W`
-/

/-- The standard circular Gaussian vector law of `CoareaPalm` is a probability measure. -/
theorem lmf_isProbabilityMeasure_circularVectorLaw (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw ι) := by
  unfold BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw
  infer_instance

theorem lmf_isProbabilityMeasure_probedClockLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (probedClockLaw W b) := by
  have := isProbabilityMeasure_growthPathLaw W b
  have := lmf_isProbabilityMeasure_circularVectorLaw (Fin 2 × Fin W)
  unfold probedClockLaw
  infer_instance

/-- Prelimit inverse moment of `M_W`, from `NegativeClockContract` and `ClockSmallBallContract`.
Fixed `0 < b < 1/2`, bulk `E`, `T₀ > 0`: there is `C₂ ≥ 0` such that for every `τ ∈ (0,T₀]`,
every clock sequence (energies `E_j → E`) whose clocks are measurable, every `t > 0` and `ε > 0`,
eventually `E f_t(M_W) ≤ C₂ + ε`, `f_t(x) = (max(x,t))^{-2}`, under `probedClockLaw`. -/
theorem lmf_eventually_invSq_le (hNeg : NegativeClockContract) (hSmall : ClockSmallBallContract)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ) (hE : -2 < E) (hE' : E < 2) (T₀ : ℝ)
    (hT₀ : 0 < T₀) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ s : ClockSequence τ E,
      (∀ j, Measurable (scaledClock b s j)) → (∀ j, Measurable (rescaledClock b s j)) →
      ∀ (t : ℝ) (ht : 0 < t), ∀ ε > 0, ∀ᶠ j in atTop,
        ∫ x, lmf_invSqTest t ht (rescaledClock b s j x) ∂probedClockLaw (s.W j) b ≤ C₂ + ε := by
  set β : ℝ := min b (1 / 2 - b) / 2 with hβ
  set κ : ℝ := (2 - |E|) / 2 with hκ
  have hβ0 : 0 < β := by rw [hβ]; exact half_pos (lt_min hb (by linarith))
  have hβ1 : β < 1 / 4 := by
    have : min b (1 / 2 - b) ≤ 1 / 4 := by
      rcases le_total b (1 / 4) with h | h
      · exact (min_le_left _ _).trans h
      · exact (min_le_right _ _).trans (by linarith)
    rw [hβ]; linarith
  have hEabs : |E| < 2 := abs_lt.2 ⟨hE, hE'⟩
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  obtain ⟨C, hC⟩ := hSmall β κ T₀ 2 hβ0 hβ1 hκ0 hT₀ two_pos
  refine ⟨max C 0, le_max_right _ _, fun τ hτ hτT s hT hM t ht ε hε => ?_⟩
  have hbβ : b ∈ Set.Icc β (1 / 2 - β) := by
    constructor
    · rw [hβ]; have := min_le_left b (1 / 2 - b); linarith
    · rw [hβ]; have := min_le_right b (1 / 2 - b); linarith
  have hlo : -2 + κ < E := by
    rw [hκ]; have := neg_abs_le E; linarith
  have hhi : E < 2 - κ := by
    rw [hκ]; have := le_abs_self E; linarith
  have hEκ : E ∈ bulkInterval κ := ⟨hlo.le, hhi.le⟩
  have hev : ∀ᶠ j in atTop, s.energy j ∈ bulkInterval κ :=
    s.energy_tendsto (Icc_mem_nhds hlo hhi)
  have hlim := (hC b hbβ E hEκ τ hτ hτT s hev).1
  have : ∀ W, IsProbabilityMeasure (probedClockLaw W b) :=
    fun W => lmf_isProbabilityMeasure_probedClockLaw W b
  have hprob : ∀ j, IsProbabilityMeasure (clockLaw (s.W j) b (rescaledClock b s j)) :=
    fun j => by unfold clockLaw; infer_instance
  have htight := lmf_isTightSeq_rescaledClock b hτ s hT hM (hNeg.tight b hb hb' E hE hE' τ hτ s)
  have key := lmf_eventually_integral_le_of_subseqLimits hprob htight (lmf_invSqTest t ht)
    (max C 0) (fun μ hμ => by
      have := hμ.1
      obtain ⟨h0, hμC⟩ := hlim μ hμ
      exact lmf_integral_invSqTest_le ht (le_max_right _ _) h0
        (hμC.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
    ε hε
  filter_upwards [key] with j hj
  rwa [clockLaw, integral_map (hM j).aemeasurable
    (lmf_invSqTest t ht).continuous.aestronglyMeasurable] at hj

end BlockBand.Endpoints
