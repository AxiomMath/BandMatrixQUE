module

public import BlockBand.SourceProcess.SourceProcessLaw.Interface

/-!
# `SeqExtraction`: a measurable inverse of `seqTraceMeasure` on transmission sequences

For `x > 0` the count `N_x(ν) = ∫ 1{y ≥ x} y⁻¹ dν(y)` of a trace measure `ν = Σ_i t_i δ_{t_i}`
is `#{i : t_i ≥ x}` (each atom of mass `t_i` at `t_i` counts once). For an antitone sequence,
`N_x ≥ i + 1 ⟺ t_i ≥ x`, so `t_i = sup {r ∈ ℚ, r > 0 : N_r ≥ i + 1}` (or `0`). Each `N_r` is
Giry-measurable, and the supremum is countable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

open MeasureTheory Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal

/-- The weight `1{y ≥ x} y⁻¹`. -/
def countWeight (x : ℝ) (y : unitInterval) : ℝ≥0∞ :=
  Set.indicator {y : unitInterval | x ≤ (y : ℝ)} (fun y => ENNReal.ofReal (1 / (y : ℝ))) y

/-- The atom count `N_x(ν) = ∫ 1{y ≥ x} y⁻¹ dν(y)`. -/
def atomCount (x : ℝ) (ν : Measure unitInterval) : ℝ≥0∞ := ∫⁻ y, countWeight x y ∂ν

/-- The extraction `ext(ν)_i = sup {r ∈ ℚ, r > 0 : N_r(ν) ≥ i + 1}`. -/
def seqExtract (ν : Measure unitInterval) (i : ℕ) : ℝ :=
  (⨆ r : {r : ℚ // 0 < r}, Set.indicator {ν : Measure unitInterval |
    ((i + 1 : ℕ) : ℝ≥0∞) ≤ atomCount (r : ℝ) ν} (fun _ => ENNReal.ofReal (r : ℝ)) ν).toReal

theorem measurable_countWeight (x : ℝ) : Measurable (countWeight x) := by
  refine Measurable.indicator ?_ (measurableSet_le measurable_const measurable_subtype_coe)
  exact ENNReal.measurable_ofReal.comp (measurable_const.div measurable_subtype_coe)

theorem measurable_seqExtract : Measurable seqExtract := by
  refine measurable_pi_iff.2 fun i => ENNReal.measurable_toReal.comp ?_
  refine Measurable.iSup fun r => measurable_const.indicator ?_
  exact measurableSet_le measurable_const (Measure.measurable_lintegral (measurable_countWeight _))

theorem atomCount_seqTraceMeasure {t : ℕ → ℝ} (ht : IsTransmissionSequence t) {x : ℝ}
    (hx : 0 < x) :
    atomCount x (seqTraceMeasure t) = ∑' j, if x ≤ t j then (1 : ℝ≥0∞) else 0 := by
  simp only [atomCount, seqTraceMeasure, lintegral_sum_measure, lintegral_smul_measure,
    lintegral_dirac]
  refine tsum_congr fun j => ?_
  have hu : ((toUnit (t j) : unitInterval) : ℝ) = t j := by
    simp [toUnit, Set.projIcc_of_mem _ ⟨(ht.2.1 j).1, (ht.2.1 j).2⟩]
  simp only [countWeight, Set.indicator, Set.mem_ofPred_eq, hu, smul_eq_mul]
  split_ifs with h
  · have hpos : 0 < t j := hx.trans_le h
    rw [← ENNReal.ofReal_mul hpos.le, mul_one_div_cancel hpos.ne', ENNReal.ofReal_one]
  · simp

theorem count_ge_iff {t : ℕ → ℝ} (ht : Antitone t) (x : ℝ) (i : ℕ) :
    ((i + 1 : ℕ) : ℝ≥0∞) ≤ (∑' j, if x ≤ t j then (1 : ℝ≥0∞) else 0) ↔ x ≤ t i := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hzero : ∀ j ∉ Finset.range i, (if x ≤ t j then (1 : ℝ≥0∞) else 0) = 0 := by
      intro j hj
      have hij : i ≤ j := by simpa using hj
      rw [ite_eq_right (not_le.2 ((ht hij).trans_lt hlt))]
    rw [tsum_eq_sum hzero] at h
    have hle : (∑ j ∈ Finset.range i, if x ≤ t j then (1 : ℝ≥0∞) else 0) ≤ i := by
      calc (∑ j ∈ Finset.range i, if x ≤ t j then (1 : ℝ≥0∞) else 0)
          ≤ ∑ _j ∈ Finset.range i, (1 : ℝ≥0∞) := Finset.sum_le_sum fun j _ => by split_ifs <;> simp
        _ = i := by simp
    have := h.trans hle
    norm_cast at this
    omega
  · intro h
    calc ((i + 1 : ℕ) : ℝ≥0∞)
        = ∑ j ∈ Finset.range (i + 1), (if x ≤ t j then (1 : ℝ≥0∞) else 0) := by
          rw [Finset.sum_congr rfl fun j hj => ite_eq_left (h.trans (ht (Nat.lt_succ_iff.1
            (Finset.mem_range.1 hj))))]
          simp
      _ ≤ _ := ENNReal.sum_le_tsum _

theorem iSup_rat_ofReal (u : ℝ) :
    (⨆ r : {r : ℚ // 0 < r}, if (r : ℝ) ≤ u then ENNReal.ofReal (r : ℝ) else 0) =
      ENNReal.ofReal u := by
  refine le_antisymm (iSup_le fun r => ?_) ?_
  · split_ifs with h
    · exact ENNReal.ofReal_le_ofReal h
    · exact bot_le
  · refine le_of_forall_lt fun c hc => ?_
    have hcfin : c ≠ ⊤ := ne_top_of_lt hc
    have hcu : c.toReal < u := by
      rw [← ENNReal.ofReal_toReal hcfin] at hc
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).1 hc
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hcu
    have hr0 : (0 : ℝ) < r := ENNReal.toReal_nonneg.trans_lt hr1
    refine lt_of_lt_of_le ?_ (le_iSup _ ⟨r, by exact_mod_cast hr0⟩)
    simp only [ite_eq_left hr2.le]
    rw [← ENNReal.ofReal_toReal hcfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).2 hr1

theorem seqExtract_seqTraceMeasure {t : ℕ → ℝ} (ht : IsTransmissionSequence t) :
    seqExtract (seqTraceMeasure t) = t := by
  funext i
  have key : ∀ r : {r : ℚ // 0 < r}, Set.indicator {ν : Measure unitInterval |
      ((i + 1 : ℕ) : ℝ≥0∞) ≤ atomCount (r : ℝ) ν} (fun _ => ENNReal.ofReal (r : ℝ))
        (seqTraceMeasure t) = if (r : ℝ) ≤ t i then ENNReal.ofReal (r : ℝ) else 0 := by
    intro r
    have hr : (0 : ℝ) < r := by exact_mod_cast r.2
    simp only [Set.indicator, Set.mem_ofPred_eq, atomCount_seqTraceMeasure ht hr,
      count_ge_iff ht.1]
  simp only [seqExtract, key, iSup_rat_ofReal, ENNReal.toReal_ofReal (ht.2.1 i).1]

/-- **`SeqExtraction` holds.** -/
theorem seqExtraction_holds : SeqExtraction :=
  ⟨seqExtract, measurable_seqExtract, fun _ ht => seqExtract_seqTraceMeasure ht⟩

end BlockBand.SourceProcess.SourceProcessLaw
