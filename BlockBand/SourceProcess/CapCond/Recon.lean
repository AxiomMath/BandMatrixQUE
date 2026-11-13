module

public import BlockBand.SourceProcess.CapCond.Count

/-!
# The transmission sequence from smoothed counts

The smoothed counts `smCount a c ν = ∫ cutWeight a c dν` (`0 < a < c`) are continuous in `ν` for
the weak topology (`continuous_smCount`), unlike `seqExtract`. They determine the transmission
sequence of a trace measure: `countExt C k = sup {a ∈ ℚ : ∃ c ∈ ℚ, 0 < a < c, k < C(a,c)}` is a
measurable function of the countable family `C`, and
`countExt (smCount · · ν) = t` when `ν = Σ_i t_i δ_{t_i}` (`countExt_smCount`). Hence a joint
limit that carries the smoothed counts of the entrance carries its transmission sequence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw
open scoped ENNReal

/-- The smoothed count `∫ cutWeight a c dν`. -/
def smCount (a c : ℝ) (ν : FiniteMeasure unitInterval) : ℝ :=
  ∫ y, cutWeight a c y ∂(ν : Measure unitInterval)

theorem continuous_smCount {a : ℝ} (ha : 0 < a) (c : ℝ) : Continuous (smCount a c) :=
  FiniteMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact ⟨cutWeight a c, continuous_cutWeight ha c⟩)

/-- Admissible rational threshold pairs. -/
abbrev RatPair := {r : ℚ × ℚ // 0 < r.1 ∧ r.1 < r.2}

/-- The sequence reconstructed from a family of smoothed counts. -/
def countExt (C : RatPair → ℝ) (k : ℕ) : ℝ :=
  (⨆ r : RatPair, Set.indicator {C : RatPair → ℝ | (k : ℝ) < C r}
    (fun _ => ENNReal.ofReal (r.1.1 : ℝ)) C).toReal

theorem measurable_countExt : Measurable countExt := by
  refine measurable_pi_iff.2 fun k => ENNReal.measurable_toReal.comp ?_
  exact Measurable.iSup fun r => measurable_const.indicator
    (measurableSet_lt measurable_const (measurable_pi_apply r))

/-- `c ≤ t_k ⟹ k + 1 ≤ smCount a c ν`. -/
theorem le_smCount (ν : FiniteMeasure unitInterval) {t : ℕ → ℝ}
    (hν : (ν : Measure unitInterval) = seqTraceMeasure t) (ht : IsTransmissionSequence t)
    {a c : ℝ} (ha : 0 < a) (hac : a < c) {k : ℕ} (hk : c ≤ t k) :
    (k : ℝ) + 1 ≤ smCount a c ν := by
  have hcount : ((k + 1 : ℕ) : ℝ≥0∞) ≤ atomCount c (ν : Measure unitInterval) := by
    rw [hν, atomCount_seqTraceMeasure ht (ha.trans hac)]
    exact (count_ge_iff ht.1 c k).2 hk
  have hle := hcount.trans (lintegral_mono fun y => countWeight_le_cutWeight hac y)
  have hfin : ∫⁻ y, ENNReal.ofReal (cutWeight a c y) ∂(ν : Measure unitInterval) ≠ ∞ := by
    have hb : ∀ y, ENNReal.ofReal (cutWeight a c y) ≤ ENNReal.ofReal (1 / a) := fun y =>
      (cutWeight_le_countWeight ha hac y).trans (by
        unfold countWeight
        by_cases hy : a ≤ (y : ℝ)
        · rw [Set.indicator_of_mem (show y ∈ {y : unitInterval | a ≤ (y : ℝ)} from hy)]
          exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le ha hy)
        · rw [Set.indicator_of_notMem (show y ∉ {y : unitInterval | a ≤ (y : ℝ)} from hy)]
          exact bot_le)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hb)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [smCount, integral_cutWeight_eq ν ha c]
  have := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_natCast] at this
  push_cast at this
  exact this

theorem countExt_smCount (ν : FiniteMeasure unitInterval) {t : ℕ → ℝ}
    (hν : (ν : Measure unitInterval) = seqTraceMeasure t) (ht : IsTransmissionSequence t) :
    countExt (fun r => smCount r.1.1 r.1.2 ν) = t := by
  funext k
  have key : (⨆ r : RatPair, Set.indicator {C : RatPair → ℝ | (k : ℝ) < C r}
      (fun _ => ENNReal.ofReal (r.1.1 : ℝ)) (fun r => smCount r.1.1 r.1.2 ν)) =
      ENNReal.ofReal (t k) := by
    refine le_antisymm (iSup_le fun r => ?_) ?_
    · have ha : (0 : ℝ) < r.1.1 := by exact_mod_cast r.2.1
      have hac : (r.1.1 : ℝ) < r.1.2 := by exact_mod_cast r.2.2
      simp only [Set.indicator, Set.mem_ofPred_eq]
      split_ifs with hC
      · refine ENNReal.ofReal_le_ofReal (not_lt.1 fun hlt => ?_)
        have := integral_cutWeight_le ν hν ht ha hac hlt
        exact absurd hC (not_lt.2 this)
      · exact bot_le
    · refine le_of_forall_lt fun x hx => ?_
      have hxfin : x ≠ ⊤ := ne_top_of_lt hx
      have hxt : x.toReal < t k := by
        rw [← ENNReal.ofReal_toReal hxfin] at hx
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).1 hx
      obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hxt
      obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn ha2
      have ha0 : (0 : ℝ) < a := ENNReal.toReal_nonneg.trans_lt ha1
      have hr : 0 < a ∧ a < c := ⟨by exact_mod_cast ha0, by exact_mod_cast hc1⟩
      refine lt_of_lt_of_le ?_ (le_iSup _ (⟨(a, c), hr⟩ : RatPair))
      have hC := le_smCount ν hν ht ha0 hc1 hc2.le
      simp only [Set.indicator, Set.mem_ofPred_eq]
      rw [ite_eq_left (show (k : ℝ) < smCount a c ν by linarith)]
      rw [← ENNReal.ofReal_toReal hxfin]
      exact (ENNReal.ofReal_lt_ofReal_iff ha0).2 ha1
  simp only [countExt, key, ENNReal.toReal_ofReal (ht.2.1 k).1]

end BlockBand.SourceProcess.CapCond
