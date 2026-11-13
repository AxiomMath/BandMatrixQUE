module

public import BlockBand.SourceProcess.ComplexSplit.Interface

/-!
# Extraction of the entrance sequence, measurability of the initial state

Pure measure theory, used for the time-0 step of `complexFiniteUniqueness_of_segment`.
* `extractSeq`: a Giry-measurable left inverse of `seqTraceMeasure` on transmission sequences.
  For `x > 0` the count `N_x(ν) = ∫ 1{y ≥ x} y⁻¹ dν(y)` of `ν = Σ_i t_i δ_{t_i}` is
  `#{i : t_i ≥ x}`; for an antitone sequence `N_x ≥ i + 1 ⟺ t_i ≥ x`, so
  `t_i = sup {r ∈ ℚ, r > 0 : N_r ≥ i + 1}` (or `0`). This is the construction of
  `SourceProcessLaw.seqExtract`, reproved locally under local names.
* `measurable_seqTraceMeasure'`, `measurable_initialGram'`: measurability in the sequence.
* Local (non-global) Borel / pseudo-metrizable facts for Gram states and joint states.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUniqueSegment

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic
open scoped ENNReal NNReal

/-! ## Extraction of a transmission sequence from its trace measure -/

/-- The weight `1{y ≥ x} y⁻¹`. -/
def atomWeight (x : ℝ) (y : unitInterval) : ℝ≥0∞ :=
  Set.indicator {y : unitInterval | x ≤ (y : ℝ)} (fun y => ENNReal.ofReal (1 / (y : ℝ))) y

/-- The atom count `N_x(ν) = ∫ 1{y ≥ x} y⁻¹ dν(y)`. -/
def atomNumber (x : ℝ) (ν : Measure unitInterval) : ℝ≥0∞ := ∫⁻ y, atomWeight x y ∂ν

/-- The extraction `ext(ν)_i = sup {r ∈ ℚ, r > 0 : N_r(ν) ≥ i + 1}`. -/
def extractSeq (ν : Measure unitInterval) (i : ℕ) : ℝ :=
  (⨆ r : {r : ℚ // 0 < r}, Set.indicator {ν : Measure unitInterval |
    ((i + 1 : ℕ) : ℝ≥0∞) ≤ atomNumber (r : ℝ) ν} (fun _ => ENNReal.ofReal (r : ℝ)) ν).toReal

theorem measurable_atomWeight (x : ℝ) : Measurable (atomWeight x) := by
  refine Measurable.indicator ?_ (measurableSet_le measurable_const measurable_subtype_coe)
  exact ENNReal.measurable_ofReal.comp (measurable_const.div measurable_subtype_coe)

theorem measurable_extractSeq : Measurable extractSeq := by
  refine measurable_pi_iff.2 fun i => ENNReal.measurable_toReal.comp ?_
  refine Measurable.iSup fun r => measurable_const.indicator ?_
  exact measurableSet_le measurable_const (Measure.measurable_lintegral (measurable_atomWeight _))

theorem atomNumber_seqTraceMeasure {t : ℕ → ℝ} (ht : IsTransmissionSequence t) {x : ℝ}
    (hx : 0 < x) :
    atomNumber x (seqTraceMeasure t) = ∑' j, if x ≤ t j then (1 : ℝ≥0∞) else 0 := by
  simp only [atomNumber, seqTraceMeasure, lintegral_sum_measure, lintegral_smul_measure,
    lintegral_dirac]
  refine tsum_congr fun j => ?_
  have hu : ((toUnit (t j) : unitInterval) : ℝ) = t j := by
    simp [toUnit, Set.projIcc_of_mem _ ⟨(ht.2.1 j).1, (ht.2.1 j).2⟩]
  simp only [atomWeight, Set.indicator, Set.mem_ofPred_eq, hu, smul_eq_mul]
  split_ifs with h
  · have hpos : 0 < t j := hx.trans_le h
    rw [← ENNReal.ofReal_mul hpos.le, mul_one_div_cancel hpos.ne', ENNReal.ofReal_one]
  · simp

theorem succ_le_count_iff {t : ℕ → ℝ} (ht : Antitone t) (x : ℝ) (i : ℕ) :
    ((i + 1 : ℕ) : ℝ≥0∞) ≤ (∑' j, if x ≤ t j then (1 : ℝ≥0∞) else 0) ↔ x ≤ t i := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hzero : ∀ j ∉ Finset.range i, (if x ≤ t j then (1 : ℝ≥0∞) else 0) = 0 := by
      intro j hj
      have hij : i ≤ j := by simpa using hj
      rw [ite_eq_right_iff]
      intro hxj
      exact absurd ((ht hij).trans_lt hlt) (not_lt.2 hxj)
    rw [tsum_eq_sum hzero] at h
    have hle : (∑ j ∈ Finset.range i, if x ≤ t j then (1 : ℝ≥0∞) else 0) ≤ i := by
      calc (∑ j ∈ Finset.range i, if x ≤ t j then (1 : ℝ≥0∞) else 0)
          ≤ ∑ _j ∈ Finset.range i, (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun j _ => by split_ifs <;> simp
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

theorem iSup_posRat_ofReal (u : ℝ) :
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

/-- On transmission sequences, `extractSeq` inverts `seqTraceMeasure`. -/
theorem extractSeq_seqTraceMeasure {t : ℕ → ℝ} (ht : IsTransmissionSequence t) :
    extractSeq (seqTraceMeasure t) = t := by
  funext i
  have key : ∀ r : {r : ℚ // 0 < r}, Set.indicator {ν : Measure unitInterval |
      ((i + 1 : ℕ) : ℝ≥0∞) ≤ atomNumber (r : ℝ) ν} (fun _ => ENNReal.ofReal (r : ℝ))
        (seqTraceMeasure t) = if (r : ℝ) ≤ t i then ENNReal.ofReal (r : ℝ) else 0 := by
    intro r
    have hr : (0 : ℝ) < r := by exact_mod_cast r.2
    simp only [Set.indicator, Set.mem_ofPred_eq, atomNumber_seqTraceMeasure ht hr,
      succ_le_count_iff ht.1]
  simp only [extractSeq, key, iSup_posRat_ofReal, ENNReal.toReal_ofReal (ht.2.1 i).1]

/-- The trace measure depends measurably on the sequence (Giry σ-algebra). -/
theorem measurable_seqTraceMeasure' : Measurable seqTraceMeasure := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hu : Measurable toUnit :=
    (continuous_projIcc : Continuous (Set.projIcc (0 : ℝ) 1 zero_le_one)).measurable
  have : (fun t : ℕ → ℝ => seqTraceMeasure t A) =
      fun t => ∑' i, ENNReal.ofReal (t i) * A.indicator 1 (toUnit (t i)) := by
    funext t
    simp only [seqTraceMeasure, Measure.sum_apply _ hA, Measure.smul_apply,
      Measure.dirac_apply' _ hA, smul_eq_mul]
  rw [this]
  exact Measurable.tsum fun i => (ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).mul
    ((measurable_one.indicator hA).comp (hu.comp (measurable_pi_apply i)))

/-! ## Borel structure on the joint state -/

section Borel

variable {c π : Type} [Fintype c] [Fintype π]

theorem matrix_pseudoMetrizable :
    TopologicalSpace.PseudoMetrizableSpace (Matrix c π ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (c → π → ℂ))

theorem matrix_secondCountable : SecondCountableTopology (Matrix c π ℂ) :=
  inferInstanceAs (SecondCountableTopology (c → π → ℂ))

attribute [local instance] matrix_pseudoMetrizable matrix_secondCountable

theorem jointState_borel : BorelSpace (GramState c × Matrix π π ℂ) := Prod.borelSpace

theorem jointState_pseudoMetrizable :
    TopologicalSpace.PseudoMetrizableSpace (GramState c × Matrix π π ℂ) := inferInstance

theorem jointState_secondCountable :
    SecondCountableTopology (GramState c × Matrix π π ℂ) := inferInstance

theorem gramState_borel' : BorelSpace (GramState c) := Prod.borelSpace

theorem gramState_pseudoMetrizable :
    TopologicalSpace.PseudoMetrizableSpace (GramState c) := inferInstance

end Borel

/-! ## Measurability of the initial Gram state -/

theorem continuous_gramPair' {ι c : Type} [Fintype ι] (P : Matrix ι ι ℂ) :
    Continuous fun V : Matrix ι c ℂ => gramPair P V := by
  unfold gramPair BlockBand.SourceProcess.sourceGram BlockBand.SourceProcess.nearGram
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_id.matrix_conjTranspose).matrix_mul continuous_id
  · exact ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
      continuous_id

theorem measurable_modeVector_apply' (σ x : Fin 2) :
    Measurable fun r : ℝ => modeVector r σ x := by
  unfold modeVector
  split_ifs
  · fin_cases x <;> simp <;> fun_prop
  · fin_cases x <;> simp <;> fun_prop

theorem measurable_initialFrame' (K : ℕ) (π : Type) (h : ℝ) :
    Measurable fun t : ℕ → ℝ => initialFrame K π t h := by
  refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun col => ?_
  rcases col with ⟨k, σ⟩ | _
  · simp only [initialFrame]
    by_cases hx : x.1 = k
    · simp only [hx, true_and]
      refine Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply _)) ?_
        measurable_const
      exact (Complex.measurable_ofReal.comp ((measurable_pi_apply _).pow_const _)).mul
        ((measurable_modeVector_apply' σ x.2).comp (measurable_pi_apply _))
    · simp [hx]
  · simp [initialFrame]

theorem measurable_initialGram' (K : ℕ) (π : Type) [Fintype π] (h : ℝ) :
    Measurable fun t : ℕ → ℝ => initialGram K π t h := by
  have : BorelSpace (Matrix (Fin K × Fin 2) (SrcCol K π) ℂ) := inferInstance
  have : BorelSpace (GramState (SrcCol K π)) := gramState_borel'
  exact (continuous_gramPair' _).measurable.comp (measurable_initialFrame' K π h)

end BlockBand.SourceProcess.ComplexUniqueSegment
