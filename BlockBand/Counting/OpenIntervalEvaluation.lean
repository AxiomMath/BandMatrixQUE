module
public import BlockBand.Model.Construction.VagueTranslation
public import Mathlib.MeasureTheory.Integral.Regular
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Open-interval mass evaluation for vague point measures

The mass of a bounded open interval is the supremum of integrals of compactly supported
continuous tests below its indicator.  Hence open-interval mass superlevel sets are open
in the vague topology, open-interval mass evaluation is Borel measurable, and a two-point
event in an open interval is witnessed by a countable family of compact tests.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-- A function vanishing outside a bounded open interval has compact support. -/
theorem hasCompactSupport_of_zero_outside_Ioo (a b : ℝ) (f : ℝ → ℝ)
    (hz : EqOn f 0 (Ioo a b)ᶜ) : HasCompactSupport f := by
  apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport f)
  apply closure_minimal
  · intro x hx
    by_contra hn
    have hxout : x ∈ (Ioo a b)ᶜ := fun hi => hn (Ioo_subset_Icc_self hi)
    exact hx (hz hxout)
  · exact isClosed_Icc

/-- Local finiteness and regularity express open mass through compactly supported tests. -/
theorem vague_Ioo_mass_eq_iSup_integral (ξ : VaguePointMeasure ℝ) (a b : ℝ) :
    ξ.measure (Ioo a b) =
      ⨆ (f : ℝ → ℝ) (_ : Continuous f) (_ : EqOn f 0 (Ioo a b)ᶜ)
        (_ : 0 ≤ f) (_ : f ≤ 1), ENNReal.ofReal (∫ x, f x ∂ξ.measure) := by
  let μ := ξ.measure.restrict (Icc a b)
  have : IsFiniteMeasure μ := ⟨by
    change ξ.measure.restrict (Icc a b) univ < ∞
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact ξ.finite_on_compact _ isCompact_Icc⟩
  have hm : μ (Ioo a b) = ξ.measure (Ioo a b) := by
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Icc_self]
  rw [← hm, isOpen_Ioo.measure_eq_biSup_integral_continuous μ]
  congr 1
  funext f
  congr 1
  funext hf
  congr 1
  funext hz
  congr 1
  funext hnn
  congr 1
  funext hle
  congr 1
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    hz (fun hi => hx (Ioo_subset_Icc_self hi))

/-- Every strict open-interval mass superlevel event is open in ordinary vague topology. -/
theorem isOpen_vague_Ioo_mass_gt (a b : ℝ) (r : ℝ≥0∞) :
    IsOpen {ξ : VaguePointMeasure ℝ | r < ξ.measure (Ioo a b)} := by
  have heq : {ξ : VaguePointMeasure ℝ | r < ξ.measure (Ioo a b)} =
      ⋃ (f : ℝ → ℝ) (hf : Continuous f) (hz : EqOn f 0 (Ioo a b)ᶜ)
        (_ : 0 ≤ f) (_ : f ≤ 1),
        {ξ : VaguePointMeasure ℝ | r < ENNReal.ofReal (ξ.coordinate
          ⟨⟨f, hf⟩, hasCompactSupport_of_zero_outside_Ioo a b f hz⟩)} := by
    ext ξ
    simp only [mem_ofPred_eq, mem_iUnion]
    rw [vague_Ioo_mass_eq_iSup_integral]
    simp only [lt_iSup_iff]
    rfl
  rw [heq]
  exact isOpen_iUnion fun f => isOpen_iUnion fun hf => isOpen_iUnion fun hz =>
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_lt continuous_const (ENNReal.continuous_ofReal.comp
    (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate _))

/-- Borel open-interval mass superlevel events, including the two-point event. -/
theorem measurableSet_vague_Ioo_mass_gt (a b : ℝ) (r : ℝ≥0∞) :
    MeasurableSet {ξ : VaguePointMeasure ℝ | r < ξ.measure (Ioo a b)} :=
  (isOpen_vague_Ioo_mass_gt a b r).measurableSet

/-- Open-interval mass evaluation is Borel measurable for the vague topology. -/
theorem measurable_vague_Ioo_mass (a b : ℝ) :
    Measurable (fun ξ : VaguePointMeasure ℝ => ξ.measure (Ioo a b)) :=
  measurable_of_Ioi fun r => measurableSet_vague_Ioo_mass_gt a b r

/-- Countable compact continuous approximants to an open-interval indicator. -/
def openIntervalApprox (a b : ℝ) (n : ℕ) : CompactlySupportedContinuousMap ℝ ℝ where
  toFun := fun x => 1 - ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n x : ℝ)
  continuous_toFun := continuous_const.sub (NNReal.continuous_coe.comp
    ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n).continuous)
  hasCompactSupport' := hasCompactSupport_of_zero_outside_Ioo a b _ (by
    intro x hx
    change 1 - ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n x : ℝ) = 0
    rw [HasOuterApproxClosed.apprSeq_apply_eq_one _ n hx]
    simp)

theorem openIntervalApprox_range (a b : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ openIntervalApprox a b n x ∧ openIntervalApprox a b n x ≤ 1 := by
  have h : ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n x : ℝ) ≤ 1 :=
    by exact_mod_cast (HasOuterApproxClosed.apprSeq_apply_le_one
      (isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl n x)
  have h0 : (0 : ℝ) ≤ ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n x : ℝ) :=
    NNReal.coe_nonneg _
  change (0 : ℝ) ≤ 1 - ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n x : ℝ) ∧
    1 - ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n x : ℝ) ≤ 1
  constructor <;> linarith

theorem openIntervalApprox_zero (a b : ℝ) (n : ℕ) :
    EqOn (openIntervalApprox a b n) 0 (Ioo a b)ᶜ := by
  intro x hx
  change 1 - ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n x : ℝ) = 0
  rw [HasOuterApproxClosed.apprSeq_apply_eq_one _ n hx]
  simp

theorem tendsto_openIntervalApprox (a b x : ℝ) :
    Tendsto (fun n => openIntervalApprox a b n x) atTop
      (𝓝 ((Ioo a b).indicator (fun _ => (1 : ℝ)) x)) := by
  have h := (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq
    (isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl)) x
  have hc := (NNReal.continuous_coe.tendsto _).comp h
  have hd := (tendsto_const_nhds (x := (1 : ℝ))).sub hc
  by_cases hx : x ∈ Ioo a b
  · simpa [openIntervalApprox, hx, Function.comp_def] using hd
  · simpa [openIntervalApprox, hx, Function.comp_def] using hd

/-- Dominated convergence for the countable compact tests. -/
theorem tendsto_integral_openIntervalApprox (ξ : VaguePointMeasure ℝ) (a b : ℝ) :
    Tendsto (fun n => ξ.coordinate (openIntervalApprox a b n)) atTop
      (𝓝 (ξ.measure.real (Ioo a b))) := by
  let μ := ξ.measure.restrict (Icc a b)
  have : IsFiniteMeasure μ := ⟨by
    change ξ.measure.restrict (Icc a b) univ < ∞
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact ξ.finite_on_compact _ isCompact_Icc⟩
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => openIntervalApprox a b n x)
    (f := (Ioo a b).indicator (fun _ => (1 : ℝ))) (fun _ => (1 : ℝ))
    (fun n => (show Continuous (fun x => openIntervalApprox a b n x) from
      (openIntervalApprox a b n).continuous).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (openIntervalApprox_range a b n x).1]
      exact (openIntervalApprox_range a b n x).2)
    (Eventually.of_forall (tendsto_openIntervalApprox a b))
  have heq (n : ℕ) : (∫ x, openIntervalApprox a b n x ∂μ) =
      ξ.coordinate (openIntervalApprox a b n) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      openIntervalApprox_zero a b n (fun hi => hx (Ioo_subset_Icc_self hi))
  have hm : μ.real (Ioo a b) = ξ.measure.real (Ioo a b) := by
    unfold Measure.real
    congr 1
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Icc_self]
  have hi : (∫ x, (Ioo a b).indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real (Ioo a b) := by
    rw [integral_indicator measurableSet_Ioo]
    simp
  simpa only [heq, hi, hm] using h

/-- Each compact indicator approximant is bounded by the interval mass. -/
theorem integral_openIntervalApprox_le_mass (ξ : VaguePointMeasure ℝ) (a b : ℝ) (n : ℕ) :
    ξ.coordinate (openIntervalApprox a b n) ≤ ξ.measure.real (Ioo a b) := by
  have hf : ξ.measure (Ioo a b) < ∞ :=
    lt_of_le_of_lt (measure_mono Ioo_subset_Icc_self) (ξ.finite_on_compact _ isCompact_Icc)
  have hn : 0 ≤ ξ.coordinate (openIntervalApprox a b n) :=
    integral_nonneg fun x => (openIntervalApprox_range a b n x).1
  have h := integral_le_measure (μ := ξ.measure)
    (fun x (_ : x ∈ Ioo a b) => (openIntervalApprox_range a b n x).2)
    (fun x hx => (openIntervalApprox_zero a b n hx).le)
  have hr := ENNReal.toReal_mono hf.ne h
  change (ENNReal.ofReal (ξ.coordinate (openIntervalApprox a b n))).toReal ≤
    ξ.measure.real (Ioo a b) at hr
  rw [ENNReal.toReal_ofReal hn] at hr
  exact hr

/-- A strict two-point interval event is exactly a countable compact-test witness event. -/
theorem vague_Ioo_twoPoint_iff_exists_approx (ξ : VaguePointMeasure ℝ) (a b : ℝ) :
    (1 : ℝ≥0∞) < ξ.measure (Ioo a b) ↔
      ∃ n : ℕ, (1 : ℝ) < ξ.coordinate (openIntervalApprox a b n) := by
  have hf : ξ.measure (Ioo a b) < ∞ :=
    lt_of_le_of_lt (measure_mono Ioo_subset_Icc_self) (ξ.finite_on_compact _ isCompact_Icc)
  have he : (1 : ℝ) < ξ.measure.real (Ioo a b) ↔ (1 : ℝ≥0∞) < ξ.measure (Ioo a b) := by
    simpa only [ENNReal.toReal_one, Measure.real] using
      (ENNReal.toReal_lt_toReal (a := (1 : ℝ≥0∞)) (b := ξ.measure (Ioo a b)) (by simp) hf.ne)
  constructor
  · intro h
    have hev : ∀ᶠ n in atTop, (1 : ℝ) < ξ.coordinate (openIntervalApprox a b n) :=
      (tendsto_integral_openIntervalApprox ξ a b) (Ioi_mem_nhds (he.mpr h))
    exact hev.exists
  · rintro ⟨n, hn⟩
    exact he.mp (hn.trans_le (integral_openIntervalApprox_le_mass ξ a b n))

end BlockBand.Counting
