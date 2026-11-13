module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The stopped killing factor: a deterministic FTC

For continuous `f` and `c ∈ [0, ∞]`, the stopped killing exponent `I(s) = ∫_0^s f(v) 1{v⁺ < c} dv`
satisfies the fundamental theorem of calculus (`killExp_sub_eq`); the indicator `1{·⁺ < c}` is
antitone and right-continuous.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set intervalIntegral
open scoped NNReal ENNReal

/-- `1{v⁺ < c}`. -/
def killInd (c : WithTop ℝ≥0) (v : ℝ) : ℝ := if (v.toNNReal : WithTop ℝ≥0) < c then 1 else 0

theorem killInd_antitone (c : WithTop ℝ≥0) : Antitone (killInd c) := by
  intro a b hab
  unfold killInd
  have hm : (a.toNNReal : WithTop ℝ≥0) ≤ b.toNNReal :=
    WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hab)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_le_of_lt hm h1) h2
  · norm_num
  · exact le_rfl

theorem measurable_killInd (c : WithTop ℝ≥0) : Measurable (killInd c) :=
  (killInd_antitone c).measurable

theorem killInd_mem (c : WithTop ℝ≥0) (v : ℝ) : 0 ≤ killInd c v ∧ killInd c v ≤ 1 := by
  unfold killInd; split_ifs <;> norm_num

/-- `1{·⁺ < c}` is right-continuous. -/
theorem continuousWithinAt_killInd (c : WithTop ℝ≥0) (b : ℝ) :
    ContinuousWithinAt (killInd c) (Ioi b) b := by
  by_cases hb : (b.toNNReal : WithTop ℝ≥0) < c
  · have hev : ∀ᶠ v in 𝓝 b, (v.toNNReal : WithTop ℝ≥0) < c := by
      cases c with
      | top => exact Eventually.of_forall fun v => WithTop.coe_lt_top _
      | coe c₀ =>
        have hb' : b.toNNReal < c₀ := WithTop.coe_lt_coe.1 hb
        have := continuous_real_toNNReal.continuousAt.eventually (isOpen_Iio.mem_nhds hb')
        filter_upwards [this] with v hv
        exact WithTop.coe_lt_coe.2 hv
    refine (tendsto_const_nhds.congr' ?_).mono_left nhdsWithin_le_nhds
    filter_upwards [hev] with v hv
    unfold killInd
    split_ifs
    rfl
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    have : ¬ (v.toNNReal : WithTop ℝ≥0) < c := fun h =>
      hb (lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal (le_of_lt hv))) h)
    unfold killInd
    split_ifs
    rfl

variable {f : ℝ → ℝ}

theorem intervalIntegrable_killRate (hf : Continuous f) (c : WithTop ℝ≥0) (a b : ℝ) :
    IntervalIntegrable (fun v => f v * killInd c v) volume a b := by
  refine (hf.intervalIntegrable a b).mono_fun
    (hf.measurable.mul (measurable_killInd c)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  show ‖f v * killInd c v‖ ≤ ‖f v‖
  rw [norm_mul]
  have := killInd_mem c v
  rw [Real.norm_eq_abs (killInd c v), abs_of_nonneg this.1]
  exact mul_le_of_le_one_right (norm_nonneg _) this.2

/-- The stopped killing exponent `I(s) = ∫_0^s f(v) 1{v⁺ < c} dv`. -/
def killExp (f : ℝ → ℝ) (c : WithTop ℝ≥0) (s : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..s, f v * killInd c v

theorem continuous_killExp (hf : Continuous f) (c : WithTop ℝ≥0) : Continuous (killExp f c) :=
  continuous_primitive (fun a b => intervalIntegrable_killRate hf c a b) 0

/-- **FTC for the stopped killing factor.** -/
theorem killExp_sub_eq (hf : Continuous f) (c : WithTop ℝ≥0) {a b : ℝ} (hab : a ≤ b) :
    Real.exp (-killExp f c b) - Real.exp (-killExp f c a) =
      ∫ u in a..b, -(f u * killInd c u) * Real.exp (-killExp f c u) := by
  have hI := continuous_killExp hf c
  refine (integral_eq_sub_of_hasDeriv_right_of_le hab
    (Real.continuous_exp.comp hI.neg).continuousOn (fun s _ => ?_) ?_).symm
  · have hd : HasDerivWithinAt (killExp f c) (f s * killInd c s) (Ici s) s := by
      have := integral_hasDerivWithinAt_right (f := fun v => f v * killInd c v)
        (a := 0) (b := s) (s := Ici s) (t := Ioi s) (intervalIntegrable_killRate hf c 0 s)
        ((hf.measurable.mul (measurable_killInd c)).stronglyMeasurable.stronglyMeasurableAtFilter)
        ((hf.continuousAt.continuousWithinAt).mul (continuousWithinAt_killInd c s))
      exact this
    have := (hd.neg.exp).mono (Ioi_subset_Ici_self)
    convert this using 1
    · rfl
    · simp only [Pi.neg_apply]; ring
  · exact (intervalIntegrable_killRate hf c a b).neg.mul_continuousOn
      (Real.continuous_exp.comp hI.neg).continuousOn

end BlockBand.Transmission.LawDuality
