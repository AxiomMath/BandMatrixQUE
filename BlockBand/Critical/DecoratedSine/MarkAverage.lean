module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The mark-averaged test `h(x) = -log ∫ e^{-f(x, g)} dγ(g)`

For a probability measure `γ` on the mark space and a nonnegative compactly supported continuous
test `f` on `ℝ × Y`, the mark average `∫ e^{-f(x, g)} dγ(g)` lies in `(0, 1]` and is continuous in
`x`, and `h = -log` of it is a nonnegative compactly supported continuous test on `ℝ`
(`markTest`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.DecoratedSine

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (γ : Measure Y) [IsProbabilityMeasure γ]

/-- The mark average `I(x) = ∫ e^{-f(x, g)} dγ(g)`. -/
def markAverage (f : ℝ × Y → ℝ) (x : ℝ) : ℝ :=
  ∫ g, Real.exp (-f (x, g)) ∂γ

variable {γ}

theorem integrable_exp_neg_mark {f : ℝ × Y → ℝ} (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (x : ℝ) :
    Integrable (fun g => Real.exp (-f (x, g))) γ := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun g => ?_)
  · exact (Real.continuous_exp.comp (hf.comp (Continuous.prodMk_right x)).neg).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    linarith [hf0 (x, g)]

theorem markAverage_pos {f : ℝ × Y → ℝ} (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (x : ℝ) :
    0 < markAverage γ f x := by
  rw [markAverage, integral_pos_iff_support_of_nonneg (fun g => (Real.exp_pos _).le)
    (integrable_exp_neg_mark hf hf0 x)]
  have : Function.support (fun g => Real.exp (-f (x, g))) = univ :=
    eq_univ_of_forall fun g => (Real.exp_pos _).ne'
  rw [this, measure_univ]
  exact one_pos

theorem markAverage_le_one {f : ℝ × Y → ℝ} (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (x : ℝ) :
    markAverage γ f x ≤ 1 := by
  rw [markAverage]
  calc ∫ g, Real.exp (-f (x, g)) ∂γ ≤ ∫ _g, (1 : ℝ) ∂γ :=
        integral_mono (integrable_exp_neg_mark hf hf0 x) (integrable_const 1)
          fun g => Real.exp_le_one_iff.mpr (by linarith [hf0 (x, g)])
    _ = 1 := by simp

theorem continuous_markAverage {f : ℝ × Y → ℝ} (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) :
    Continuous (markAverage γ f) := by
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (fun x => (integrable_exp_neg_mark hf hf0 x).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun g => ?_) (integrable_const 1)
    (Eventually.of_forall fun g => ?_)
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    linarith [hf0 (x, g)]
  · exact Real.continuous_exp.comp (hf.comp (Continuous.prodMk_left g)).neg

omit [TopologicalSpace Y] [OpensMeasurableSpace Y] in
theorem markAverage_eq_one {f : ℝ × Y → ℝ} {x : ℝ} (hx : ∀ g, f (x, g) = 0) :
    markAverage γ f x = 1 := by
  simp [markAverage, hx]

/-- `h(x) = -log ∫ e^{-f(x, g)} dγ(g)`. -/
def markTestFun (f : ℝ × Y → ℝ) (x : ℝ) : ℝ :=
  -Real.log (markAverage γ f x)

variable (γ) in
/-- The averaged test `h(x) = -log ∫ e^{-f(x, g)} dγ(g)` as a compactly supported continuous map,
for a nonnegative compactly supported continuous `f` on `ℝ × Y`. -/
def markTest (f : CompactlySupportedContinuousMap (ℝ × Y) ℝ) (hf0 : ∀ z, 0 ≤ f z) :
    CompactlySupportedContinuousMap ℝ ℝ where
  toFun := markTestFun (γ := γ) f
  continuous_toFun :=
    ((continuous_markAverage (γ := γ) (map_continuous f) hf0).log
      fun x => (markAverage_pos (map_continuous f) hf0 x).ne').neg
  hasCompactSupport' := by
    refine HasCompactSupport.intro (f.hasCompactSupport.image continuous_fst) fun x hx => ?_
    have h0 : ∀ g, f (x, g) = 0 := fun g =>
      image_eq_zero_of_notMem_tsupport fun hg => hx ⟨(x, g), hg, rfl⟩
    simp [markTestFun, markAverage_eq_one h0]

theorem markTest_apply (f : CompactlySupportedContinuousMap (ℝ × Y) ℝ) (hf0 : ∀ z, 0 ≤ f z)
    (x : ℝ) : markTest γ f hf0 x = -Real.log (markAverage γ f x) :=
  rfl

theorem markTest_nonneg (f : CompactlySupportedContinuousMap (ℝ × Y) ℝ) (hf0 : ∀ z, 0 ≤ f z)
    (x : ℝ) : 0 ≤ markTest γ f hf0 x := by
  rw [markTest_apply, neg_nonneg]
  exact Real.log_nonpos (markAverage_pos (map_continuous f) hf0 x).le
    (markAverage_le_one (map_continuous f) hf0 x)

theorem exp_neg_markTest (f : CompactlySupportedContinuousMap (ℝ × Y) ℝ) (hf0 : ∀ z, 0 ≤ f z)
    (x : ℝ) : Real.exp (-markTest γ f hf0 x) = markAverage γ f x := by
  rw [markTest_apply, neg_neg, Real.exp_log (markAverage_pos (map_continuous f) hf0 x)]

theorem markTest_eq_zero (f : CompactlySupportedContinuousMap (ℝ × Y) ℝ) (hf0 : ∀ z, 0 ≤ f z)
    {x : ℝ} (hx : ∀ g, f (x, g) = 0) : markTest γ f hf0 x = 0 := by
  simp [markTest_apply, markAverage_eq_one hx]

end BlockBand.Critical.DecoratedSine
