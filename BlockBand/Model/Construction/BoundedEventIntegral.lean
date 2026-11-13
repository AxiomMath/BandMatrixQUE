module
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Event bounds imply bounded-test bounds

If two probability measures differ by at most `C` on every measurable set, then the integrals of
a measurable test function bounded by `M` differ by at most `M C` (nonnegative tests, by the layer
cake formula) or `2 M C` (signed tests).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

theorem probability_tail_le_one (μ : Measure X) [IsProbabilityMeasure μ] (B : Set X) :
    0 ≤ μ.real B ∧ μ.real B ≤ 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · have h : μ B ≤ 1 := by simpa using (measure_mono (subset_univ B) : μ B ≤ μ univ)
    simpa only [Measure.real, ENNReal.toReal_one] using ENNReal.toReal_mono (by simp) h

theorem integrable_probability_tail (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (M : ℝ) :
    Integrable (fun t : ℝ => μ.real {x | t ≤ f x}) (volume.restrict (Ioc 0 M)) := by
  have hm : Measurable (fun t : ℝ => μ {x | t ≤ f x}) :=
    Antitone.measurable (fun _ _ h => measure_mono (fun _ hx => h.trans hx))
  apply (integrable_const (1 : ℝ)).mono' hm.ennreal_toReal.aestronglyMeasurable
  filter_upwards with t
  change |μ.real {x | t ≤ f x}| ≤ 1
  rw [abs_of_nonneg (probability_tail_le_one μ _).1]
  exact (probability_tail_le_one μ _).2

theorem integral_nonnegative_sub_le_of_event_bound
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (M C : ℝ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ f x) (hb : ∀ x, f x ≤ M)
    (he : ∀ B : Set X, MeasurableSet B → |μ.real B-ν.real B| ≤ C) :
    |(∫ x, f x ∂μ)-(∫ x, f x ∂ν)| ≤ M*C := by
  have hi (η : Measure X) [IsProbabilityMeasure η] : Integrable f η := by
    apply (integrable_const M).mono' hf.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (hn x)]
    exact hb x
  rw [(hi μ).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall hb),
    (hi ν).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall hb),
    ← integral_sub (integrable_probability_tail μ f M) (integrable_probability_tail ν f M)]
  calc
    _ ≤ ∫ t in Ioc 0 M, |μ.real {x | t ≤ f x}-ν.real {x | t ≤ f x}| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Ioc 0 M)) (fun t : ℝ => μ.real {x | t ≤ f x}-ν.real {x | t ≤ f x})
    _ ≤ ∫ _t in Ioc 0 M, C := by
      apply integral_mono ((integrable_probability_tail μ f M).sub
        (integrable_probability_tail ν f M)).abs (integrable_const C)
      intro t
      exact he _ (measurableSet_le measurable_const hf)
    _ = M*C := by simp [hM]

/-- A common absolute bound `M` gives the factor `2M` for signed real tests. -/
theorem integral_signed_sub_le_of_event_bound
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (M C : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, |f x| ≤ M)
    (he : ∀ B : Set X, MeasurableSet B → |μ.real B-ν.real B| ≤ C) :
    |(∫ x, f x ∂μ)-(∫ x, f x ∂ν)| ≤ 2*M*C := by
  have hi (η : Measure X) [IsProbabilityMeasure η] : Integrable f η :=
    (integrable_const M).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have h := integral_nonnegative_sub_le_of_event_bound μ ν (fun x => f x+M)
    (hf.add_const M) (2*M) C (by positivity)
    (fun x => by have h0 := (abs_le.mp (hb x)).1; linarith)
    (fun x => by have h0 := (abs_le.mp (hb x)).2; linarith) he
  rw [integral_add (hi μ) (integrable_const M), integral_add (hi ν) (integrable_const M)] at h
  simpa using h

end BlockBand.Model.Construction
