module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Scalar Gaussian translation through densities

The total variation distance between a centred real Gaussian law of standard deviation `σ` and
its translate by `s` is at most `min(1, |s|/(√(2π) σ))`, proved through the Gaussian densities.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- Probability normalization: half the `L¹` distance of the densities. -/
def gaussianTranslationHalfL1 (v : ℝ≥0) (s : ℝ) : ℝ :=
  (∫ x : ℝ, |gaussianPDFReal 0 v x - gaussianPDFReal s v x|) / 2

/-- Scalar probability total variation in the event-supremum convention, between a Gaussian
law and its translate. -/
def gaussianTranslationEventTV (v : ℝ≥0) (s : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ A : Set ℝ, MeasurableSet A ∧
    r = |(gaussianReal 0 v).real A - (gaussianReal s v).real A|}

/-- Exact global Gaussian density maximum, including zero variance density. -/
theorem gaussianTranslation_density_le (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  unfold gaussianPDFReal
  calc
    _ ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    _ = _ := mul_one _

/-- The midpoint is the single crossing for a nonnegative mean shift. -/
theorem gaussianTranslation_density_crossing (v : ℝ≥0) (s x : ℝ)
    (hs : 0 ≤ s) :
    (x ≤ s / 2 → gaussianPDFReal s v x ≤ gaussianPDFReal 0 v x) ∧
    (s / 2 ≤ x → gaussianPDFReal 0 v x ≤ gaussianPDFReal s v x) := by
  have hmono (a b : ℝ) (hab : a ^ 2 ≤ b ^ 2) :
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-b ^ 2 / (2 * (v : ℝ))) ≤
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-a ^ 2 / (2 * (v : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg hab) (by positivity)
  constructor <;> intro hx <;> unfold gaussianPDFReal
  · apply hmono
    simp only [sub_zero]
    nlinarith
  · apply hmono
    simp only [sub_zero]
    nlinarith

/-- Real-valued probability of a measurable event is its density integral. -/
theorem gaussianTranslation_real_apply (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (A : Set ℝ) :
    (gaussianReal μ v).real A = ∫ x in A, gaussianPDFReal μ v x := by
  rw [Measure.real, gaussianReal_apply_eq_integral μ hv,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg μ v))]

/-- Translating the Gaussian law translates its half-line probability. -/
theorem gaussianTranslation_cdf (v : ℝ≥0) (s a : ℝ) :
    gaussianReal s v (Iic a) = gaussianReal 0 v (Iic (a - s)) := by
  rw [← zero_add s, ← gaussianReal_map_add_const s,
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_preimage, mem_Iic]
  constructor <;> intro h <;> linarith

/-- The signed density has total integral zero, without a boundary premise. -/
theorem gaussianTranslation_integral_sub (v : ℝ≥0) (hv : v ≠ 0) (s : ℝ) :
    (∫ x : ℝ, gaussianPDFReal 0 v x - gaussianPDFReal s v x) = 0 := by
  rw [integral_sub (integrable_gaussianPDFReal 0 v) (integrable_gaussianPDFReal s v),
    integral_gaussianPDFReal_eq_one 0 hv, integral_gaussianPDFReal_eq_one s hv]
  norm_num

/-- Single crossing identifies half the `L¹` distance with a central interval. -/
theorem gaussianTranslation_halfL1_eq_interval (v : ℝ≥0) (hv : v ≠ 0)
    (s : ℝ) (hs : 0 ≤ s) :
    gaussianTranslationHalfL1 v s =
      ∫ x in (-s / 2)..(s / 2), gaussianPDFReal 0 v x := by
  let d : ℝ → ℝ := fun x => gaussianPDFReal 0 v x - gaussianPDFReal s v x
  have hd : Integrable d :=
    (integrable_gaussianPDFReal 0 v).sub (integrable_gaussianPDFReal s v)
  have hd0 : (∫ x, d x) = 0 := gaussianTranslation_integral_sub v hv s
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := s / 2) hd.integrableOn hd.integrableOn
  have hsplitabs := intervalIntegral.integral_Iic_add_Ioi
    (b := s / 2) hd.abs.integrableOn hd.abs.integrableOn
  have hl : (∫ x in Iic (s / 2), |d x|) = ∫ x in Iic (s / 2), d x := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro x hx
    exact abs_of_nonneg (sub_nonneg.mpr
      ((gaussianTranslation_density_crossing v s x hs).1 hx))
  have hr : (∫ x in Ioi (s / 2), |d x|) = -(∫ x in Ioi (s / 2), d x) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact abs_of_nonpos (sub_nonpos.mpr
      ((gaussianTranslation_density_crossing v s x hs).2 hx.le))
  have hhalf : gaussianTranslationHalfL1 v s = ∫ x in Iic (s / 2), d x := by
    unfold gaussianTranslationHalfL1
    change (∫ x, |d x|) / 2 = _
    rw [hl, hr] at hsplitabs
    rw [hd0] at hsplit
    linarith
  rw [hhalf, integral_sub (integrable_gaussianPDFReal 0 v).integrableOn
    (integrable_gaussianPDFReal s v).integrableOn]
  have hc' := congrArg ENNReal.toReal (gaussianTranslation_cdf v s (s / 2))
  change (gaussianReal s v).real (Iic (s / 2)) =
    (gaussianReal 0 v).real (Iic (s / 2 - s)) at hc'
  rw [gaussianTranslation_real_apply _ _ hv,
    gaussianTranslation_real_apply _ _ hv] at hc'
  have he : s / 2 - s = -s / 2 := by ring
  rw [he] at hc'
  rw [hc']
  exact intervalIntegral.integral_Iic_sub_Iic
    (integrable_gaussianPDFReal 0 v).integrableOn
    (integrable_gaussianPDFReal 0 v).integrableOn

/-- Half-`L¹` is unchanged by reversing the shift. -/
theorem gaussianTranslation_halfL1_neg (v : ℝ≥0) (s : ℝ) :
    gaussianTranslationHalfL1 v (-s) = gaussianTranslationHalfL1 v s := by
  unfold gaussianTranslationHalfL1
  congr 1
  have h := integral_neg_eq_self
    (fun x : ℝ => |gaussianPDFReal 0 v x - gaussianPDFReal s v x|) volume
  rw [← h]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [gaussianPDFReal, sub_zero, sub_neg_eq_add]
  ring_nf

/-- Exact scalar density distance bound, uniform over every real shift. -/
theorem gaussianTranslation_halfL1_le (v : ℝ≥0) (hv : v ≠ 0) (s : ℝ) :
    gaussianTranslationHalfL1 v s ≤
      |s| * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  wlog hs : 0 ≤ s generalizing s
  · have h := this (-s) (by linarith)
    simpa only [gaussianTranslation_halfL1_neg, abs_neg] using h
  rw [gaussianTranslation_halfL1_eq_interval v hv s hs, abs_of_nonneg hs]
  have h := intervalIntegral.integral_mono
    (a := -s / 2) (b := s / 2) (by linarith)
    (integrable_gaussianPDFReal 0 v).intervalIntegrable
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) volume (-s / 2) (s / 2))
    (gaussianTranslation_density_le 0 v)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, show s / 2 - -s / 2 = s by ring] using h

/-- The bound `≤ 1` follows from the normalization of the densities. -/
theorem gaussianTranslation_halfL1_le_one (v : ℝ≥0) (hv : v ≠ 0) (s : ℝ) :
    gaussianTranslationHalfL1 v s ≤ 1 := by
  have h : (∫ x : ℝ, |gaussianPDFReal 0 v x - gaussianPDFReal s v x|) ≤ 2 := by
    calc
      _ ≤ ∫ x : ℝ, gaussianPDFReal 0 v x + gaussianPDFReal s v x := by
        apply integral_mono ((integrable_gaussianPDFReal 0 v).sub
          (integrable_gaussianPDFReal s v)).abs
          ((integrable_gaussianPDFReal 0 v).add (integrable_gaussianPDFReal s v))
        intro x
        change |gaussianPDFReal 0 v x - gaussianPDFReal s v x| ≤
          gaussianPDFReal 0 v x + gaussianPDFReal s v x
        exact abs_sub_le_iff.mpr ⟨by linarith [gaussianPDFReal_nonneg s v x],
          by linarith [gaussianPDFReal_nonneg 0 v x]⟩
      _ = 2 := by
        rw [integral_add (integrable_gaussianPDFReal 0 v) (integrable_gaussianPDFReal s v),
          integral_gaussianPDFReal_eq_one 0 hv, integral_gaussianPDFReal_eq_one s hv]
        norm_num
  unfold gaussianTranslationHalfL1
  linarith

/-- Every measurable event is controlled by the probability-normalized `L¹` bound. This gives
the event-supremum form of the total variation bound. -/
theorem gaussianTranslation_event_le_halfL1 (v : ℝ≥0) (hv : v ≠ 0) (s : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    |(gaussianReal 0 v).real A - (gaussianReal s v).real A| ≤
      gaussianTranslationHalfL1 v s := by
  let d : ℝ → ℝ := fun x => gaussianPDFReal 0 v x - gaussianPDFReal s v x
  have hd : Integrable d :=
    (integrable_gaussianPDFReal 0 v).sub (integrable_gaussianPDFReal s v)
  have hd0 : (∫ x, d x) = 0 := gaussianTranslation_integral_sub v hv s
  have hc : (∫ x in Aᶜ, d x) = -(∫ x in A, d x) := by
    rw [setIntegral_compl hA hd, hd0, zero_sub]
  have hleft : |∫ x in A, d x| ≤ ∫ x in A, |d x| := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := volume.restrict A) d)
  have hright : |∫ x in A, d x| ≤ ∫ x in Aᶜ, |d x| := by
    have h := norm_integral_le_integral_norm (μ := volume.restrict Aᶜ) d
    simpa only [Real.norm_eq_abs, hc, abs_neg] using h
  have hsplit := integral_add_compl hA hd.abs
  rw [gaussianTranslation_real_apply _ _ hv, gaussianTranslation_real_apply _ _ hv,
    ← integral_sub (integrable_gaussianPDFReal 0 v).integrableOn
      (integrable_gaussianPDFReal s v).integrableOn]
  change |∫ x in A, d x| ≤ (∫ x, |d x|) / 2
  linarith

/-- Scalar Gaussian event distance, all shifts, exact coefficient, capped one. -/
theorem gaussianTranslation_event_le_min (v : ℝ≥0) (hv : v ≠ 0) (s : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    |(gaussianReal 0 v).real A - (gaussianReal s v).real A| ≤
      min 1 (|s| * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) := by
  exact (gaussianTranslation_event_le_halfL1 v hv s A hA).trans
    (le_min (gaussianTranslation_halfL1_le_one v hv s)
      (gaussianTranslation_halfL1_le v hv s))

/-- Standard-deviation form with the scalar constant `1/(√(2π) σ)`. -/
theorem gaussianTranslation_sigma_halfL1_le (σ : ℝ) (hσ : 0 < σ) (s : ℝ) :
    gaussianTranslationHalfL1 ⟨σ ^ 2, sq_nonneg σ⟩ s ≤
      min 1 (|s| / (Real.sqrt (2 * Real.pi) * σ)) := by
  have hv : (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have : σ ^ 2 = 0 := congrArg (fun t : ℝ≥0 => (t : ℝ)) h
    nlinarith
  have he : Real.sqrt (2 * Real.pi * σ ^ 2) = Real.sqrt (2 * Real.pi) * σ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hσ]
  have h := le_min (gaussianTranslation_halfL1_le_one ⟨σ ^ 2, sq_nonneg σ⟩ hv s)
    (gaussianTranslation_halfL1_le ⟨σ ^ 2, sq_nonneg σ⟩ hv s)
  change gaussianTranslationHalfL1 ⟨σ ^ 2, sq_nonneg σ⟩ s ≤
    min 1 (|s| * (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹) at h
  simpa only [he, div_eq_mul_inv] using h

/-- Standard-deviation event formulation of the exact scalar TV bound. -/
theorem gaussianTranslation_sigma_event_le (σ : ℝ) (hσ : 0 < σ) (s : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    |(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩).real A -
      (gaussianReal s ⟨σ ^ 2, sq_nonneg σ⟩).real A| ≤
      min 1 (|s| / (Real.sqrt (2 * Real.pi) * σ)) := by
  have hv : (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have : σ ^ 2 = 0 := congrArg (fun t : ℝ≥0 => (t : ℝ)) h
    nlinarith
  exact (gaussianTranslation_event_le_halfL1 ⟨σ ^ 2, sq_nonneg σ⟩ hv s A hA).trans
    (gaussianTranslation_sigma_halfL1_le σ hσ s)

/-- The scalar event-supremum total variation is bounded by half-`L¹`. -/
theorem gaussianTranslation_eventTV_le_halfL1 (v : ℝ≥0) (hv : v ≠ 0) (s : ℝ) :
    gaussianTranslationEventTV v s ≤ gaussianTranslationHalfL1 v s := by
  unfold gaussianTranslationEventTV
  apply csSup_le
  · refine ⟨0, ∅, MeasurableSet.empty, ?_⟩
    simp
  · rintro r ⟨A, hA, rfl⟩
    exact gaussianTranslation_event_le_halfL1 v hv s A hA

/-- Scalar Gaussian translation total variation, all shifts, coefficient
`1/(√(2π) σ)` and cap one. The norm is the supremum over measurable events. -/
theorem gaussianTranslation_sigma_tv_le (σ : ℝ) (hσ : 0 < σ) (s : ℝ) :
    gaussianTranslationEventTV ⟨σ ^ 2, sq_nonneg σ⟩ s ≤
      min 1 (|s| / (Real.sqrt (2 * Real.pi) * σ)) := by
  have hv : (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have : σ ^ 2 = 0 := congrArg (fun t : ℝ≥0 => (t : ℝ)) h
    nlinarith
  exact (gaussianTranslation_eventTV_le_halfL1 ⟨σ ^ 2, sq_nonneg σ⟩ hv s).trans
    (gaussianTranslation_sigma_halfL1_le σ hσ s)

end BlockBand.Model.Construction
