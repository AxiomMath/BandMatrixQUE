module

public import BlockBand.Model.Construction.GaussianTranslationDensity
public import BlockBand.Counting.ScalarTrace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Independent-background Gaussian translation contraction

For a product of a centred real Gaussian and an arbitrary probability background, translating the
Gaussian coordinate moves every measurable event, and every measurable image event, by at most
the scalar translation bound.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- For finite measures, measurable product-event sections are integrable.
This constructs the Fubini premise from the event indicator. -/
theorem gaussianTranslation_integrable_sections (μ : Measure ℝ) (η : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure η] (A : Set (ℝ × Ω)) (hA : MeasurableSet A) :
    Integrable (fun y => μ.real ((fun x : ℝ => (x, y)) ⁻¹' A)) η := by
  have hi : Integrable (A.indicator (1 : ℝ × Ω → ℝ)) (μ.prod η) := by
    change Integrable (A.indicator (fun _ : ℝ × Ω => (1 : ℝ))) (μ.prod η)
    exact (integrable_const (1 : ℝ)).indicator hA
  have hs (y : Ω) :
      (∫ x : ℝ, A.indicator (1 : ℝ × Ω → ℝ) (x, y) ∂μ) =
        μ.real ((fun x : ℝ => (x, y)) ⁻¹' A) := by
    have hm : MeasurableSet ((fun x : ℝ => (x, y)) ⁻¹' A) :=
      hA.preimage (by fun_prop)
    calc
      _ = ∫ x : ℝ, ((fun t : ℝ => (t, y)) ⁻¹' A).indicator 1 x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : (x, y) ∈ A <;> simp [hx]
      _ = _ := integral_indicator_one hm
  simpa only [hs] using hi.integral_prod_right

/-- Product-event probability equals the integral of its scalar section
probabilities. The integrability is proved, rather than assumed. -/
theorem gaussianTranslation_product_real_event (μ : Measure ℝ) (η : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure η] (A : Set (ℝ × Ω)) (hA : MeasurableSet A) :
    (μ.prod η).real A = ∫ y, μ.real ((fun x : ℝ => (x, y)) ⁻¹' A) ∂η := by
  have hi : Integrable (A.indicator (1 : ℝ × Ω → ℝ)) (μ.prod η) := by
    change Integrable (A.indicator (fun _ : ℝ × Ω => (1 : ℝ))) (μ.prod η)
    exact (integrable_const (1 : ℝ)).indicator hA
  rw [← integral_indicator_one hA, integral_prod_symm _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  have hm : MeasurableSet ((fun x : ℝ => (x, y)) ⁻¹' A) :=
    hA.preimage (by fun_prop)
  calc
    _ = ∫ x : ℝ, ((fun t : ℝ => (t, y)) ⁻¹' A).indicator 1 x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : (x, y) ∈ A <;> simp [hx]
    _ = _ := integral_indicator_one hm

/-- Independent product contraction for every measurable input event. -/
theorem gaussianTranslation_product_event_le (σ : ℝ) (hσ : 0 < σ) (s : ℝ)
    (η : Measure Ω) [IsProbabilityMeasure η]
    (A : Set (ℝ × Ω)) (hA : MeasurableSet A) :
    |((gaussianReal 0 (NNReal.mk (σ ^ 2) (sq_nonneg σ))).prod η).real A -
      ((gaussianReal s (NNReal.mk (σ ^ 2) (sq_nonneg σ))).prod η).real A| ≤
      min 1 (|s| / (Real.sqrt (2 * Real.pi) * σ)) := by
  let μ₀ := gaussianReal 0 (NNReal.mk (σ ^ 2) (sq_nonneg σ))
  let μₛ := gaussianReal s (NNReal.mk (σ ^ 2) (sq_nonneg σ))
  let C := min 1 (|s| / (Real.sqrt (2 * Real.pi) * σ))
  let : IsProbabilityMeasure μ₀ := instIsProbabilityMeasureGaussianReal 0 _
  let : IsProbabilityMeasure μₛ := instIsProbabilityMeasureGaussianReal s _
  have h₀ := gaussianTranslation_integrable_sections μ₀ η A hA
  have hₛ := gaussianTranslation_integrable_sections μₛ η A hA
  change |(μ₀.prod η).real A - (μₛ.prod η).real A| ≤ C
  rw [gaussianTranslation_product_real_event _ _ A hA,
    gaussianTranslation_product_real_event _ _ A hA, ← integral_sub h₀ hₛ]
  calc
    _ ≤ ∫ y, |μ₀.real ((fun x : ℝ => (x, y)) ⁻¹' A) -
        μₛ.real ((fun x : ℝ => (x, y)) ⁻¹' A)| ∂η := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := η) (fun y => μ₀.real ((fun x : ℝ => (x, y)) ⁻¹' A) -
          μₛ.real ((fun x : ℝ => (x, y)) ⁻¹' A))
    _ ≤ ∫ _ : Ω, C ∂η := by
      apply integral_mono (h₀.sub hₛ).abs (integrable_const C)
      intro y
      exact gaussianTranslation_sigma_event_le σ hσ s _
        (hA.preimage (by fun_prop))
    _ = C := by simp

/-- Every measurable map contracts the independent-product event bound. -/
theorem gaussianTranslation_product_map_event_le (σ : ℝ) (hσ : 0 < σ) (s : ℝ)
    (η : Measure Ω) [IsProbabilityMeasure η]
    (F : ℝ × Ω → X) (hF : Measurable F) (B : Set X) (hB : MeasurableSet B) :
    |(Measure.map F ((gaussianReal 0 (NNReal.mk (σ ^ 2) (sq_nonneg σ))).prod η)).real B -
      (Measure.map F ((gaussianReal s (NNReal.mk (σ ^ 2) (sq_nonneg σ))).prod η)).real B| ≤
      min 1 (|s| / (Real.sqrt (2 * Real.pi) * σ)) := by
  simp only [Measure.real, Measure.map_apply hF hB]
  exact gaussianTranslation_product_event_le σ hσ s η (F ⁻¹' B) (hB.preimage hF)

end BlockBand.Model.Construction

namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- Positive scalar standard deviation at a positive microscopic density. -/
def spectralScalarStandardDeviation (p : BlockBand.Parameters) (ρ : ℝ) : ℝ :=
  ρ * Real.sqrt (p.c * (p.n : ℝ))

theorem spectralScalarStandardDeviation_pos (p : BlockBand.Parameters)
    (ρ : ℝ) (hρ : 0 < ρ) : 0 < p.spectralScalarStandardDeviation ρ := by
  unfold spectralScalarStandardDeviation
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  positivity [p.c_pos]

/-- The microscopic variance is exactly the displayed standard deviation squared. -/
theorem spectralScalarVariance_eq_standardDeviation_sq (p : BlockBand.Parameters) (ρ : ℝ) :
    p.spectralScalarVariance ρ =
      (NNReal.mk ((p.spectralScalarStandardDeviation ρ) ^ 2) (sq_nonneg _)) := by
  apply NNReal.coe_injective
  change p.c * ρ ^ 2 * (p.n : ℝ) = (ρ * Real.sqrt (p.c * (p.n : ℝ))) ^ 2
  rw [mul_pow, Real.sq_sqrt (mul_nonneg p.c_pos.le (Nat.cast_nonneg _))]
  ring

/-- Physical scalar marginal, in the standard-deviation normalization
used by the scalar product contraction. No independent background is asserted. -/
theorem GaussianRingModel.spectralScalarTrace_standardDeviation_hasLaw
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (ρ : ℝ) :
    HasLaw (fun H => ((p.N : ℝ) * ρ) * p.scalarTrace H)
      (gaussianReal 0 (NNReal.mk ((p.spectralScalarStandardDeviation ρ) ^ 2) (sq_nonneg _)))
      (model.law : Measure p.SiteMatrix) := by
  simpa only [p.spectralScalarVariance_eq_standardDeviation_sq ρ] using
    model.spectralScalarTrace_hasLaw ρ

/-- Exact physical normalization of the scalar TV denominator. -/
theorem spectralScalarStandardDeviation_denominator (p : BlockBand.Parameters) (ρ : ℝ) :
    Real.sqrt (2 * Real.pi) * p.spectralScalarStandardDeviation ρ =
      ρ * Real.sqrt (2 * Real.pi * p.c * (p.n : ℝ)) := by
  unfold spectralScalarStandardDeviation
  have hsqrt : Real.sqrt ((2 * Real.pi) * (p.c * (p.n : ℝ))) =
      Real.sqrt (2 * Real.pi) * Real.sqrt (p.c * (p.n : ℝ)) :=
    Real.sqrt_mul (by positivity) _
  rw [show 2 * Real.pi * p.c * (p.n : ℝ) =
    (2 * Real.pi) * (p.c * (p.n : ℝ)) by ring, hsqrt]
  ring

/-- The microscopic scalar marginal, independently coupled with any
probability background and passed through any measurable map, obeys the
finite translation bound. The product is constructed here; it is not
identified with a physical marked-spectrum law. -/
theorem GaussianRingModel.spectralScalarTrace_product_map_event_le
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (ρ : ℝ) (hρ : 0 < ρ)
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (s : ℝ) (η : Measure Ω) [IsProbabilityMeasure η]
    (F : ℝ × Ω → X) (hF : Measurable F) (B : Set X) (hB : MeasurableSet B) :
    |(Measure.map F ((Measure.map
        (fun H => ((p.N : ℝ) * ρ) * p.scalarTrace H)
        (model.law : Measure p.SiteMatrix)).prod η)).real B -
      (Measure.map F ((Measure.map (fun t : ℝ => t + s) (Measure.map
        (fun H => ((p.N : ℝ) * ρ) * p.scalarTrace H)
        (model.law : Measure p.SiteMatrix))).prod η)).real B| ≤
      min 1 (|s| / (ρ * Real.sqrt (2 * Real.pi * p.c * (p.n : ℝ)))) := by
  have hm : Measure.map (fun t : ℝ => t + s)
      (gaussianReal 0 (NNReal.mk ((p.spectralScalarStandardDeviation ρ) ^ 2) (sq_nonneg _))) =
      gaussianReal s (NNReal.mk ((p.spectralScalarStandardDeviation ρ) ^ 2) (sq_nonneg _)) := by
    simpa only [zero_add] using
      (gaussianReal_map_add_const (μ := 0)
        (v := NNReal.mk ((p.spectralScalarStandardDeviation ρ) ^ 2) (sq_nonneg _)) s)
  rw [(model.spectralScalarTrace_standardDeviation_hasLaw ρ).map_eq, hm]
  have h := BlockBand.Model.Construction.gaussianTranslation_product_map_event_le
    (p.spectralScalarStandardDeviation ρ)
    (p.spectralScalarStandardDeviation_pos ρ hρ) s η F hF B hB
  simpa only [p.spectralScalarStandardDeviation_denominator ρ] using h

end BlockBand.Parameters
