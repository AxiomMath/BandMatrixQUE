module

public import BlockBand.Endpoints.Response.RemoteHigherWindowPathwise
public import BlockBand.Endpoints.Sine.FlowAdmissionPalmGaussian
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Gaussian likelihoods for the window transfer: products, scalings, shifts, Hölder

* `rhw_pi_withDensity` — a product of densities is the density of the product measure.
* `rhw_lintegral_prod_pi` — `∫ ∏ f_i(x_i) d(⊗μ_i) = ∏ ∫ f_i dμ_i` (probability factors).
* `rhw_lintegral_withDensity_holder` — `∫ f d(ρμ) ≤ (∫ρ^{a'})^{1/a'} (∫ f^a)^{1/a}`.
* `rhw_lintegral_rpow_le` — Jensen `∫ f^θ ≤ (∫ f)^θ` for `0 ≤ θ ≤ 1` on a probability space.
* `rhw_withDensity_scaleRatio` — `N(0, μ²v) = N(0, v)` with density
  `μ⁻¹ exp(x²(1 - μ⁻²)/(2v))`; `rhw_lintegral_scaleRatio_rpow`, `rhw_lintegral_exp_sq`.
* `rhw_lintegral_ratio_rpow` — `∫ (dN(m,1)/dN(0,1))^s dN(0,1) = e^{s(s-1)m²/2}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-!
## 1. Abstract measure facts
-/

theorem rhw_lintegral_prod_pi {ι : Type*} [Fintype ι] {Y : ι → Type*}
    [∀ i, MeasurableSpace (Y i)] (μ : ∀ i, Measure (Y i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ∀ i, Y i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  classical
  refine (lintegral_prod_eq_prod_lintegral_of_indepFun (μ := Measure.pi μ) Finset.univ
    (fun i (x : ∀ j, Y j) => f i (x i))
    (iIndepFun_pi fun i => (hf i).aemeasurable)
    (fun i => (hf i).comp (measurable_pi_apply i))).trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (measurePreserving_eval μ i).lintegral_comp (hf i)

theorem rhw_pi_withDensity {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (ρ : ∀ i, X i → ℝ≥0∞) (hρ : ∀ i, Measurable (ρ i))
    [∀ i, SigmaFinite ((μ i).withDensity (ρ i))] :
    Measure.pi (fun i => (μ i).withDensity (ρ i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, ρ i (x i)) := by
  classical
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (fun x => ∏ i, ρ i (x i)) = fun x =>
      ∏ i, (s i).indicator (ρ i) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, rhw_lintegral_prod_pi μ _ fun i => (hρ i).indicator (hs i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]

/-- **Hölder for a density**: `∫ f d(ρμ) ≤ (∫ ρ^{a'} dμ)^{1/a'} (∫ f^a dμ)^{1/a}`. -/
theorem rhw_lintegral_withDensity_holder {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ρ f : X → ℝ≥0∞} (hρ : Measurable ρ) (hf : AEMeasurable f μ) {a a' : ℝ}
    (ha : a.HolderConjugate a') :
    ∫⁻ x, f x ∂μ.withDensity ρ ≤
      (∫⁻ x, ρ x ^ a' ∂μ) ^ (1 / a') * (∫⁻ x, f x ^ a ∂μ) ^ (1 / a) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀ hρ.aemeasurable hf]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ ha.symm hρ.aemeasurable hf

/-- **Jensen** on a probability space: `∫ f^θ ≤ (∫ f)^θ`, `0 < θ ≤ 1`. -/
theorem rhw_lintegral_rpow_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ≥0∞} (hf : AEMeasurable f μ) {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) : ∫⁻ x, f x ^ θ ∂μ ≤ (∫⁻ x, f x ∂μ) ^ θ := by
  rcases hθ1.lt_or_eq with h | h
  · have hc : (1 / θ).HolderConjugate (1 / (1 - θ)) := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [one_div, inv_inv]; ring
      · positivity
      · exact one_div_pos.mpr (by linarith)
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc (hf.pow_const θ) aemeasurable_const
      (f := fun x => f x ^ θ) (g := fun _ => (1 : ℝ≥0∞))
    simp only [mul_one, ENNReal.one_rpow, lintegral_const, measure_univ, one_div_one_div,
      ← ENNReal.rpow_mul, mul_one_div_cancel hθ.ne', ENNReal.rpow_one, Pi.mul_apply] at this
    exact this
  · subst h; simp

/-!
## 2. One real Gaussian coordinate
-/

/-- The density of `N(0, μ²v)` with respect to `N(0, v)`: `μ⁻¹ exp(x²(1 - μ⁻²)/(2v))`. -/
def rhwScaleRatio (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (μ⁻¹ * Real.exp (x ^ 2 * (1 - (μ ^ 2)⁻¹) / (2 * v)))

theorem rhw_measurable_scaleRatio (μ : ℝ) (v : ℝ≥0) : Measurable (rhwScaleRatio μ v) := by
  unfold rhwScaleRatio; fun_prop

theorem rhw_withDensity_scaleRatio {μ : ℝ} (hμ : 0 < μ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 v).withDensity (rhwScaleRatio μ v) =
      gaussianReal 0 (NNReal.mk (μ ^ 2) (sq_nonneg _) * v) := by
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.mp h.symm))
  have hv2 : (NNReal.mk (μ ^ 2) (sq_nonneg _) * v : ℝ≥0) ≠ 0 := by
    refine mul_ne_zero (fun h => ?_) hv
    have := congrArg (fun r : ℝ≥0 => (r : ℝ)) h
    simp only [NNReal.coe_zero] at this
    exact (pow_pos hμ 2).ne' this
  rw [gaussianReal_of_var_ne_zero 0 hv, gaussianReal_of_var_ne_zero 0 hv2,
    ← withDensity_mul volume (measurable_gaussianPDF 0 v) (rhw_measurable_scaleRatio μ v)]
  congr 1
  funext x
  simp only [Pi.mul_apply, gaussianPDF, rhwScaleRatio]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)]
  congr 1
  have hc : ((NNReal.mk (μ ^ 2) (sq_nonneg _) * v : ℝ≥0) : ℝ) = μ ^ 2 * v := by
    rw [NNReal.coe_mul, NNReal.coe_mk]
  simp only [gaussianPDFReal, sub_zero]
  rw [hc]
  have hs : Real.sqrt (2 * Real.pi * (μ ^ 2 * v)) = μ * Real.sqrt (2 * Real.pi * v) := by
    rw [show 2 * Real.pi * (μ ^ 2 * v) = μ ^ 2 * (2 * Real.pi * v) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hμ.le]
  have he : Real.exp (-x ^ 2 / (2 * v)) * Real.exp (x ^ 2 * (1 - (μ ^ 2)⁻¹) / (2 * v)) =
      Real.exp (-x ^ 2 / (2 * (μ ^ 2 * v))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hs, mul_inv]
  linear_combination ((Real.sqrt (2 * Real.pi * v))⁻¹ * μ⁻¹) * he

theorem rhw_lintegral_scaleRatio {μ : ℝ} (hμ : 0 < μ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ x, rhwScaleRatio μ v x ∂gaussianReal 0 v = 1 := by
  have h := congrArg (fun m : Measure ℝ => m Set.univ) (rhw_withDensity_scaleRatio hμ hv)
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, measure_univ] at h
  exact h

/-- `∫ exp(x²(1 - μ⁻²)/(2v)) dN(0, v) = μ`. -/
theorem rhw_lintegral_exp_sq {μ : ℝ} (hμ : 0 < μ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (x ^ 2 * (1 - (μ ^ 2)⁻¹) / (2 * v))) ∂gaussianReal 0 v =
      ENNReal.ofReal μ := by
  have h := rhw_lintegral_scaleRatio hμ hv
  unfold rhwScaleRatio at h
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr hμ.le)] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  have h1 : ENNReal.ofReal μ * ENNReal.ofReal μ⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hμ.le, mul_inv_cancel₀ hμ.ne', ENNReal.ofReal_one]
  calc _ = ENNReal.ofReal μ * (ENNReal.ofReal μ⁻¹ * ∫⁻ x, ENNReal.ofReal
        (Real.exp (x ^ 2 * (1 - (μ ^ 2)⁻¹) / (2 * v))) ∂gaussianReal 0 v) := by
          rw [← mul_assoc, h1, one_mul]
    _ = _ := by rw [h, mul_one]

/-- **Moments of the scale ratio**: for `s ≥ 0` with `κ = 1 - s(1 - μ⁻²) > 0`,
`∫ (dN(0,μ²v)/dN(0,v))^s dN(0,v) = μ^{-s} κ^{-1/2}`. -/
theorem rhw_lintegral_scaleRatio_rpow {μ : ℝ} (hμ : 0 < μ) {v : ℝ≥0} (hv : v ≠ 0) {s : ℝ}
    (hs : 0 ≤ s) (hκ : 0 < 1 - s * (1 - (μ ^ 2)⁻¹)) :
    ∫⁻ x, rhwScaleRatio μ v x ^ s ∂gaussianReal 0 v =
      ENNReal.ofReal (μ ^ (-s) * (1 - s * (1 - (μ ^ 2)⁻¹)) ^ (-(1 / 2 : ℝ))) := by
  set κ := 1 - s * (1 - (μ ^ 2)⁻¹) with hκdef
  set ν := κ ^ (-(1 / 2 : ℝ)) with hν
  have hν0 : 0 < ν := Real.rpow_pos_of_pos hκ _
  have hνsq : (ν ^ 2)⁻¹ = κ := by
    rw [hν, ← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
    norm_num
    rw [Real.rpow_neg_one, inv_inv]
  have hpt : ∀ x : ℝ, rhwScaleRatio μ v x ^ s = ENNReal.ofReal (μ ^ (-s)) *
      ENNReal.ofReal (Real.exp (x ^ 2 * (1 - (ν ^ 2)⁻¹) / (2 * v))) := by
    intro x
    unfold rhwScaleRatio
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hs,
      Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul,
      ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), Real.inv_rpow hμ.le,
      ← Real.rpow_neg hμ.le, hνsq, hκdef]
    congr 3
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, rhw_lintegral_exp_sq hν0 hv,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hμ.le _)]

/-- **Moments of the shift ratio**: `∫ (dN(m,1)/dN(0,1))^s dN(0,1) = e^{s(s-1)m²/2}`. -/
theorem rhw_lintegral_ratio_rpow (m : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ y, fa_ratio m 1 y ^ s ∂gaussianReal 0 1 =
      ENNReal.ofReal (Real.exp (s * (s - 1) * m ^ 2 / 2)) := by
  have hpt : ∀ y, fa_ratio m 1 y ^ s =
      ENNReal.ofReal (Real.exp (s * (s - 1) * m ^ 2 / 2)) * fa_ratio (s * m) 1 y := by
    intro y
    unfold fa_ratio
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hs, ← Real.exp_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    simp only [NNReal.coe_one, div_one]
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h1 : ∫⁻ y, fa_ratio (s * m) 1 y ∂gaussianReal 0 1 = 1 := by
    have h := congrArg (fun m' : Measure ℝ => m' Set.univ)
      (fa_withDensity_ratio (s * m) (one_ne_zero : (1 : ℝ≥0) ≠ 0))
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      measure_univ] using h
  rw [h1, mul_one]

end BlockBand.Endpoints
