module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.Monotone

/-!
# One-dimensional area formula and Gaussian averaging for the pair pole exclusion lemma

* `lintegral_deriv_indicator_le` (inequality form): for every monotone
  `f : ℝ → ℝ` and Borel `B`, `∫ f'(ζ) 1{f(ζ) ∈ B} dζ ≤ |B|`, with `f'` the a.e. derivative
  (`deriv f`). No absolute continuity is needed for the inequality: on
  `{f' > 0}` the function is injective and the change of variables
  `lintegral_image_eq_lintegral_abs_deriv_mul` applies; elsewhere the integrand vanishes.
* `le_deriv_of_left_bound`: a quantitative left-difference bound
  `f(ζ₀ - δ) ≤ f(ζ₀) - δ m + δ²/g` gives `m ≤ f'(ζ₀)` at a differentiability point.
* `averaging_core`: if `m ≤ f'` Lebesgue-a.e., then
  `∫ m(ζ) 1{f(ζ) ∈ B} dN(0,v) ≤ (2πv)^{-1/2} |B|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.PoleExclusion

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-- A monotone function constant on `[a, b]`, `a < b`, has zero derivative at `a`. -/
theorem deriv_eq_zero_of_eq {f : ℝ → ℝ} (hf : Monotone f) {a b : ℝ} (hab : a < b)
    (hfab : f a = f b) (hd : DifferentiableAt ℝ f a) : deriv f a = 0 := by
  have ht := hd.hasDerivAt.tendsto_slope_zero_right
  have hev : (fun t : ℝ => t⁻¹ • (f (a + t) - f a)) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hab)] with t ht
    have h1 : f a ≤ f (a + t) := hf (by linarith [ht.1])
    have h2 : f (a + t) ≤ f b := hf (by linarith [ht.2])
    have : f (a + t) = f a := le_antisymm (hfab ▸ h2) h1
    simp [this]
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hev.symm)

/-- A monotone function is injective on the set where it has positive derivative. -/
theorem injOn_pos_deriv {f : ℝ → ℝ} (hf : Monotone f) :
    InjOn f {x | DifferentiableAt ℝ f x ∧ 0 < deriv f x} := by
  intro a ha b hb hfab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (ne_of_gt ha.2) (deriv_eq_zero_of_eq hf h hfab ha.1)
  · exact (ne_of_gt hb.2) (deriv_eq_zero_of_eq hf h hfab.symm hb.1)

/-- **One-dimensional area inequality**: `∫ f' 1{f ∈ B} ≤ |B|` for monotone `f`. -/
theorem lintegral_deriv_indicator_le {f : ℝ → ℝ} (hf : Monotone f) {B : Set ℝ}
    (hB : MeasurableSet B) :
    ∫⁻ ζ, ENNReal.ofReal (deriv f ζ) * B.indicator 1 (f ζ) ≤ volume B := by
  set s := {x | DifferentiableAt ℝ f x ∧ 0 < deriv f x} with hs_def
  have hs : MeasurableSet s :=
    (measurableSet_of_differentiableAt ℝ f).inter
      (measurableSet_lt measurable_const (measurable_deriv f))
  have hind : (fun ζ => ENNReal.ofReal (deriv f ζ) * B.indicator 1 (f ζ)) =
      s.indicator (fun ζ => ENNReal.ofReal (|deriv f ζ|) * B.indicator 1 (f ζ)) := by
    funext ζ
    by_cases hζ : ζ ∈ s
    · rw [indicator_of_mem hζ, abs_of_pos hζ.2]
    · rw [indicator_of_notMem hζ]
      have : deriv f ζ ≤ 0 := by
        by_contra hpos
        rw [not_le] at hpos
        refine hζ ⟨?_, hpos⟩
        by_contra hnd
        rw [deriv_zero_of_not_differentiableAt hnd] at hpos
        exact lt_irrefl _ hpos
      rw [ENNReal.ofReal_of_nonpos this, zero_mul]
  rw [hind, lintegral_indicator hs, ← lintegral_image_eq_lintegral_abs_deriv_mul hs
    (fun x hx => hx.1.hasDerivAt.hasDerivWithinAt) (injOn_pos_deriv hf) (B.indicator 1),
    ← lintegral_indicator_one hB]
  exact setLIntegral_le_lintegral _ _

/-- Gaussian density bound: `∫ g dN(0,v) ≤ (2πv)^{-1/2} ∫ g dζ`. -/
theorem lintegral_gaussianReal_le {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ζ, g ζ ∂gaussianReal 0 v ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.pi * v))⁻¹ * ∫⁻ ζ, g ζ := by
  rw [gaussianReal_of_var_ne_zero 0 hv,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 v) hg,
    ← lintegral_const_mul _ hg]
  refine lintegral_mono fun ζ => ?_
  simp only [Pi.mul_apply]
  refine mul_le_mul_left ?_ _
  rw [gaussianPDF_def, gaussianPDFReal_def]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : Real.exp (-(ζ - 0) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (ζ - 0) ^ 2 / (2 * (v : ℝ)) := by positivity
    linarith [neg_div (2 * (v : ℝ)) ((ζ - 0) ^ 2)]
  have h2 : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(ζ - 0) ^ 2 / (2 * (v : ℝ)))
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := mul_one _

/-- A left-difference bound `f(ζ₀ - δ) ≤ f(ζ₀) - δ m + δ²/g` for `0 < δ < g` gives
`m ≤ f'(ζ₀)` at a differentiability point. -/
theorem le_deriv_of_left_bound {f : ℝ → ℝ} {ζ₀ m g : ℝ} (hd : DifferentiableAt ℝ f ζ₀)
    (hg : 0 < g) (hb : ∀ δ : ℝ, 0 < δ → δ < g → f (ζ₀ - δ) ≤ f ζ₀ - δ * m + δ ^ 2 / g) :
    m ≤ deriv f ζ₀ := by
  have ht := hd.hasDerivAt.tendsto_slope_zero_left
  have hlow : Tendsto (fun t : ℝ => m + t / g) (𝓝[<] 0) (𝓝 m) := by
    have : Tendsto (fun t : ℝ => m + t / g) (𝓝 0) (𝓝 (m + 0 / g)) :=
      (tendsto_const_nhds.add (tendsto_id.div_const g))
    rw [zero_div, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hlow ht ?_
  filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr hg)] with t ht'
  have hδ := hb (-t) (by linarith [ht'.2]) (by linarith [ht'.1])
  rw [show ζ₀ - -t = ζ₀ + t by ring] at hδ
  have htneg : t < 0 := ht'.2
  simp only [smul_eq_mul]
  rw [show t⁻¹ * (f (ζ₀ + t) - f ζ₀) = (f (ζ₀ + t) - f ζ₀) / t by ring,
    le_div_iff_of_neg htneg]
  have : (m + t / g) * t = t * m + t ^ 2 / g := by ring
  rw [this]
  rw [show (-t) ^ 2 = t ^ 2 by ring] at hδ
  linarith

/-- **Gaussian averaging**: if
`m ≤ f'` Lebesgue-almost everywhere for a monotone `f`, then for every Borel `B` and `v > 0`,
`∫ m 1{f ∈ B} dN(0,v) ≤ (2πv)^{-1/2} |B|`. -/
theorem averaging_core {f : ℝ → ℝ} (hf : Monotone f) (m : ℝ → ℝ)
    (hm : ∀ᵐ ζ, ENNReal.ofReal (m ζ) ≤ ENNReal.ofReal (deriv f ζ)) {v : ℝ≥0} (hv : v ≠ 0)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ∫⁻ ζ, ENNReal.ofReal (m ζ) * B.indicator 1 (f ζ) ∂gaussianReal 0 v ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.pi * v))⁻¹ * volume B := by
  have hac := gaussianReal_absolutelyContinuous 0 hv
  have hmeas : Measurable fun ζ => ENNReal.ofReal (deriv f ζ) * B.indicator 1 (f ζ) :=
    (measurable_deriv f).ennreal_ofReal.mul
      ((measurable_one.indicator hB).comp hf.measurable)
  calc ∫⁻ ζ, ENNReal.ofReal (m ζ) * B.indicator 1 (f ζ) ∂gaussianReal 0 v
      ≤ ∫⁻ ζ, ENNReal.ofReal (deriv f ζ) * B.indicator 1 (f ζ) ∂gaussianReal 0 v := by
        refine lintegral_mono_ae ?_
        filter_upwards [hac.ae_le hm] with ζ hζ
        exact mul_le_mul_left hζ _
    _ ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * v))⁻¹ *
          ∫⁻ ζ, ENNReal.ofReal (deriv f ζ) * B.indicator 1 (f ζ) :=
        lintegral_gaussianReal_le hv hmeas
    _ ≤ _ := mul_le_mul_right (lintegral_deriv_indicator_le hf hB) _

end BlockBand.Coarea.PoleExclusion
