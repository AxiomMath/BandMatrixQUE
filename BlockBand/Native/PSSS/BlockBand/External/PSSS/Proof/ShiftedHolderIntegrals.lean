module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Scalar and Hölder estimates for the shifted APSSS integral

This file isolates the dimension-free real-analysis steps in APSSS
(Aizenman–Peled–Schenker–Shamis–Sodin), (6.19)--(6.22).  The lemmas
`holder_three_one` and `holder_three_two` are the cases `r = 1, 2` of the
first Hölder step; the case `r = 0` needs no Hölder inequality.  The exponent
arithmetic is recorded
separately so that the eventual assembly theorem does not have to normalize
fractions under a finite case split.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory Set
open scoped ENNReal NNReal

/-- APSSS (6.19), case `r = 1`, with the exact weights `1/3` and `2/3`. -/
theorem holder_three_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℝ≥0∞) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x ^ ((1 : ℝ) / 3) * g x ^ ((2 : ℝ) / 3) ∂μ) ≤
      (∫⁻ x, f x ∂μ) ^ ((1 : ℝ) / 3) *
        (∫⁻ x, g x ∂μ) ^ ((2 : ℝ) / 3) := by
  exact ENNReal.lintegral_mul_norm_pow_le hf hg (by norm_num) (by norm_num) (by norm_num)

/-- APSSS (6.19), case `r = 2`, with three equal Hölder weights. -/
theorem holder_three_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f₀ f₁ g : α → ℝ≥0∞)
    (hf₀ : AEMeasurable f₀ μ) (hf₁ : AEMeasurable f₁ μ)
    (hg : AEMeasurable g μ) :
    (∫⁻ x, f₀ x ^ ((1 : ℝ) / 3) *
        f₁ x ^ ((1 : ℝ) / 3) * g x ^ ((1 : ℝ) / 3) ∂μ) ≤
      (∫⁻ x, f₀ x ∂μ) ^ ((1 : ℝ) / 3) *
        (∫⁻ x, f₁ x ∂μ) ^ ((1 : ℝ) / 3) *
          (∫⁻ x, g x ∂μ) ^ ((1 : ℝ) / 3) := by
  let F : Fin 3 → α → ℝ≥0∞ := ![f₀, f₁, g]
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (F i) μ := by
    intro i _
    fin_cases i <;> simp [F, hf₀, hf₁, hg]
  have h := ENNReal.lintegral_prod_norm_pow_le (Finset.univ : Finset (Fin 3))
    hF (p := fun _ => (1 : ℝ) / 3) (by norm_num) (by
      intro i hi
      norm_num)
  simpa [F, Fin.prod_univ_succ, mul_assoc] using h

/-- The basic one-dimensional `3/4` kernel occurring after scaling ξ by δ.
Its integrability is the scalar fact behind all three APSSS Hölder cases. -/
theorem integrable_one_add_sq_rpow_three_quarters :
    Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 4)) := by
  convert
    (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (r := (3 : ℝ) / 2) (by norm_num)) using 1
  all_goals norm_num

/-- A fixed finite constant for the scaled `3/4` kernel. -/
def threeQuarterKernelConstant : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ‖((1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 4) : ℝ)‖ₑ

/-- The scalar kernel constant is finite. -/
theorem threeQuarterKernelConstant_ne_top : threeQuarterKernelConstant ≠ ⊤ := by
  unfold threeQuarterKernelConstant
  exact ne_of_lt integrable_one_add_sq_rpow_three_quarters.hasFiniteIntegral

/-- The sharp scalar comparison behind (6.22).  The rational exponential
produces the scale `sqrt (1+q)`, rather than merely being discarded. -/
theorem rational_exp_kernel_le_scaled (q : ℝ) (hq : 0 ≤ q) (x : ℝ) :
    (1 + x ^ 2) ^ (-(3 : ℝ) / 4) *
        Real.exp (-q * x ^ 2 / (1 + x ^ 2)) ≤
      (1 + (Real.sqrt (1 + q) * x) ^ 2) ^ (-(3 : ℝ) / 4) := by
  let B : ℝ := 1 + x ^ 2
  let D : ℝ := 1 + (1 + q) * x ^ 2
  have hB : 0 < B := by simp [B]; positivity
  have hD : 0 < D := by
    simp only [D]
    positivity
  have hBD : B ≤ D := by
    simp only [B, D]
    nlinarith [sq_nonneg x]
  let t : ℝ := q * x ^ 2 / B
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hmulExp : (1 + t) * Real.exp (-t) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
    rw [← Real.exp_add] at h
    simpa [add_comm] using h
  have hexp : Real.exp (-t) ≤ B / D := by
    have hone : 1 + t = D / B := by
      dsimp [t, B, D]
      field_simp
      ring
    rw [hone] at hmulExp
    apply (le_div_iff₀ hD).2
    calc
      Real.exp (-t) * D = B * (D / B * Real.exp (-t)) := by
        field_simp
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hmulExp hB.le
      _ = B := mul_one B
  have hpow : B ^ ((1 : ℝ) / 4) ≤ D ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hB.le hBD (by norm_num)
  have hmain :
      B ^ (-(3 : ℝ) / 4) * Real.exp (-t) ≤
        D ^ (-(3 : ℝ) / 4) := by
    calc
      B ^ (-(3 : ℝ) / 4) * Real.exp (-t) ≤
          B ^ (-(3 : ℝ) / 4) * (B / D) := by
            gcongr
      _ = B ^ ((1 : ℝ) / 4) / D := by
            calc
              B ^ (-(3 : ℝ) / 4) * (B / D) =
                  (B ^ (-(3 : ℝ) / 4) * B) / D := by ring
              _ = B ^ ((1 : ℝ) / 4) / D := by
                congr 1
                calc
                  B ^ (-(3 : ℝ) / 4) * B =
                      B ^ (-(3 : ℝ) / 4) * B ^ (1 : ℝ) := by rw [Real.rpow_one]
                  _ = B ^ (-(3 : ℝ) / 4 + 1) := (Real.rpow_add hB _ _).symm
                  _ = B ^ ((1 : ℝ) / 4) := by norm_num
      _ ≤ D ^ ((1 : ℝ) / 4) / D := by gcongr
      _ = D ^ (-(3 : ℝ) / 4) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg_one]
            rw [← Real.rpow_add hD]
            norm_num
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 + q)]
  convert hmain using 1
  all_goals dsimp [B, D, t]
  all_goals ring_nf

/-- Sharp integrated scalar estimate: the rational exponential gains exactly
the scale `(sqrt (1+q))⁻¹`.  The constant is the same fixed `3/4` kernel
constant for every `q`. -/
theorem lintegral_rational_exp_sharp (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((1 + x ^ 2) ^ (-(3 : ℝ) / 4) *
        Real.exp (-q * x ^ 2 / (1 + x ^ 2)))) ≤
      ENNReal.ofReal ((Real.sqrt (1 + q))⁻¹) * threeQuarterKernelConstant := by
  let k : ℝ → ℝ := fun x => (1 + x ^ 2) ^ (-(3 : ℝ) / 4)
  let f : ℝ → ℝ := fun x =>
    k x * Real.exp (-q * x ^ 2 / (1 + x ^ 2))
  let c : ℝ := Real.sqrt (1 + q)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hk : Integrable k := by
    simpa [k, Real.norm_eq_abs, sq_abs] using
      integrable_one_add_sq_rpow_three_quarters
  have hkc : Integrable (fun x : ℝ => k (c * x)) := by
    simpa only [smul_eq_mul] using hk.comp_smul hc.ne'
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    dsimp [f, k]
    positivity
  have hle : ∀ x, f x ≤ k (c * x) := by
    intro x
    simpa [f, k, c] using rational_exp_kernel_le_scaled q hq x
  have hf : Integrable f := by
    refine Integrable.mono' hkc (by
      dsimp [f, k]
      fun_prop) ?_
    exact ae_of_all _ fun x => by
      simpa only [Real.norm_of_nonneg (hf_nonneg x)] using hle x
  have hint : (∫ x, f x) ≤ c⁻¹ * ∫ x, k x := by
    calc
      (∫ x, f x) ≤ ∫ x, k (c * x) :=
        integral_mono hf hkc hle
      _ = |c⁻¹| * ∫ x, k x := by
        simpa [smul_eq_mul] using Measure.integral_comp_mul_left k c
      _ = c⁻¹ * ∫ x, k x := by rw [abs_of_pos (inv_pos.mpr hc)]
  have hf_ae : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ f x :=
    ae_of_all _ hf_nonneg
  have hk_ae : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ k x := by
    filter_upwards with x
    dsimp [k]
    positivity
  have hOf := ENNReal.ofReal_le_ofReal hint
  rw [ofReal_integral_eq_lintegral_ofReal hf hf_ae,
    ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
    ofReal_integral_eq_lintegral_ofReal hk hk_ae] at hOf
  have hconst :
      (∫⁻ x : ℝ, ENNReal.ofReal (k x)) = threeQuarterKernelConstant := by
    unfold threeQuarterKernelConstant
    apply lintegral_congr
    intro x
    rw [Real.enorm_of_nonneg (by
      dsimp [k]
      positivity)]
    simp only [k, Real.norm_eq_abs, sq_abs]
  rw [hconst] at hOf
  simpa [f, k, c] using hOf

/-- Sharp polynomial counterpart: an exponent `p ≥ 3/4` gains the scale
`sqrt (4p/3)`. -/
theorem rpow_kernel_le_scaled (p : ℝ) (hp : (3 : ℝ) / 4 ≤ p) (x : ℝ) :
    (1 + x ^ 2) ^ (-p) ≤
      (1 + (Real.sqrt (4 * p / 3) * x) ^ 2) ^ (-(3 : ℝ) / 4) := by
  let s : ℝ := 4 * p / 3
  have hs : 1 ≤ s := by
    dsimp [s]
    linarith
  have hbase : 0 < 1 + x ^ 2 := by positivity
  have hBernoulli : 1 + s * x ^ 2 ≤ (1 + x ^ 2) ^ s :=
    one_add_mul_self_le_rpow_one_add (by nlinarith [sq_nonneg x]) hs
  have hpow := Real.rpow_le_rpow_of_nonpos
    (by positivity : 0 < 1 + s * x ^ 2) hBernoulli
    (show (-(3 : ℝ) / 4) ≤ 0 by norm_num)
  have hrepack :
      ((1 + x ^ 2) ^ s) ^ (-(3 : ℝ) / 4) =
        (1 + x ^ 2) ^ (-p) := by
    rw [← Real.rpow_mul hbase.le]
    dsimp [s]
    congr 1
    ring
  rw [hrepack] at hpow
  rw [mul_pow, Real.sq_sqrt (by
    positivity)]
  simpa [s] using hpow

/-- Integrated form of `rpow_kernel_le_scaled`. -/
theorem lintegral_rpow_sharp (p : ℝ) (hp : (3 : ℝ) / 4 ≤ p) :
    (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-p))) ≤
      ENNReal.ofReal ((Real.sqrt (4 * p / 3))⁻¹) *
        threeQuarterKernelConstant := by
  let k : ℝ → ℝ := fun x => (1 + x ^ 2) ^ (-(3 : ℝ) / 4)
  let f : ℝ → ℝ := fun x => (1 + x ^ 2) ^ (-p)
  let c : ℝ := Real.sqrt (4 * p / 3)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hk : Integrable k := by
    simpa [k, Real.norm_eq_abs, sq_abs] using
      integrable_one_add_sq_rpow_three_quarters
  have hkc : Integrable (fun x : ℝ => k (c * x)) := by
    simpa only [smul_eq_mul] using hk.comp_smul hc.ne'
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    dsimp [f]
    positivity
  have hle : ∀ x, f x ≤ k (c * x) := by
    intro x
    simpa [f, k, c] using rpow_kernel_le_scaled p hp x
  have hf : Integrable f := by
    refine Integrable.mono' hkc ?_ ?_
    · dsimp [f]
      exact ((continuous_const.add (continuous_id.pow 2)).rpow_const
        (fun x => Or.inl (ne_of_gt (by
          nlinarith [sq_nonneg x] : (0 : ℝ) < 1 + x ^ 2)))).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simpa only [Real.norm_of_nonneg (hf_nonneg x)] using hle x
  have hint : (∫ x, f x) ≤ c⁻¹ * ∫ x, k x := by
    calc
      (∫ x, f x) ≤ ∫ x, k (c * x) := integral_mono hf hkc hle
      _ = |c⁻¹| * ∫ x, k x := by
        simpa [smul_eq_mul] using Measure.integral_comp_mul_left k c
      _ = c⁻¹ * ∫ x, k x := by rw [abs_of_pos (inv_pos.mpr hc)]
  have hf_ae : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ f x :=
    ae_of_all _ hf_nonneg
  have hk_ae : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ k x := by
    filter_upwards with x
    dsimp [k]
    positivity
  have hOf := ENNReal.ofReal_le_ofReal hint
  rw [ofReal_integral_eq_lintegral_ofReal hf hf_ae,
    ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
    ofReal_integral_eq_lintegral_ofReal hk hk_ae] at hOf
  have hconst :
      (∫⁻ x : ℝ, ENNReal.ofReal (k x)) = threeQuarterKernelConstant := by
    unfold threeQuarterKernelConstant
    apply lintegral_congr
    intro x
    rw [Real.enorm_of_nonneg (by
      dsimp [k]
      positivity)]
    simp only [k, Real.norm_eq_abs, sq_abs]
  rw [hconst] at hOf
  simpa [f, c] using hOf

/-- The polynomial half of the APSSS tail-coordinate estimate. -/
theorem tail_scalar_polynomial_bound (m α b : ℝ)
    (hm : 1 ≤ m) (hα : 0 < α) (hmα : m * α ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((1 + x ^ 2) ^ (-(3 / (4 * m * α) : ℝ)) *
        Real.exp (-(2 * b ^ 2 / α) * x ^ 2 / (1 + x ^ 2)))) ≤
      ENNReal.ofReal ((Real.sqrt (1 / (m * α)))⁻¹) *
        threeQuarterKernelConstant := by
  have hp : (3 : ℝ) / 4 ≤ 3 / (4 * m * α) := by
    have hmαpos : 0 < m * α := mul_pos (lt_of_lt_of_le zero_lt_one hm) hα
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4)
      (by positivity : (0 : ℝ) < 4 * m * α)).2
    nlinarith
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((1 + x ^ 2) ^ (-(3 / (4 * m * α) : ℝ)) *
        Real.exp (-(2 * b ^ 2 / α) * x ^ 2 / (1 + x ^ 2)))) ≤
        ∫⁻ x : ℝ, ENNReal.ofReal
          ((1 + x ^ 2) ^ (-(3 / (4 * m * α) : ℝ)) : ℝ) := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      have hexponent :
          -(2 * b ^ 2 / α) * x ^ 2 / (1 + x ^ 2) ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
            (sq_nonneg x)) (by positivity)
      exact mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _)
        (Real.exp_le_one_iff.mpr hexponent)
    _ ≤ ENNReal.ofReal ((Real.sqrt (4 * (3 / (4 * m * α)) / 3))⁻¹) *
        threeQuarterKernelConstant :=
      lintegral_rpow_sharp (3 / (4 * m * α)) hp
    _ = ENNReal.ofReal ((Real.sqrt (1 / (m * α)))⁻¹) *
        threeQuarterKernelConstant := by
      congr 2
      congr 2
      field_simp

/-- The exponential half of the APSSS tail-coordinate estimate. -/
theorem tail_scalar_exponential_bound (m α b : ℝ)
    (hm : 1 ≤ m) (hα : 0 < α) (hmα : m * α ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((1 + x ^ 2) ^ (-(3 / (4 * m * α) : ℝ)) *
        Real.exp (-(2 * b ^ 2 / α) * x ^ 2 / (1 + x ^ 2)))) ≤
      ENNReal.ofReal ((Real.sqrt (1 + 2 * b ^ 2 / α))⁻¹) *
        threeQuarterKernelConstant := by
  have hp : (3 : ℝ) / 4 ≤ 3 / (4 * m * α) := by
    have hmαpos : 0 < m * α := mul_pos (lt_of_lt_of_le zero_lt_one hm) hα
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4)
      (by positivity : (0 : ℝ) < 4 * m * α)).2
    nlinarith
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((1 + x ^ 2) ^ (-(3 / (4 * m * α) : ℝ)) *
        Real.exp (-(2 * b ^ 2 / α) * x ^ 2 / (1 + x ^ 2)))) ≤
        ∫⁻ x : ℝ, ENNReal.ofReal
          ((1 + x ^ 2) ^ (-(3 : ℝ) / 4) *
            Real.exp (-(2 * b ^ 2 / α) * x ^ 2 / (1 + x ^ 2))) := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le
          (by nlinarith [sq_nonneg x] : (1 : ℝ) ≤ 1 + x ^ 2)
          (by linarith [hp]))
        (Real.exp_pos _).le
    _ ≤ ENNReal.ofReal ((Real.sqrt (1 + 2 * b ^ 2 / α))⁻¹) *
        threeQuarterKernelConstant :=
      lintegral_rational_exp_sharp (2 * b ^ 2 / α) (by positivity)

/-- The polynomial scale is at most `sqrt 3 * sqrt α` in the three APSSS
cases (`m = 3-r`, hence `1 ≤ m ≤ 3`). -/
theorem polynomial_scale_le (m α : ℝ) (hm : 1 ≤ m) (hm3 : m ≤ 3)
    (_hα : 0 < α) :
    (Real.sqrt (1 / (m * α)))⁻¹ ≤ Real.sqrt 3 * Real.sqrt α := by
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1) (m * α), Real.sqrt_one,
    one_div, inv_inv]
  rw [Real.sqrt_mul hm0]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hm3) (Real.sqrt_nonneg _)

/-- For `|b| ≥ 1`, the exponential scale supplies the missing `1/|b|`.
This is the sharp parameter bridge in APSSS (6.22). -/
theorem exponential_scale_le (α b : ℝ) (hα : 0 < α)
    (hb : 1 ≤ |b|) :
    (Real.sqrt (1 + 2 * b ^ 2 / α))⁻¹ ≤ Real.sqrt α / |b| := by
  have hbpos : 0 < |b| := lt_of_lt_of_le zero_lt_one hb
  have hbase : b ^ 2 / α ≤ 1 + 2 * b ^ 2 / α := by
    apply (div_le_iff₀ hα).2
    field_simp
    nlinarith [sq_nonneg b]
  have hsqrt := Real.sqrt_le_sqrt hbase
  have hsqrtpos : 0 < Real.sqrt (b ^ 2 / α) := by
    apply Real.sqrt_pos.2
    exact div_pos (sq_pos_of_ne_zero (abs_pos.mp hbpos)) hα
  have hinv :
      (Real.sqrt (1 + 2 * b ^ 2 / α))⁻¹ ≤ (Real.sqrt (b ^ 2 / α))⁻¹ :=
    inv_anti₀ hsqrtpos hsqrt
  calc
    (Real.sqrt (1 + 2 * b ^ 2 / α))⁻¹ ≤ (Real.sqrt (b ^ 2 / α))⁻¹ := hinv
    _ = Real.sqrt α / |b| := by
      rw [Real.sqrt_div (sq_nonneg b) α, Real.sqrt_sq_eq_abs]
      field_simp

/-- Complete sharp scalar bound needed after the second Hölder step.  The
constant `sqrt 3 * threeQuarterKernelConstant` is absolute, and the displayed
dependence is exactly `sqrt α / max(1,|b|)`. -/
theorem tail_scalar_sharp (m α b : ℝ)
    (hm : 1 ≤ m) (hm3 : m ≤ 3) (hα : 0 < α) (hmα : m * α ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((1 + x ^ 2) ^ (-(3 / (4 * m * α) : ℝ)) *
        Real.exp (-(2 * b ^ 2 / α) * x ^ 2 / (1 + x ^ 2)))) ≤
      ENNReal.ofReal
          (Real.sqrt 3 * Real.sqrt α / max 1 |b|) *
        threeQuarterKernelConstant := by
  by_cases hb : |b| ≤ 1
  · have hscale := polynomial_scale_le m α hm hm3 hα
    have hpoly := tail_scalar_polynomial_bound m α b hm hα hmα
    rw [max_eq_left hb]
    refine hpoly.trans ?_
    gcongr
    simpa [div_one] using hscale
  · have hb' : 1 ≤ |b| := le_of_not_ge hb
    have hscale := exponential_scale_le α b hα hb'
    have hexp := tail_scalar_exponential_bound m α b hm hα hmα
    rw [max_eq_right hb']
    have hsqrt3 : 1 ≤ Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    have hscale' :
        (Real.sqrt (1 + 2 * b ^ 2 / α))⁻¹ ≤
          Real.sqrt 3 * Real.sqrt α / |b| := by
      calc
        _ ≤ Real.sqrt α / |b| := hscale
        _ ≤ Real.sqrt 3 * Real.sqrt α / |b| := by
          apply div_le_div_of_nonneg_right _ (abs_nonneg b)
          exact le_mul_of_one_le_left (Real.sqrt_nonneg α) hsqrt3
    refine hexp.trans ?_
    gcongr

/-- The sharp scalar estimate specialized to the three residual Hölder
weights in APSSS (6.21).  This is the form consumed by the assembly of
`I'`: `m` has been replaced by `3-r`, while its two range hypotheses have
been discharged from `r ≤ 2`. -/
theorem tail_scalar_sharp_of_r (r : ℕ) (hr : r ≤ 2) (α b : ℝ)
    (hα : 0 < α) (hweight : ((3 - r : ℕ) : ℝ) * α ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((1 + x ^ 2) ^
          (-(3 / (4 * ((3 - r : ℕ) : ℝ) * α) : ℝ)) *
        Real.exp (-(2 * b ^ 2 / α) * x ^ 2 / (1 + x ^ 2)))) ≤
      ENNReal.ofReal
          (Real.sqrt 3 * Real.sqrt α / max 1 |b|) *
        threeQuarterKernelConstant := by
  have hm : (1 : ℝ) ≤ ((3 - r : ℕ) : ℝ) := by
    interval_cases r <;> norm_num
  have hm3 : ((3 - r : ℕ) : ℝ) ≤ 3 := by
    interval_cases r <;> norm_num
  exact tail_scalar_sharp (((3 - r : ℕ) : ℝ)) α b hm hm3 hα hweight

/-- Substitution of the APSSS weight
`α = E²(1+b²)/ν²` in the sharp scalar factor.  The quotient by
`max(1,|b|)` cancels the possible growth of `sqrt (1+b²)`, leaving the
exact absolute factor `sqrt 2 * |E| / ν` used in (6.22). -/
theorem sqrt_weight_div_max_le (E b ν : ℝ) (hν : 0 < ν) :
    Real.sqrt (E ^ 2 * (1 + b ^ 2) / ν ^ 2) / max 1 |b| ≤
      Real.sqrt 2 * |E| / ν := by
  have hmaxpos : 0 < max (1 : ℝ) |b| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsquare :
      1 + b ^ 2 ≤ 2 * (max (1 : ℝ) |b|) ^ 2 := by
    have h₁ : (1 : ℝ) ≤ max 1 |b| := le_max_left _ _
    have hb : |b| ≤ max 1 |b| := le_max_right _ _
    nlinarith [mul_self_le_mul_self zero_le_one h₁,
      mul_self_le_mul_self (abs_nonneg b) hb, sq_abs b]
  have hsqrt :
      Real.sqrt (1 + b ^ 2) ≤ Real.sqrt 2 * max (1 : ℝ) |b| := by
    have h := Real.sqrt_le_sqrt hsquare
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq hmaxpos.le] at h
    exact h
  have hsqrt_weight :
      Real.sqrt (E ^ 2 * (1 + b ^ 2) / ν ^ 2) =
        |E| * Real.sqrt (1 + b ^ 2) / ν := by
    rw [Real.sqrt_div (mul_nonneg (sq_nonneg E) (by positivity)) (ν ^ 2),
      Real.sqrt_mul (sq_nonneg E), Real.sqrt_sq_eq_abs,
      Real.sqrt_sq_eq_abs, abs_of_pos hν]
  rw [hsqrt_weight]
  have hratio :
      Real.sqrt (1 + b ^ 2) / max (1 : ℝ) |b| ≤ Real.sqrt 2 := by
    apply (div_le_iff₀ hmaxpos).2
    simpa [mul_comm] using hsqrt
  calc
    (|E| * Real.sqrt (1 + b ^ 2) / ν) / max (1 : ℝ) |b| =
        (|E| / ν) * (Real.sqrt (1 + b ^ 2) / max (1 : ℝ) |b|) := by ring
    _ ≤ (|E| / ν) * Real.sqrt 2 := by
      exact mul_le_mul_of_nonneg_left hratio (div_nonneg (abs_nonneg E) hν.le)
    _ = Real.sqrt 2 * |E| / ν := by ring

/-- Direct (6.22) specialization with
`α = E²(1+b²)/ν²`.  It exposes the factor `|E|/ν` which cancels the
Jacobian factor `1/(|E| sqrt δ)` once the choice
`δ = 1/(10ν²)` is substituted in the shifted integral. -/
theorem tail_scalar_sharp_weighted (r : ℕ) (hr : r ≤ 2)
    (E b ν : ℝ) (hE : E ≠ 0) (hν : 0 < ν)
    (hweight :
      ((3 - r : ℕ) : ℝ) * (E ^ 2 * (1 + b ^ 2) / ν ^ 2) ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((1 + x ^ 2) ^
          (-(3 / (4 * ((3 - r : ℕ) : ℝ) *
            (E ^ 2 * (1 + b ^ 2) / ν ^ 2)) : ℝ)) *
        Real.exp
          (-(2 * b ^ 2 / (E ^ 2 * (1 + b ^ 2) / ν ^ 2)) *
            x ^ 2 / (1 + x ^ 2)))) ≤
      ENNReal.ofReal
          (Real.sqrt 3 * (Real.sqrt 2 * |E| / ν)) *
        threeQuarterKernelConstant := by
  have hα : 0 < E ^ 2 * (1 + b ^ 2) / ν ^ 2 := by
    positivity
  have htail := tail_scalar_sharp_of_r r hr
    (E ^ 2 * (1 + b ^ 2) / ν ^ 2) b hα hweight
  refine htail.trans ?_
  gcongr
  have h := mul_le_mul_of_nonneg_left (sqrt_weight_div_max_le E b ν hν)
    (Real.sqrt_nonneg 3)
  simpa [div_eq_mul_inv, mul_assoc] using h

end PSSSNative.BlockBand.PSSS
