module

public import BlockBand.Model.Parameters
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The scalar Gaussian kernel

The `Gaussian(0,σ²)` scalar convolution `h(x) = E_t w(scale(x+t-E))`, its
integrability and the positive-part exponential kernel bound; the capped power series
`Σ_m min(ε, C(a/(1+m))^q) ≤ (2^q C^{1/q}/(q-1)) a ε^{1-1/q}`; `σ² = c/(NW)`, `Nσ = √(cn)`;
kernel `≤ C/√n`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace BlockBand.Window.Transfer

noncomputable def scalarVariance (σ : ℝ) : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩

noncomputable def scalarConvolution (w : ℝ → ℝ) (scale E σ x : ℝ) : ℝ :=
  ∫ t, w (scale * (x + t - E)) ∂gaussianReal 0 (scalarVariance σ)

/-- Affine window mass: for integrable `w` with `∫ w = 1` and `scale > 0`, the function
`t ↦ w(scale(x + t - E))` is Lebesgue integrable with integral `scale⁻¹`. -/
theorem affine_window_integral (w : ℝ → ℝ) (hw : Integrable w)
    (hunit : ∫ y, w y = 1) (scale E x : ℝ) (hs : 0 < scale) :
    Integrable (fun t => w (scale * (x + t - E))) ∧
      (∫ t, w (scale * (x + t - E))) = scale⁻¹ := by
  have heq : (fun t => w (scale * (x + t - E))) =
      (fun t => w (scale * (t + (x - E)))) := by
    funext t
    congr 1
    ring
  rw [heq]
  refine ⟨(hw.comp_mul_left' hs.ne').comp_add_right (x - E), ?_⟩
  rw [integral_add_right_eq_self (fun u => w (scale * u)) (x - E), Measure.integral_comp_mul_left, hunit,
    abs_of_pos (inv_pos.mpr hs)]
  simp

/-- If `w(scale(x + t - E)) ≠ 0` for a window supported in `[-M, M]`, then
`|t| ≥ max(|x - E| - M/scale, 0)`. -/
theorem scalar_gap_le_abs (w : ℝ → ℝ) (scale E M x t : ℝ) (hs : 0 < scale)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M)
    (hwt : w (scale * (x + t - E)) ≠ 0) :
    max (|x - E| - M / scale) 0 ≤ |t| := by
  have hw := hsupp _ hwt
  rw [abs_mul, abs_of_pos hs] at hw
  have hwin : |x + t - E| ≤ M / scale :=
    (le_div_iff₀ hs).mpr (by simpa [mul_comm] using hw)
  have htriangle : |x - E| ≤ |x + t - E| + |t| := by
    have hh := abs_sub (x + t - E) t
    simpa only [show x + t - E - t = x - E by ring] using hh
  apply max_le
  · linarith
  · exact abs_nonneg t

/-- The Gaussian density of variance `σ²` on the support of the window is bounded by
`exp(-max(|x - E| - M/scale, 0)²/(2σ²))/√(2πσ²)`. -/
theorem scalar_density_window_bound (w : ℝ → ℝ) (scale E σ M x t : ℝ)
    (hs : 0 < scale) (hσ : 0 < σ) (hw0 : ∀ y, 0 ≤ w y)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M) :
    gaussianPDFReal 0 (scalarVariance σ) t * w (scale * (x + t - E)) ≤
      (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ *
        Real.exp (-(max (|x - E| - M / scale) 0) ^ 2 / (2 * σ ^ 2)) *
        w (scale * (x + t - E)) := by
  by_cases hzero : w (scale * (x + t - E)) = 0
  · simp [hzero]
  have hgap := scalar_gap_le_abs w scale E M x t hs hsupp hzero
  have hgap0 : 0 ≤ max (|x - E| - M / scale) 0 := le_max_right _ _
  have hsq : (max (|x - E| - M / scale) 0) ^ 2 ≤ t ^ 2 := by
    have habs := sq_abs t
    nlinarith [sq_nonneg (|t| - max (|x - E| - M / scale) 0)]
  apply mul_le_mul_of_nonneg_right _ (hw0 _)
  unfold gaussianPDFReal scalarVariance
  simp only [sub_zero]
  change (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-t ^ 2 / (2 * σ ^ 2)) ≤ _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact (div_le_div_iff_of_pos_right (show 0 < 2 * σ ^ 2 by positivity)).mpr (by linarith)

/-- The scalar convolution bound for a normalized, nonnegative, integrable window supported in
`[-M, M]` and the law `Gaussian(0, σ²)`: integrability, nonnegativity and
`h(x) ≤ exp(-max(|x - E| - M/scale, 0)²/(2σ²))/(scale σ √(2π))`. -/
theorem scalar_convolution_bound (w : ℝ → ℝ) (hw : Measurable w) (hwi : Integrable w)
    (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (scale E σ M x : ℝ) (hs : 0 < scale) (hσ : 0 < σ)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M) :
    Integrable (fun t => w (scale * (x + t - E))) (gaussianReal 0 (scalarVariance σ)) ∧
    0 ≤ scalarConvolution w scale E σ x ∧
    scalarConvolution w scale E σ x ≤
      Real.exp (-(max (|x - E| - M / scale) 0) ^ 2 / (2 * σ ^ 2)) /
        (scale * σ * Real.sqrt (2 * Real.pi)) := by
  let B := (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ *
    Real.exp (-(max (|x - E| - M / scale) 0) ^ 2 / (2 * σ ^ 2))
  have hB0 : 0 ≤ B := by unfold B; positivity
  have haff := affine_window_integral w hwi hunit scale E x hs
  have hbound : ∀ t, gaussianPDFReal 0 (scalarVariance σ) t * w (scale * (x + t - E)) ≤
      B * w (scale * (x + t - E)) := fun t =>
    scalar_density_window_bound w scale E σ M x t hs hσ hw0 hsupp
  have hwm : Measurable (fun t => w (scale * (x + t - E))) := hw.comp (by fun_prop)
  have hpm : Measurable (fun t => gaussianPDFReal 0 (scalarVariance σ) t *
      w (scale * (x + t - E))) := (measurable_gaussianPDFReal _ _).mul hwm
  have hp0 : ∀ t, 0 ≤ gaussianPDFReal 0 (scalarVariance σ) t *
      w (scale * (x + t - E)) := fun t => mul_nonneg (gaussianPDFReal_nonneg _ _ _) (hw0 _)
  have hprod : Integrable (fun t => gaussianPDFReal 0 (scalarVariance σ) t *
      w (scale * (x + t - E))) :=
    (haff.1.const_mul B).mono' hpm.aestronglyMeasurable (ae_of_all volume fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hp0 t)] using hbound t)
  have hv : scalarVariance σ ≠ 0 := by
    intro hz
    have hh := congrArg (fun v : ℝ≥0 => (v : ℝ)) hz
    change σ ^ 2 = 0 at hh
    nlinarith
  have hscalar : Integrable (fun t => w (scale * (x + t - E)))
      (gaussianReal 0 (scalarVariance σ)) := by
    rw [gaussianReal_of_var_ne_zero _ hv]
    apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all volume fun t => gaussianPDF_lt_top)).mpr
    simpa only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
      smul_eq_mul] using hprod
  refine ⟨hscalar, integral_nonneg fun t => hw0 _, ?_⟩
  unfold scalarConvolution
  rw [integral_gaussianReal_eq_integral_smul hv]
  change (∫ t, gaussianPDFReal 0 (scalarVariance σ) t * w (scale * (x + t - E))) ≤ _
  calc
    _ ≤ ∫ t, B * w (scale * (x + t - E)) :=
      integral_mono hprod (haff.1.const_mul B) hbound
    _ = B * scale⁻¹ := by rw [integral_const_mul, haff.2]
    _ = _ := by
      unfold B
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), Real.sqrt_sq_eq_abs,
        abs_of_pos hσ]
      field_simp

/-- The scalar convolution bound for a continuous compactly supported window. -/
theorem scalar_convolution_bound_continuous (w : ℝ → ℝ) (hw : Continuous w)
    (hcompact : HasCompactSupport w) (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (scale E σ M x : ℝ) (hs : 0 < scale) (hσ : 0 < σ)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M) :
    Integrable (fun t => w (scale * (x + t - E))) (gaussianReal 0 (scalarVariance σ)) ∧
    0 ≤ scalarConvolution w scale E σ x ∧
    scalarConvolution w scale E σ x ≤
      Real.exp (-(max (|x - E| - M / scale) 0) ^ 2 / (2 * σ ^ 2)) /
        (scale * σ * Real.sqrt (2 * Real.pi)) :=
  scalar_convolution_bound w hw.measurable (hw.integrable_of_hasCompactSupport hcompact)
    hunit hw0 scale E σ M x hs hσ hsupp

/-- Shifted power tail: `x ↦ (B + x)^{-q}` is integrable on `(0, ∞)`, with its integral, for
`q > 1` and `B > 0`. -/
theorem shifted_power_tail (q B : ℝ) (hq : 1 < q) (hB : 0 < B) :
    IntegrableOn (fun x : ℝ => (B + x) ^ (-q)) (Ioi 0) ∧
      (∫ x : ℝ in Ioi 0, (B + x) ^ (-q)) = B ^ (1 - q) / (q - 1) := by
  have hi := integrableOn_Ioi_rpow_of_lt (show -q < -1 by linarith) hB
  let g : ℝ → ℝ := (Ioi B).indicator (fun x => x ^ (-q))
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  have heq : (fun x => g (B + x)) = (Ioi 0).indicator (fun x : ℝ => (B + x) ^ (-q)) := by
    funext x
    by_cases hx : 0 < x
    · simp [g, hx, show B < B + x by linarith]
    · simp [g, hx, show ¬ B < B + x by linarith]
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).mp ?_, ?_⟩
  · rw [← heq]
    exact hg.comp_add_left B
  · rw [← integral_indicator measurableSet_Ioi, ← heq, integral_add_left_eq_self g B]
    rw [integral_indicator measurableSet_Ioi,
      integral_Ioi_rpow_of_lt (show -q < -1 by linarith) hB]
    have he : -q + 1 = 1 - q := by ring
    rw [he]
    have hd : 1 - q = -(q - 1) := by ring
    rw [hd, div_neg]
    ring

/-- A capped power is dominated by a smooth power tail, under `K ≤ ε B^q`. -/
theorem capped_power_le_smooth (ε B K r q : ℝ) (hε : 0 ≤ ε) (hB : 0 < B)
    (hr : 0 < r) (hq : 0 < q) (hK : K ≤ ε * B ^ q) :
    min ε (K / r ^ q) ≤ ε * (2 * B) ^ q * (B + r) ^ (-q) := by
  have heq : ε * (2 * B) ^ q * (B + r) ^ (-q) = ε * (2 * B / (B + r)) ^ q := by
    rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity) q]
    ring
  rw [heq]
  by_cases hrB : r ≤ B
  · have hratio : 1 ≤ 2 * B / (B + r) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    exact (min_le_left _ _).trans (by nlinarith [Real.one_le_rpow hratio hq.le])
  · have hratio : B / r ≤ 2 * B / (B + r) := by
      apply (div_le_div_iff₀ hr (by positivity)).mpr
      nlinarith
    calc
      _ ≤ K / r ^ q := min_le_right _ _
      _ ≤ ε * B ^ q / r ^ q := div_le_div_of_nonneg_right hK (Real.rpow_nonneg hr.le q)
      _ = ε * (B / r) ^ q := by rw [Real.div_rpow hB.le hr.le]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hratio hq.le) hε

/-- The capped power series bound, by the integral test (`q > 1`), with summability. -/
theorem capped_power_series (ε B K q : ℝ) (hε : 0 ≤ ε) (hB : 0 < B)
    (hK0 : 0 ≤ K) (hq : 1 < q) (hK : K ≤ ε * B ^ q) :
    Summable (fun m : ℕ => min ε (K / ((m : ℝ) + 1) ^ q)) ∧
      (∑' m : ℕ, min ε (K / ((m : ℝ) + 1) ^ q)) ≤
        ε * (2 : ℝ) ^ q * B / (q - 1) := by
  let f : ℝ → ℝ := fun x => ε * (2 * B) ^ q * (B + x) ^ (-q)
  have hfanti : AntitoneOn f (Ici 0) := by
    intro x hx y hy hxy
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx]) (by linarith) (by linarith)
  have hfint : IntegrableOn f (Ioi 0) :=
    (shifted_power_tail q B hq hB).1.const_mul _
  have hf0 : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x := by
    intro x hx
    change 0 < x at hx
    unfold f
    positivity
  have hfsum : Summable (fun n : ℕ => f (n + 1)) := by
    have hsumn : Summable (fun n : ℕ => f (n : ℝ)) :=
      hfanti.summable_of_integrableOn_Ioi_zero hfint hf0
    have hinj : Function.Injective (fun n : ℕ => n + 1) := fun n m h => Nat.add_right_cancel h
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using (hsumn.comp_injective hinj : Summable ((fun n : ℕ => f (n : ℝ)) ∘ (fun n : ℕ => n + 1)))
  have hdom : ∀ m : ℕ, min ε (K / ((m : ℝ) + 1) ^ q) ≤ f (m + 1) := fun m =>
    capped_power_le_smooth ε B K _ q hε hB (by positivity) (by linarith) hK
  have hc0 : ∀ m : ℕ, 0 ≤ min ε (K / ((m : ℝ) + 1) ^ q) := by
    intro m
    positivity
  have hcsum := Summable.of_nonneg_of_le hc0 hdom hfsum
  refine ⟨hcsum, ?_⟩
  calc
    _ ≤ ∑' m : ℕ, f (m + 1) := Summable.tsum_le_tsum hdom hcsum hfsum
    _ ≤ ∫ x in Ioi (0 : ℝ), f x := by simpa only [Nat.cast_add, Nat.cast_one] using hfanti.tsum_add_one_le_integral hfint hf0
    _ = ε * (2 : ℝ) ^ q * B / (q - 1) := by
      rw [integral_const_mul, (shifted_power_tail q B hq hB).2]
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) hB.le,
        show 1 - q = -q + 1 by ring, Real.rpow_add hB, Real.rpow_neg hB.le,
        Real.rpow_one]
      field_simp

/-- The rank-tail series of the window transfer theorem: for `q > 1`, `a ≥ 1` and `0 < ε ≤ 1`,
`Σ_{m ≥ 0} min(ε, C (a/(1+m))^q) ≤ (2^q C^{1/q}/(q-1)) a ε^{1-1/q}`, with summability. -/
theorem rank_tail_series_bound (q a ε C : ℝ) (hq : 1 < q) (ha : 1 ≤ a)
    (hε : 0 < ε) (_hε1 : ε ≤ 1) (hC : 0 ≤ C) :
    Summable (fun m : ℕ => min ε (C * (a / (1 + (m : ℝ))) ^ q)) ∧
      (∑' m : ℕ, min ε (C * (a / (1 + (m : ℝ))) ^ q)) ≤
        ((2 : ℝ) ^ q * C ^ (1 / q) / (q - 1)) * a * ε ^ (1 - 1 / q) := by
  by_cases hCzero : C = 0
  · subst C
    simp only [zero_mul, min_eq_right hε.le, tsum_zero]
    constructor
    · exact summable_zero
    · have hq1 : 0 < q - 1 := by linarith
      have ha0 : 0 ≤ a := by linarith
      positivity
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
  have hap : 0 < a := by linarith
  have hqp : 0 < q := by linarith
  let B : ℝ := a * (C / ε) ^ (1 / q)
  have hBp : 0 < B := by unfold B; positivity
  have hBq : B ^ q = a ^ q * (C / ε) := by
    unfold B
    rw [Real.mul_rpow hap.le (Real.rpow_nonneg (div_nonneg hC hε.le) (1 / q)), ← Real.rpow_mul (div_nonneg hC hε.le)]
    simp [hqp.ne']
  have hmass : C * a ^ q ≤ ε * B ^ q := by
    rw [hBq]
    have heq : ε * (a ^ q * (C / ε)) = C * a ^ q := by field_simp
    exact le_of_eq heq.symm
  have hseries := capped_power_series ε B (C * a ^ q) q hε.le hBp
    (by positivity) hq hmass
  have hterms : (fun m : ℕ => min ε (C * (a / (1 + (m : ℝ))) ^ q)) =
      (fun m : ℕ => min ε (C * a ^ q / ((m : ℝ) + 1) ^ q)) := by
    funext m
    rw [Real.div_rpow hap.le (by positivity)]
    congr 1
    rw [add_comm 1 (m : ℝ)]
    ring
  rw [hterms]
  refine ⟨hseries.1, hseries.2.trans_eq ?_⟩
  have heps : ε * (C / ε) ^ (1 / q) = C ^ (1 / q) * ε ^ (1 - 1 / q) := by
    rw [Real.div_rpow hC hε.le, Real.rpow_sub hε 1 (1 / q), Real.rpow_one]
    field_simp
  unfold B
  have heq : ε * (2 : ℝ) ^ q * (a * (C / ε) ^ (1 / q)) / (q - 1) =
      ((2 : ℝ) ^ q / (q - 1)) * a * (ε * (C / ε) ^ (1 / q)) := by ring
  rw [heq, heps]
  ring

/-- The standard deviation `σ = √(c/(NW))` of the scalar trace component of the physical model. -/
noncomputable def originalScalarSigma (p : BlockBand.Parameters) : ℝ :=
  Real.sqrt (p.c / ((p.N : ℝ) * (p.W : ℝ)))

/-- `σ > 0`. -/
theorem originalScalarSigma_pos (p : BlockBand.Parameters) : 0 < originalScalarSigma p := by
  unfold originalScalarSigma
  apply Real.sqrt_pos.mpr
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  exact div_pos p.c_pos (mul_pos hN hW)

/-- `σ² = c/(NW)`. -/
theorem originalScalarSigma_sq (p : BlockBand.Parameters) :
    originalScalarSigma p ^ 2 = p.c / ((p.N : ℝ) * (p.W : ℝ)) := by
  unfold originalScalarSigma
  apply Real.sq_sqrt
  have hc : 0 < p.c := p.c_pos
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  positivity

/-- `σ² = c/(nW²)`. -/
theorem originalScalarSigma_sq_block (p : BlockBand.Parameters) :
    originalScalarSigma p ^ 2 = p.c / ((p.n : ℝ) * (p.W : ℝ) ^ 2) := by
  rw [originalScalarSigma_sq]
  simp only [BlockBand.Parameters.N, Nat.cast_mul]
  congr 1
  ring

/-- `Nσ = √(cn)`. -/
theorem dimension_mul_originalScalarSigma (p : BlockBand.Parameters) :
    (p.N : ℝ) * originalScalarSigma p = Real.sqrt (p.c * (p.n : ℝ)) := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hsq : ((p.N : ℝ) * originalScalarSigma p) ^ 2 = p.c * (p.n : ℝ) := by
    rw [mul_pow, originalScalarSigma_sq]
    field_simp
    simp only [BlockBand.Parameters.N, Nat.cast_mul]
    ring
  calc
    _ = Real.sqrt (((p.N : ℝ) * originalScalarSigma p) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hN (originalScalarSigma_pos p))]
    _ = _ := congrArg Real.sqrt hsq

/-- The scalar kernel at the physical variance `σ²` for a unit-mass continuous compactly supported
window at microscopic scale `Nρ`, for every deterministic `x`:
`0 ≤ h(x) ≤ (ρ√(2π))⁻¹/(Nσ) · exp(-max(|x - E| - M/(Nρ), 0)²/(2σ²))`. -/
theorem original_scalar_kernel_bound (p : BlockBand.Parameters) (ρ E M x : ℝ) (hρ : 0 < ρ)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M) :
    0 ≤ scalarConvolution w ((p.N : ℝ) * ρ) E (originalScalarSigma p) x ∧
    scalarConvolution w ((p.N : ℝ) * ρ) E (originalScalarSigma p) x ≤
      (ρ * Real.sqrt (2 * Real.pi))⁻¹ / ((p.N : ℝ) * originalScalarSigma p) *
        Real.exp (-(max (|x - E| - M / ((p.N : ℝ) * ρ)) 0) ^ 2 /
          (2 * originalScalarSigma p ^ 2)) := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hh := scalar_convolution_bound_continuous w hw hcompact hunit hw0
    ((p.N : ℝ) * ρ) E (originalScalarSigma p) M x (mul_pos hN hρ)
    (originalScalarSigma_pos p) hsupp
  refine ⟨hh.2.1, hh.2.2.trans_eq ?_⟩
  field_simp

/-- The uniform bound `h(x) ≤ (ρ √(2π) √c)⁻¹/√n` on the scalar kernel. -/
theorem original_scalar_kernel_uniform (p : BlockBand.Parameters) (ρ E M x : ℝ) (hρ : 0 < ρ)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M) :
    scalarConvolution w ((p.N : ℝ) * ρ) E (originalScalarSigma p) x ≤
      (ρ * Real.sqrt (2 * Real.pi) * Real.sqrt p.c)⁻¹ / Real.sqrt (p.n : ℝ) := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hcn : 0 < p.c := p.c_pos
  have hσ : 0 < originalScalarSigma p := originalScalarSigma_pos p
  have hh := (original_scalar_kernel_bound p ρ E M x hρ w hw hcompact hunit hw0 hsupp).2
  have he : Real.exp (-(max (|x - E| - M / ((p.N : ℝ) * ρ)) 0) ^ 2 /
      (2 * originalScalarSigma p ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
    positivity
  calc
    _ ≤ (ρ * Real.sqrt (2 * Real.pi))⁻¹ / ((p.N : ℝ) * originalScalarSigma p) :=
      hh.trans (mul_le_of_le_one_right (by positivity) he)
    _ = _ := by
      rw [dimension_mul_originalScalarSigma, Real.sqrt_mul hcn.le]
      field_simp

end BlockBand.Window.Transfer
