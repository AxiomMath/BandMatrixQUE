module

public import BlockBand.Endpoints.Sine.Law
public import BlockBand.Endpoints.Sine.Intensity

/-!
# Reflection and dilation stability of the sine Laplace functional

* `sineLaplaceFunctional_reflect`: reflection preserves the sine law, `L_sine(f(-·)) = L_sine(f)`
  (the sine kernel is even and Lebesgue measure on `ℝ^k` is reflection invariant).
* `abs_sineLaplace_sub_le`: if `|g - f| ≤ εχ` pointwise (nonnegative `C_c` tests), then
  `|L_sine(g) - L_sine(f)| ≤ ε ∫ χ`, through the intensity-one sine law (`exists_isSineLaw`,
  `integral_coordinate_eq_of_fredholm`).
* `exists_dilation_sandwich`: since the density rescaling tends uniformly to one, for a
  nonnegative `C_c` test `f` and `η > 0` there are `δ ∈ (0, 1/2]` and nonnegative `C_c` tests
  `g⁻ ≤ f(r·) ≤ g⁺` for all `|r - 1| ≤ δ`, with `|L_sine(g^±) - L_sine(f)| ≤ η`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter
open scoped ENNReal Topology

/-!
## Reflection
-/

/-- The reflected test `x ↦ f(-x)`. -/
def reflectTest (f : CompactlySupportedContinuousMap ℝ ℝ) : CompactlySupportedContinuousMap ℝ ℝ :=
  ⟨⟨fun x => f (-x), f.continuous.comp continuous_neg⟩,
    f.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)⟩

@[simp] theorem reflectTest_apply (f : CompactlySupportedContinuousMap ℝ ℝ) (x : ℝ) :
    reflectTest f x = f (-x) := rfl

theorem sineLaplaceFunctional_reflect (f : CompactlySupportedContinuousMap ℝ ℝ) :
    sineLaplaceFunctional (reflectTest f) = sineLaplaceFunctional f := by
  unfold sineLaplaceFunctional
  congr 1
  funext k
  congr 1
  rw [← volume_pi]
  rw [← integral_neg_eq_self (fun x : Fin k → ℝ =>
    Matrix.det (fun i j : Fin k => sineKernel (x i) (x j)) *
      ∏ i : Fin k, (1 - Real.exp (-f (x i)))) volume]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [reflectTest_apply, Pi.neg_apply]
  congr 1
  congr 1
  funext a b
  simp only [sineKernel]
  rw [show Real.pi * (-x a - -x b) = -(Real.pi * (x a - x b)) by ring, Real.sinc_neg]

/-!
## Stability under small uniform perturbations
-/

theorem abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]; exact this hb ha (le_of_lt (not_le.mp hab))
  have h1 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr h1), abs_of_nonpos (sub_nonpos.mpr hab)]
  have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
    have := Real.add_one_le_exp (-(b - a)); linarith
  have h4 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h5 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  rw [h2]
  nlinarith

theorem integrable_test (ξ : VaguePointMeasure ℝ) (g : CompactlySupportedContinuousMap ℝ ℝ) :
    Integrable g ξ.measure := by
  have : IsFiniteMeasureOnCompacts ξ.measure := ⟨ξ.finite_on_compact⟩
  exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

/-- `|L_sine(g) - L_sine(f)| ≤ ε ∫ χ` when `|g - f| ≤ εχ` (all tests nonnegative, `C_c`). -/
theorem abs_sineLaplace_sub_le (f g χ : CompactlySupportedContinuousMap ℝ ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hχ : ∀ x, 0 ≤ χ x) (ε : ℝ)
    (hgf : ∀ x, |g x - f x| ≤ ε * χ x) :
    |sineLaplaceFunctional g - sineLaplaceFunctional f| ≤ ε * ∫ x, χ x := by
  obtain ⟨P, hP⟩ := exists_isSineLaw
  set μ : Measure (VaguePointMeasure ℝ) := (P : Measure (VaguePointMeasure ℝ))
  have hLap : ∀ h : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ h x) →
      ∫ ξ, Real.exp (-∫ x, h x ∂ξ.measure) ∂μ =
        fredholmSeries sineKernel volume (fun x => 1 - Real.exp (-h x)) := fun h hh =>
    (hP.2 h hh).trans (sineLaplaceFunctional_eq_fredholmSeries h)
  have hcoord := fun (h : CompactlySupportedContinuousMap ℝ ℝ) (hh : ∀ x, 0 ≤ h x) =>
    integral_coordinate_eq_of_fredholm P abs_det_sineKernel_le_one sineKernel_self volume hLap h hh
  have hexpint : ∀ h : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ h x) →
      Integrable (fun ξ : VaguePointMeasure ℝ => Real.exp (-∫ x, h x ∂ξ.measure)) μ := by
    intro h hh
    refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ξ => ?_)
    · exact (Real.continuous_exp.comp continuous_neg).comp_aestronglyMeasurable
        (hcoord h hh).1.aestronglyMeasurable
    · have h0 : 0 ≤ ∫ x, h x ∂ξ.measure := integral_nonneg hh
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by linarith)
  rw [← hP.2 g hg, ← hP.2 f hf, ← integral_sub (hexpint g hg) (hexpint f hf)]
  calc |∫ ξ, (Real.exp (-∫ x, g x ∂ξ.measure) - Real.exp (-∫ x, f x ∂ξ.measure)) ∂μ|
      ≤ ∫ ξ, |Real.exp (-∫ x, g x ∂ξ.measure) - Real.exp (-∫ x, f x ∂ξ.measure)| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ξ, ε * ∫ x, χ x ∂ξ.measure ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => abs_nonneg _)
          ((hcoord χ hχ).1.const_mul ε) (Eventually.of_forall fun ξ => ?_)
        refine (abs_exp_neg_sub_exp_neg_le (integral_nonneg hg) (integral_nonneg hf)).trans ?_
        show _ ≤ ε * ∫ x, χ x ∂ξ.measure
        rw [← integral_sub (integrable_test ξ g) (integrable_test ξ f), ← integral_const_mul]
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun x => abs_nonneg _) ((integrable_test ξ χ).const_mul ε)
          (Eventually.of_forall fun x => hgf x))
    _ = ε * ∫ x, χ x := by rw [integral_const_mul, (hcoord χ hχ).2]

/-!
## Dilation sandwich
-/

/-- The plateau bump `χ_K(y) = max 0 (min 1 (K + 1 - |y|))`: `0 ≤ χ ≤ 1`, `χ = 1` on
`[-K, K]`, supported in `[-(K+1), K+1]`. -/
def plateauBump (K : ℝ) : CompactlySupportedContinuousMap ℝ ℝ :=
  ⟨⟨fun y => max 0 (min 1 (K + 1 - |y|)), by fun_prop⟩, by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(K + 1)) (b := K + 1)) fun y hy => ?_
    have h : K + 1 < |y| := not_le.mp fun h => hy (abs_le.mp h)
    exact max_eq_left (min_le_of_right_le (by linarith))⟩

theorem plateauBump_apply (K y : ℝ) : plateauBump K y = max 0 (min 1 (K + 1 - |y|)) := rfl

theorem plateauBump_nonneg (K y : ℝ) : 0 ≤ plateauBump K y := le_max_left _ _

theorem plateauBump_eq_one {K y : ℝ} (hy : |y| ≤ K) : plateauBump K y = 1 := by
  rw [plateauBump_apply, min_eq_left (by linarith), max_eq_right zero_le_one]

/-- The upper test `f + εχ`. -/
def upperTest (f χ : CompactlySupportedContinuousMap ℝ ℝ) (ε : ℝ) :
    CompactlySupportedContinuousMap ℝ ℝ := f + ε • χ

/-- The lower test `min f (max (f - εχ) 0)` (equal to `max (f - εχ) 0` for `f, εχ ≥ 0`). -/
def lowerTest (f χ : CompactlySupportedContinuousMap ℝ ℝ) (ε : ℝ) :
    CompactlySupportedContinuousMap ℝ ℝ :=
  ⟨⟨fun y => min (f y) (max (f y - ε * χ y) 0), by fun_prop⟩, by
    refine f.hasCompactSupport.mono fun y hy => ?_
    intro hfy
    apply hy
    change min (f y) (max (f y - ε * χ y) 0) = 0
    rw [hfy]
    exact min_eq_left (le_max_right _ _)⟩

theorem lowerTest_apply (f χ : CompactlySupportedContinuousMap ℝ ℝ) (ε y : ℝ) :
    lowerTest f χ ε y = min (f y) (max (f y - ε * χ y) 0) := rfl

theorem upperTest_apply (f χ : CompactlySupportedContinuousMap ℝ ℝ) (ε y : ℝ) :
    upperTest f χ ε y = f y + ε * χ y := rfl

/-- Dilation sandwich. For a nonnegative `C_c` test `f` and `η > 0` there are `δ ∈ (0, 1/2]`
and nonnegative `C_c` tests `g⁻, g⁺` with `g⁻(y) ≤ f(ry) ≤ g⁺(y)` for all `y` and all
`|r - 1| ≤ δ`, and `|L_sine(g^±) - L_sine(f)| ≤ η`. -/
theorem exists_dilation_sandwich (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ gm gp : CompactlySupportedContinuousMap ℝ ℝ,
      (∀ x, 0 ≤ gm x) ∧ (∀ x, 0 ≤ gp x) ∧
      (∀ r : ℝ, |r - 1| ≤ δ → ∀ y, gm y ≤ f (r * y) ∧ f (r * y) ≤ gp y) ∧
      |sineLaplaceFunctional gm - sineLaplaceFunctional f| ≤ η ∧
      |sineLaplaceFunctional gp - sineLaplaceFunctional f| ≤ η := by
  -- support radius
  obtain ⟨K₀, hK₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set K : ℝ := max K₀ 1
  have hK1 : 1 ≤ K := le_max_right _ _
  have hfK : ∀ y, K < |y| → f y = 0 := by
    intro y hy
    by_contra h
    have hy' := hK₀ (subset_tsupport _ h)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hy'
    linarith [le_max_left K₀ 1]
  set χ := plateauBump (2 * K)
  have hχ0 : ∀ y, 0 ≤ χ y := plateauBump_nonneg _
  set I : ℝ := ∫ x, χ x
  have hI : 0 ≤ I := integral_nonneg hχ0
  set ε : ℝ := η / (I + 1)
  have hε : 0 < ε := div_pos hη (by linarith)
  have hεI : ε * I ≤ η := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  -- uniform continuity of `f`
  obtain ⟨δ₀, hδ₀, hδf⟩ := Metric.uniformContinuous_iff.mp
    (f.hasCompactSupport.uniformContinuous_of_continuous f.continuous) ε hε
  set δ : ℝ := min (1 / 2) (δ₀ / (4 * K))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hδ₀ (by linarith))
  refine ⟨δ, hδ, min_le_left _ _, lowerTest f χ ε, upperTest f χ ε, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; rw [lowerTest_apply]; exact le_min (hf x) (le_max_right _ _)
  · intro x; rw [upperTest_apply]; exact add_nonneg (hf x) (mul_nonneg hε.le (hχ0 x))
  · intro r hr y
    have hr' : |r - 1| ≤ 1 / 2 := hr.trans (min_le_left _ _)
    have hrpos : 1 / 2 ≤ r := by linarith [neg_abs_le (r - 1)]
    by_cases hy : |y| ≤ 2 * K
    · have hχ1 : χ y = 1 := plateauBump_eq_one hy
      have hclose : |f (r * y) - f y| ≤ ε := by
        have hd : dist (r * y) y < δ₀ := by
          rw [Real.dist_eq, show r * y - y = (r - 1) * y by ring, abs_mul]
          calc |r - 1| * |y| ≤ δ₀ / (4 * K) * (2 * K) :=
                mul_le_mul (hr.trans (min_le_right _ _)) hy (abs_nonneg _) (by positivity)
            _ = δ₀ / 2 := by field_simp; ring
            _ < δ₀ := by linarith
        have h' := hδf hd
        rw [Real.dist_eq] at h'
        exact h'.le
      rw [lowerTest_apply, upperTest_apply, hχ1, mul_one]
      constructor
      · refine min_le_of_right_le (max_le ?_ (hf _))
        linarith [(abs_le.mp hclose).1]
      · linarith [(abs_le.mp hclose).2]
    · have hy' : 2 * K < |y| := not_le.mp hy
      have hry : K < |r * y| := by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < r)]; nlinarith
      have hfy : f y = 0 := hfK y (by linarith)
      rw [hfK _ hry, lowerTest_apply, upperTest_apply, hfy]
      exact ⟨min_le_left _ _, by simpa using mul_nonneg hε.le (hχ0 y)⟩
  · refine (abs_sineLaplace_sub_le f (lowerTest f χ ε) χ hf
      (fun x => le_min (hf x) (le_max_right _ _)) hχ0 ε fun x => ?_).trans hεI
    rw [lowerTest_apply]
    have h1 : max (f x - ε * χ x) 0 ≤ f x := max_le (by nlinarith [hχ0 x]) (hf x)
    rw [min_eq_right h1, abs_le]
    constructor
    · have := le_max_left (f x - ε * χ x) 0; linarith
    · have := mul_nonneg hε.le (hχ0 x); linarith [max_le (by linarith : f x - ε * χ x ≤ f x) (hf x)]
  · refine (abs_sineLaplace_sub_le f (upperTest f χ ε) χ hf
      (fun x => add_nonneg (hf x) (mul_nonneg hε.le (hχ0 x))) hχ0 ε fun x => ?_).trans hεI
    rw [upperTest_apply, add_sub_cancel_left, abs_of_nonneg (mul_nonneg hε.le (hχ0 x))]

end BlockBand.Endpoints
