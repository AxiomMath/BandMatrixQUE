module

public import BlockBand.Diffusion.Kernel.SphereCK
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# The approximate identity for the sphere factor

Throughout `D₀ > 0`, Lebesgue measure on `ℝ`, and
`skSemigroupY D0 f h y = ∫ pY_h(y, y') f(y') dy'` for the kernel `skKernelY` (a copy of
`lbkKernelY`).

For `f` continuous on `[0,1]`, `P_h f → f` uniformly on `[0,1]` as `h → 0⁺`:
* `sk_semigroupY_approx`: `∀ ε > 0, ∃ δ > 0, ∀ h ∈ (0, δ), ∀ y ∈ [0,1], |P_h f(y) - f(y)| < ε`;
* `sk_semigroupY_tendstoUniformlyOn`: the same as `TendstoUniformlyOn … (𝓝[>] 0) (Icc 0 1)`.

Proof. (i) For a polynomial `q = Σ_{m ≤ N} β_m P̃_m`, the eigenfunction identity
gives `P_h q = Σ β_m e^{-(D₀/2)m(m+1)h} P̃_m`, so `|P_h q - q| ≤ B_q h` on `[0,1]`
(`sk_poly_approx`). (ii) Nonnegativity (`skp_series_nonneg`) and normalisation give
`|P_h g| ≤ ε` on `[0,1]` when `|g| ≤ ε` there (`sk_abs_integral_series_mul_le`).
(iii) Weierstrass approximation of `f` by a polynomial.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Polynomial

/-- `P_t f (y)` as an interval integral of the series, for `t > 0`, `y ∈ [0,1]`, any `f`. -/
theorem sk_semigroupY_eq_intervalIntegral {D0 t y : ℝ} (ht : 0 < t) (hy : y ∈ Icc (0 : ℝ) 1)
    (f : ℝ → ℝ) :
    skSemigroupY D0 f t y = ∫ w in (0 : ℝ)..1, skSphereSeries D0 t y w * f w := by
  unfold skSemigroupY
  rw [sk_kernelY_eq_indicator ht hy]
  have e1 : (fun y' => (Icc (0 : ℝ) 1).indicator (skSphereSeries D0 t y) y' * f y') =
      (Icc (0 : ℝ) 1).indicator fun y' => skSphereSeries D0 t y y' * f y' := by
    funext y'
    by_cases h : y' ∈ Icc (0 : ℝ) 1 <;> simp [h]
  rw [e1, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]

/-- **Contraction**: `|∫₀¹ pY_t(y,w) g(w) dw| ≤ ε` when `|g| ≤ ε` on `[0,1]`. -/
theorem sk_abs_integral_series_mul_le {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) {ε : ℝ}
    (hε : ∀ w ∈ Icc (0 : ℝ) 1, |g w| ≤ ε) :
    |∫ w in (0 : ℝ)..1, skSphereSeries D0 t y w * g w| ≤ ε := by
  have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun w => skSphereSeries D0 t y w * g w) zero_le_one
  have hint1 : IntervalIntegrable (fun w => |skSphereSeries D0 t y w * g w|) volume 0 1 :=
    (skp_series_intervalIntegrable_mul hD0 ht hy hg).abs
  have hint2 : IntervalIntegrable (fun w => skSphereSeries D0 t y w * ε) volume 0 1 :=
    skp_series_intervalIntegrable_mul hD0 ht hy continuousOn_const
  have h2 : (∫ w in (0 : ℝ)..1, |skSphereSeries D0 t y w * g w|) ≤
      ∫ w in (0 : ℝ)..1, skSphereSeries D0 t y w * ε :=
    intervalIntegral.integral_mono_on zero_le_one hint1 hint2 fun w hw => by
      rw [abs_mul, abs_of_nonneg (skp_series_nonneg hD0 ht hy hw)]
      exact mul_le_mul_of_nonneg_left (hε w hw) (skp_series_nonneg hD0 ht hy hw)
  have h3 : (∫ w in (0 : ℝ)..1, skSphereSeries D0 t y w * ε) = ε := by
    rw [intervalIntegral.integral_mul_const, skp_integral_series_one hD0 ht hy, one_mul]
  linarith

/-- **Polynomials**: `|∫₀¹ pY_t(y,w) q(w) dw - q(y)| ≤ B_q t` on `[0,1]`. -/
theorem sk_poly_approx {D0 : ℝ} (hD0 : 0 < D0) (q : ℝ[X]) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 < t → ∀ y ∈ Icc (0 : ℝ) 1,
      |(∫ w in (0 : ℝ)..1, skSphereSeries D0 t y w * q.eval w) - q.eval y| ≤ B * t := by
  obtain ⟨N, hN⟩ : ∃ N, q.natDegree = N := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ := skp_leg_span N q hN.le
  refine ⟨∑ m ∈ Finset.range (N + 1),
      |β m| * (D0 / 2 * ((m : ℝ) * (m + 1))) * 8 ^ m,
    Finset.sum_nonneg fun m _ => by positivity, fun t ht y hy => ?_⟩
  rw [hβ, skp_integral_series_legSum hD0 ht hy]
  have hq : (∑ m ∈ Finset.range (N + 1), C (β m) * skLeg m).eval y =
      ∑ m ∈ Finset.range (N + 1), β m * (skLeg m).eval y := by
    simp [eval_finsetSum]
  rw [hq, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  have hl : 0 ≤ D0 / 2 * ((m : ℝ) * (m + 1)) := by positivity
  have he1 : |Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * t)) - 1| ≤
      D0 / 2 * ((m : ℝ) * (m + 1)) * t := by
    have hle : Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * t)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
    linarith [Real.add_one_le_exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * t))]
  have hP := sk_leg_bound m hy
  calc |β m * Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * t)) * (skLeg m).eval y -
        β m * (skLeg m).eval y|
      = |β m| * |Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * t)) - 1| *
          |(skLeg m).eval y| := by
        rw [← abs_mul, ← abs_mul]; congr 1; ring
    _ ≤ |β m| * (D0 / 2 * ((m : ℝ) * (m + 1)) * t) * 8 ^ m := by gcongr
    _ = |β m| * (D0 / 2 * ((m : ℝ) * (m + 1))) * 8 ^ m * t := by ring

/-- **Approximate identity** (KY2): `P_h f → f` uniformly on `[0,1]` as `h → 0⁺`, for `f`
continuous on `[0,1]`. -/
theorem sk_semigroupY_approx {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → ∀ y ∈ Icc (0 : ℝ) 1, |skSemigroupY D0 f h y - f y| < ε := by
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf (ε / 3) (by positivity)
  obtain ⟨B, hB, hBq⟩ := sk_poly_approx hD0 q
  refine ⟨ε / (3 * (B + 1)), by positivity, fun h hh hhδ y hy => ?_⟩
  rw [sk_semigroupY_eq_intervalIntegral hh hy]
  have hfq : ContinuousOn (fun w => f w - q.eval w) (Icc 0 1) :=
    hf.sub q.continuous.continuousOn
  have hsplit : (∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * f w) =
      (∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * (f w - q.eval w)) +
        ∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * q.eval w := by
    rw [← intervalIntegral.integral_add (skp_series_intervalIntegrable_mul hD0 hh hy hfq)
      (skp_series_intervalIntegrable_mul hD0 hh hy q.continuous.continuousOn)]
    congr 1; funext w; ring
  have h1 : |∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * (f w - q.eval w)| ≤ ε / 3 :=
    sk_abs_integral_series_mul_le hD0 hh hy hfq fun w hw => by
      rw [abs_sub_comm]; exact (hq w hw).le
  have h2 := hBq h hh y hy
  have h3 : B * h < ε / 3 := by
    have hB1 : 0 < B + 1 := by linarith
    calc B * h ≤ (B + 1) * h := by nlinarith
      _ < (B + 1) * (ε / (3 * (B + 1))) := mul_lt_mul_of_pos_left hhδ hB1
      _ = ε / 3 := by field_simp
  have h4 := hq y hy
  rw [hsplit]
  calc |(∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * (f w - q.eval w)) +
        (∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * q.eval w) - f y|
      = |(∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * (f w - q.eval w)) +
          ((∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * q.eval w) - q.eval y) +
          (q.eval y - f y)| := by ring_nf
    _ ≤ |∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * (f w - q.eval w)| +
          |(∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * q.eval w) - q.eval y| +
          |q.eval y - f y| := abs_add_three _ _ _
    _ < ε := by linarith

/-- **Approximate identity, uniform-convergence form.** -/
theorem sk_semigroupY_tendstoUniformlyOn {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) :
    TendstoUniformlyOn (fun h y => skSemigroupY D0 f h y) f (𝓝[>] 0) (Icc 0 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := sk_semigroupY_approx hD0 hf hε
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hh y hy
  rw [Real.dist_eq, abs_sub_comm]
  exact H h hh.1 hh.2 y hy

end BlockBand.Diffusion
