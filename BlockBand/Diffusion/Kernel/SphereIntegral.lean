module

public import BlockBand.Diffusion.Kernel.SphereCone
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds


/-!
# Integrals of the spherical kernel against polynomials

We compute the integrals of the spherical kernel `k_t` against Legendre polynomials and prove its
positivity against the Bernstein cone, Chapman–Kolmogorov and symmetry.
* `skp_integral_series_leg`: `∫₀¹ k_t(y,w) P̃_n(w) dw = e^{-(D₀/2)n(n+1)t} P̃_n(y)`;
* `skp_integral_series_one`: `∫₀¹ k_t(y,w) dw = 1`;
* `skp_integral_series_cone_nonneg`: `∫₀¹ k_t(y,w) q(w) dw ≥ 0` for every `q` in the Bernstein
  cone `SkpCone N` (the semigroup `e^{t(D₀/2)L}` on polynomials of degree `≤ N` is the limit of
  the cone-preserving Euler steps `T_{(D₀/2)t/i}ⁱ`);
* `skp_chapman`: Chapman–Kolmogorov `k_{s+u}(y,y') = ∫₀¹ k_s(y,w) k_u(w,y') dw`;
* `skp_series_symm`: symmetry `k_t(y,y') = k_t(y',y)`;
* `skp_integral_pos`, `skp_eq_zero_of_integral_eq_zero`, `skp_exists_Icc_sub`: elementary
  facts on continuous functions on `[0,1]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Polynomial
open scoped Interval

theorem skp_uIoc_sub : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
  rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self

/-- Termwise integration on `[0,1]` under a summable uniform majorant. -/
theorem skp_hasSum_integral {F : ℕ → ℝ → ℝ} {b : ℕ → ℝ} (hb : Summable b)
    (hF : ∀ n, ContinuousOn (F n) (Icc 0 1)) (hle : ∀ n, ∀ w ∈ Icc (0 : ℝ) 1, ‖F n w‖ ≤ b n) :
    HasSum (fun n => ∫ w in (0 : ℝ)..1, F n w) (∫ w in (0 : ℝ)..1, ∑' n, F n w) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => b n)
    (fun n => ((hF n).mono skp_uIoc_sub).aestronglyMeasurable measurableSet_uIoc) ?_ ?_ ?_ ?_
  · exact fun n => ae_of_all _ fun w hw => hle n w (skp_uIoc_sub hw)
  · exact ae_of_all _ fun w _ => hb
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun w hw =>
      (Summable.of_norm_bounded hb fun n => hle n w (skp_uIoc_sub hw)).hasSum

theorem skp_bound_nonneg (D0 t : ℝ) (n : ℕ) : 0 ≤ skYBound D0 t n := by
  unfold skYBound; positivity

theorem skp_series_norm_le {D0 t y w : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) :
    ‖skSphereSeries D0 t y w‖ ≤ ∑' n, skYBound D0 t n :=
  tsum_of_norm_bounded (sk_summable_bound hD0 ht).hasSum (sk_term_le hy hw)

theorem skp_term_continuousOn (D0 t y' : ℝ) (n : ℕ) :
    Continuous fun w : ℝ => skYTerm D0 t w y' n :=
  (sk_term_continuous D0 n).comp (by fun_prop : Continuous fun w : ℝ => (t, w, y'))

theorem skp_term_continuous_right (D0 t y : ℝ) (n : ℕ) :
    Continuous fun w : ℝ => skYTerm D0 t y w n :=
  (sk_term_continuous D0 n).comp (by fun_prop : Continuous fun w : ℝ => (t, y, w))

theorem skp_integral_term_leg (D0 t y : ℝ) (m n : ℕ) :
    ∫ w in (0 : ℝ)..1, skYTerm D0 t y w m * (skLeg n).eval w =
      (2 * m + 1) * Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * t)) * (skLeg m).eval y *
        ∫ w in (0 : ℝ)..1, (skLeg m).eval w * (skLeg n).eval w := by
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext w
  simp only [skYTerm]; ring

/-- **Eigenfunction integrals**: `∫₀¹ k_t(y,w) P̃_n(w) dw = e^{-(D₀/2)n(n+1)t} P̃_n(y)`. -/
theorem skp_integral_series_leg {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    ∫ w in (0 : ℝ)..1, skSphereSeries D0 t y w * (skLeg n).eval w =
      Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * (skLeg n).eval y := by
  have hs := skp_hasSum_integral (F := fun m w => skYTerm D0 t y w m * (skLeg n).eval w)
    (b := fun m => skYBound D0 t m * 8 ^ n) ((sk_summable_bound hD0 ht).mul_right _)
    (fun m => ((skp_term_continuous_right D0 t y m).mul (skLeg n).continuous).continuousOn)
    (fun m w hw => by
      rw [norm_mul]
      exact mul_le_mul (sk_term_le hy hw m) (by rw [Real.norm_eq_abs]; exact sk_leg_bound n hw)
        (norm_nonneg _) (skp_bound_nonneg D0 t m))
  have e : (fun w => ∑' m, skYTerm D0 t y w m * (skLeg n).eval w) =
      fun w => skSphereSeries D0 t y w * (skLeg n).eval w := by
    funext w; rw [skSphereSeries, tsum_mul_right]
  rw [e] at hs
  rw [← hs.tsum_eq, tsum_eq_single n]
  · rw [skp_integral_term_leg, skp_integral_leg_leg]
    simp only [↓reduceIte]
    have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · intro m hm
    rw [skp_integral_term_leg, skp_integral_leg_leg]
    simp [hm]

/-- **Normalisation** on `[0,1]`: `∫₀¹ k_t(y,w) dw = 1`. -/
theorem skp_integral_series_one {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) : ∫ w in (0 : ℝ)..1, skSphereSeries D0 t y w = 1 := by
  have := skp_integral_series_leg hD0 ht hy 0
  simpa [sk_leg_zero] using this

theorem skp_series_intervalIntegrable_mul {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) :
    IntervalIntegrable (fun w => skSphereSeries D0 t y w * g w) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  exact (sk_sphereSeries_continuousOn hD0 ht hy).mul hg

theorem skp_integral_series_legSum {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) (N : ℕ) (β : ℕ → ℝ) :
    ∫ w in (0 : ℝ)..1, skSphereSeries D0 t y w *
        (∑ m ∈ Finset.range (N + 1), C (β m) * skLeg m).eval w =
      ∑ m ∈ Finset.range (N + 1),
        β m * Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * t)) * (skLeg m).eval y := by
  simp only [eval_finsetSum, eval_mul, eval_C, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    have : (fun w => skSphereSeries D0 t y w * (β m * (skLeg m).eval w)) =
        fun w => β m * (skSphereSeries D0 t y w * (skLeg m).eval w) := by
      funext w; ring
    rw [this, intervalIntegral.integral_const_mul, skp_integral_series_leg hD0 ht hy]
    ring
  · intro m _
    exact skp_series_intervalIntegrable_mul hD0 ht hy
      ((continuous_const.mul (skLeg m).continuous).continuousOn)

/-- **Positivity against the Bernstein cone**: `∫₀¹ k_t(y,w) q(w) dw ≥ 0` for `q ∈ SkpCone N`. -/
theorem skp_integral_series_cone_nonneg {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) {N : ℕ} {q : ℝ[X]} (hq : SkpCone N q) :
    0 ≤ ∫ w in (0 : ℝ)..1, skSphereSeries D0 t y w * q.eval w := by
  obtain ⟨β, hβ⟩ := skp_leg_span N q (skp_cone_natDegree_le hq)
  have hlim : Tendsto (fun i : ℕ => ((skpT (D0 / 2 * t / i))^[i] q).eval y) atTop
      (𝓝 (∑ m ∈ Finset.range (N + 1),
        β m * Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * t)) * (skLeg m).eval y)) := by
    have hform : ∀ i : ℕ, ((skpT (D0 / 2 * t / i))^[i] q).eval y =
        ∑ m ∈ Finset.range (N + 1),
          β m * (1 + -(D0 / 2 * ((m : ℝ) * (m + 1)) * t) / i) ^ i * (skLeg m).eval y := by
      intro i
      rw [hβ, skp_T_iterate_leg]
      simp only [eval_finsetSum, eval_mul, eval_C]
      refine Finset.sum_congr rfl fun m _ => ?_
      have e : (1 - D0 / 2 * t / (i : ℝ) * ((m : ℝ) * (m + 1))) =
          1 + -(D0 / 2 * ((m : ℝ) * (m + 1)) * t) / i := by ring
      rw [e]
    simp_rw [hform]
    exact tendsto_finsetSum _ fun m _ =>
      ((Real.tendsto_one_add_div_pow_exp _).const_mul (β m)).mul_const _
  rw [hβ, skp_integral_series_legSum hD0 ht hy]
  refine ge_of_tendsto hlim ?_
  rw [eventually_atTop]
  refine ⟨⌈D0 / 2 * t * (2 * ((N : ℝ) + 1) ^ 2)⌉₊ + 1, fun i hi => ?_⟩
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have ha : 0 < D0 / 2 * t := by positivity
  refine skp_cone_eval_nonneg (N := N) ?_ hy
  refine skp_cone_T_iterate hq (div_nonneg ha.le hi0.le) ?_ i
  rw [div_mul_eq_mul_div, div_le_one hi0]
  have h1 := Nat.le_ceil (D0 / 2 * t * (2 * ((N : ℝ) + 1) ^ 2))
  have h2 : (⌈D0 / 2 * t * (2 * ((N : ℝ) + 1) ^ 2)⌉₊ : ℝ) + 1 ≤ i := by exact_mod_cast hi
  linarith

/-!
### Elementary facts on `[0,1]`
-/

/-- A continuous function with `f w₀ ∈ U` (`U` open) stays in `U` on a nondegenerate
subinterval of `[0,1]` near `w₀`. -/
theorem skp_exists_Icc_sub {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) {w0 : ℝ}
    (hw0 : w0 ∈ Icc (0 : ℝ) 1) {U : Set ℝ} (hU : IsOpen U) (hfU : f w0 ∈ U) :
    ∃ c d : ℝ, 0 ≤ c ∧ c < d ∧ d ≤ 1 ∧ ∀ w ∈ Icc c d, f w ∈ U := by
  have hmem : f ⁻¹' U ∈ 𝓝[Icc 0 1] w0 := hf w0 hw0 (hU.mem_nhds hfU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hmem
  have hin : ∀ w ∈ Icc (0 : ℝ) 1, |w - w0| < ε → f w ∈ U := fun w hw hd =>
    hball ⟨by rw [Metric.mem_ball, Real.dist_eq]; exact hd, hw⟩
  rcases lt_or_eq_of_le hw0.2 with h1 | h1
  · refine ⟨w0, min 1 (w0 + ε / 2), hw0.1, lt_min h1 (by linarith), min_le_left _ _,
      fun w hw => hin w ⟨hw0.1.trans hw.1, hw.2.trans (min_le_left _ _)⟩ ?_⟩
    have := hw.2.trans (min_le_right _ _)
    rw [abs_lt]; constructor <;> linarith [hw.1]
  · refine ⟨max 0 (1 - ε / 2), 1, le_max_left _ _, max_lt (by norm_num) (by linarith), le_rfl,
      fun w hw => hin w ⟨(le_max_left _ _).trans hw.1, hw.2⟩ ?_⟩
    have := (le_max_right _ _).trans hw.1
    rw [abs_lt]; constructor <;> linarith [hw.2]

/-- A continuous nonnegative function on `[0,1]` that is positive somewhere has positive
integral. -/
theorem skp_integral_pos {h : ℝ → ℝ} (hc : ContinuousOn h (Icc 0 1))
    (hnn : ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ h w) {w0 : ℝ} (hw0 : w0 ∈ Icc (0 : ℝ) 1)
    (hpos : 0 < h w0) : 0 < ∫ w in (0 : ℝ)..1, h w := by
  obtain ⟨c, d, hc0, hcd, hd1, hcdpos⟩ := skp_exists_Icc_sub hc hw0 isOpen_Ioi hpos
  have hae : 0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) 1)] h :=
    ae_restrict_of_forall_mem measurableSet_uIoc fun w hw => hnn w (skp_uIoc_sub hw)
  have hfi : IntervalIntegrable h volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [uIcc_of_le zero_le_one]
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hae hfi]
  refine ⟨zero_lt_one, ?_⟩
  have hsub : Ioo c d ⊆ Function.support h ∩ Ioc 0 1 := fun w hw =>
    ⟨(mem_Ioi.1 (hcdpos w (Ioo_subset_Icc_self hw))).ne',
      ⟨hc0.trans_lt hw.1, hw.2.le.trans hd1⟩⟩
  exact ((Measure.measure_Ioo_pos _).2 hcd).trans_le (measure_mono hsub)

theorem skp_eq_zero_of_integral_eq_zero {h : ℝ → ℝ} (hc : ContinuousOn h (Icc 0 1))
    (hnn : ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ h w) (h0 : ∫ w in (0 : ℝ)..1, h w = 0) :
    ∀ w ∈ Icc (0 : ℝ) 1, h w = 0 := by
  intro w hw
  by_contra hne
  have := skp_integral_pos hc hnn hw (lt_of_le_of_ne (hnn w hw) (Ne.symm hne))
  linarith

/-!
### Symmetry and Chapman–Kolmogorov
-/

theorem skp_series_symm (D0 t y y' : ℝ) : skSphereSeries D0 t y y' = skSphereSeries D0 t y' y := by
  unfold skSphereSeries
  congr 1; funext n
  simp only [skYTerm]; ring

/-- **Chapman–Kolmogorov** for the spherical kernel on `[0,1]`. -/
theorem skp_chapman {D0 s u y y' : ℝ} (hD0 : 0 < D0) (hs : 0 < s) (hu : 0 < u)
    (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1) :
    skSphereSeries D0 (s + u) y y' =
      ∫ w in (0 : ℝ)..1, skSphereSeries D0 s y w * skSphereSeries D0 u w y' := by
  have hB := skp_hasSum_integral
    (F := fun n w => skSphereSeries D0 s y w * skYTerm D0 u w y' n)
    (b := fun n => (∑' m, skYBound D0 s m) * skYBound D0 u n)
    ((sk_summable_bound hD0 hu).mul_left _)
    (fun n => (sk_sphereSeries_continuousOn hD0 hs hy).mul
      (skp_term_continuousOn D0 u y' n).continuousOn)
    (fun n w hw => by
      rw [norm_mul]
      exact mul_le_mul (skp_series_norm_le hD0 hs hy hw) (sk_term_le hw hy' n)
        (norm_nonneg _) (tsum_nonneg (skp_bound_nonneg D0 s)))
  have e : (fun w => ∑' n, skSphereSeries D0 s y w * skYTerm D0 u w y' n) =
      fun w => skSphereSeries D0 s y w * skSphereSeries D0 u w y' := by
    funext w; exact tsum_mul_left
  rw [e] at hB
  rw [← hB.tsum_eq, skSphereSeries]
  refine tsum_congr fun n => ?_
  have h1 : (∫ w in (0 : ℝ)..1, skSphereSeries D0 s y w * skYTerm D0 u w y' n) =
      (2 * n + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * u)) * (skLeg n).eval y' *
        ∫ w in (0 : ℝ)..1, skSphereSeries D0 s y w * (skLeg n).eval w := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext w
    simp only [skYTerm]; ring
  rw [h1, skp_integral_series_leg hD0 hs hy, skYTerm]
  have h2 : Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * (s + u))) =
      Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * s)) *
        Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * u)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2]; ring

end BlockBand.Diffusion
