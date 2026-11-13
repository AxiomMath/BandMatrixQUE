module

public import BlockBand.Diffusion.Kernel.SphereSmooth
public import BlockBand.Diffusion.Kernel.SphereIntegral

/-!
# Backward equation for the sphere factor `pY` and for `P_t f`

We prove that the sphere factor `pY` and its semigroup `P_t f` are smooth and solve the backward
equation `∂_t u = 𝒟_Y u`, `𝒟_Y = (D₀/2)[y(1-y)∂²_y + (1-2y)∂_y]`.

**Kernel.** `skSphereSeries D0 t y y' = skSer D0 (skLegFam (skKerCoef y')) t y`
(`sk_sphereSeries_eq_ser`), so for every `y' ∈ ℝ`:
* `sk_sphereSeries_contDiffOn`: `(t, y) ↦ pY_t(y, y')` (the series) is `C^∞` on `(0,∞) × ℝ`;
* `sk_sphereSeries_pde`: it solves `∂_t p = 𝒟_Y p` at every `(t, y) ∈ (0,∞) × ℝ`;
* `sk_kernelY_contDiffOn`, `sk_kernelY_pde`: the kernel `skKernelY` (which is `0` for
  `y ∉ [0,1]`) is `C^∞` and solves the equation on the open set `(0,∞) × (0,1)`, for
  `y' ∈ [0,1]`; `sk_kernelY_contDiffOn_Icc`: it is `C^∞` on `(0,∞) × [0,1]` in Mathlib's
  within-set sense (it agrees there with the smooth series).

**Semigroup.** For `f` a.e.-strongly measurable on `[0,1]` with `|f| ≤ M` there,
`skSemigroupY D0 f t y = ∫ pY_t(y, y') f(y') dy'` equals, for `t > 0` and `y ∈ [0,1]`, the
Legendre series `skSer D0 (skLegFam (skCoef f)) t y` with
`skCoef f n = (2n+1) ∫₀¹ P̃_n f` (`sk_semigroupY_eq_ser`); hence
* `sk_semigroupY_continuousOn`: `u` is continuous on `(0,∞) × [0,1]`;
* `sk_semigroupY_contDiffOn`, `sk_semigroupY_pde`: `u` is `C^∞` on `(0,∞) × (0,1)` and solves
  `∂_t u = 𝒟_Y u` there; `sk_semigroupY_contDiffOn_Icc`: `u` is `C^∞` on `(0,∞) × [0,1]`
  (within-set sense);
* `sk_semigroupY_ext_contDiffOn`, `sk_semigroupY_ext_pde`: the explicit extension
  `skSer D0 (skLegFam (skCoef f))` is `C^∞` on `(0,∞) × ℝ`, solves the equation everywhere there
  and agrees with `u` on `(0,∞) × [0,1]` — so `u` is `C^∞` up to the boundary `y ∈ {0, 1}` in
  the sense of one-sided restrictions of a smooth function.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Polynomial
open scoped ContDiff

/-!
### Generic: the backward equation in `deriv` form
-/

theorem sk_legFam_pde_deriv {D0 : ℝ} (hD0 : 0 < D0) {c : ℕ → ℝ} {A K : ℝ} (hA : 0 ≤ A)
    (hK : 0 ≤ K) (hc : ∀ n, |c n| ≤ A * K ^ n) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    deriv (fun s => skSer D0 (skLegFam c) s y) t =
      D0 / 2 * (y * (1 - y) * deriv (deriv fun z => skSer D0 (skLegFam c) t z) y +
        (1 - 2 * y) * deriv (fun z => skSer D0 (skLegFam c) t z) y) := by
  have hG := sk_growth_legFam hA hK hc
  rw [(sk_ser_hasDerivAt_t hD0 hG ht y).deriv, sk_ser_deriv_y hD0 hG ht,
    sk_ser_deriv_y hD0 (sk_growth_dy hG) ht]
  exact sk_legFam_pde hD0 hA hK hc ht y

/-!
### The kernel
-/

/-- The Legendre coefficients `(2n+1) P̃_n(y')` of `y ↦ pY_t(y, y')`. -/
def skKerCoef (y' : ℝ) (n : ℕ) : ℝ := (2 * n + 1) * (skLeg n).eval y'

theorem sk_kerCoef_le (y' : ℝ) (n : ℕ) :
    |skKerCoef y' n| ≤ 2 * (32 * (|y'| + 1)) ^ n := by
  have hR : (1 : ℝ) ≤ |y'| + 1 := by linarith [abs_nonneg y']
  have h1 := sk_leg_eval_le (y := y') hR (by linarith) n
  have h2 : |(2 * (n : ℝ) + 1)| ≤ 2 * 2 ^ n := by
    rw [abs_of_nonneg (by positivity)]
    linarith [sk_succ_le_two_pow n]
  rw [skKerCoef, abs_mul]
  calc |(2 * (n : ℝ) + 1)| * |(skLeg n).eval y'| ≤ (2 * 2 ^ n) * (16 * (|y'| + 1)) ^ n :=
        mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
    _ = 2 * (32 * (|y'| + 1)) ^ n := by
        rw [mul_pow, mul_pow, show (32 : ℝ) = 2 * 16 by norm_num, mul_pow]; ring

theorem sk_growth_kerCoef (y' : ℝ) : SkGrowth (skLegFam (skKerCoef y')) :=
  sk_growth_legFam (by norm_num) (by positivity) (sk_kerCoef_le y')

theorem sk_sphereSeries_eq_ser (D0 t y y' : ℝ) :
    skSphereSeries D0 t y y' = skSer D0 (skLegFam (skKerCoef y')) t y := by
  unfold skSphereSeries skSer
  refine tsum_congr fun n => ?_
  simp only [skYTerm, skLegFam, skKerCoef, eval_mul, eval_C]
  ring

/-- **Joint smoothness of the spherical kernel** in `(t, y)` on `(0, ∞) × ℝ`, any `y'`. -/
theorem sk_sphereSeries_contDiffOn {D0 : ℝ} (hD0 : 0 < D0) (y' : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => skSphereSeries D0 p.1 p.2 y') (Ioi 0 ×ˢ univ) := by
  simp only [sk_sphereSeries_eq_ser]
  exact sk_ser_contDiffOn hD0 (sk_growth_kerCoef y')

/-- **The backward equation for the spherical kernel**:
`∂_t pY = (D₀/2)[y(1-y)∂²_y pY + (1-2y)∂_y pY]` at every `t > 0`, `y, y' ∈ ℝ`. -/
theorem sk_sphereSeries_pde {D0 : ℝ} (hD0 : 0 < D0) {t : ℝ} (ht : 0 < t) (y y' : ℝ) :
    deriv (fun s => skSphereSeries D0 s y y') t =
      D0 / 2 * (y * (1 - y) * deriv (deriv fun z => skSphereSeries D0 t z y') y +
        (1 - 2 * y) * deriv (fun z => skSphereSeries D0 t z y') y) := by
  simp only [sk_sphereSeries_eq_ser]
  exact sk_legFam_pde_deriv hD0 (by norm_num) (by positivity) (sk_kerCoef_le y') ht y

/-- Differentiability of the spherical kernel in `t` and (twice) in `y`, with the termwise
derivatives. -/
theorem sk_sphereSeries_hasDerivAt {D0 : ℝ} (hD0 : 0 < D0) {t : ℝ} (ht : 0 < t) (y y' : ℝ) :
    HasDerivAt (fun s => skSphereSeries D0 s y y')
        (skSer D0 (skDt D0 (skLegFam (skKerCoef y'))) t y) t ∧
      HasDerivAt (fun z => skSphereSeries D0 t z y')
        (skSer D0 (skDy (skLegFam (skKerCoef y'))) t y) y ∧
      HasDerivAt (deriv fun z => skSphereSeries D0 t z y')
        (skSer D0 (skDy (skDy (skLegFam (skKerCoef y')))) t y) y := by
  have hG := sk_growth_kerCoef y'
  simp only [sk_sphereSeries_eq_ser]
  refine ⟨sk_ser_hasDerivAt_t hD0 hG ht y, sk_ser_hasDerivAt_y hD0 hG ht y, ?_⟩
  rw [sk_ser_deriv_y hD0 hG ht]
  exact sk_ser_hasDerivAt_y hD0 (sk_growth_dy hG) ht y

theorem sk_kernelY_eqOn {D0 y' : ℝ} (hy' : y' ∈ Icc (0 : ℝ) 1) :
    EqOn (fun p : ℝ × ℝ => skKernelY D0 p.1 p.2 y')
      (fun p : ℝ × ℝ => skSphereSeries D0 p.1 p.2 y') (Ioi 0 ×ˢ Icc 0 1) :=
  fun _ hp => sk_kernelY_eq hp.1 hp.2 hy'

/-- **Joint smoothness of the kernel** `skKernelY` on the open set `(0,∞) × (0,1)`. -/
theorem sk_kernelY_contDiffOn {D0 y' : ℝ} (hD0 : 0 < D0) (hy' : y' ∈ Icc (0 : ℝ) 1) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => skKernelY D0 p.1 p.2 y') (Ioi 0 ×ˢ Ioo 0 1) :=
  ((sk_sphereSeries_contDiffOn hD0 y').mono (prod_mono subset_rfl (subset_univ _))).congr
    fun _ hp => (sk_kernelY_eqOn hy') ⟨hp.1, Ioo_subset_Icc_self hp.2⟩

/-- `skKernelY` is `C^∞` on `(0,∞) × [0,1]` (within-derivatives up to `y ∈ {0, 1}`), as the
restriction of the smooth series. -/
theorem sk_kernelY_contDiffOn_Icc {D0 y' : ℝ} (hD0 : 0 < D0) (hy' : y' ∈ Icc (0 : ℝ) 1) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => skKernelY D0 p.1 p.2 y') (Ioi 0 ×ˢ Icc 0 1) :=
  ((sk_sphereSeries_contDiffOn hD0 y').mono (prod_mono subset_rfl (subset_univ _))).congr
    (sk_kernelY_eqOn hy')

theorem sk_kernelY_eventuallyEq_y {D0 t y y' : ℝ} (ht : 0 < t) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hy' : y' ∈ Icc (0 : ℝ) 1) :
    (fun z => skKernelY D0 t z y') =ᶠ[𝓝 y] fun z => skSphereSeries D0 t z y' :=
  Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hy) fun _ hz =>
    sk_kernelY_eq ht (Ioo_subset_Icc_self hz) hy'

/-- **The backward equation for `skKernelY`** on `(0,∞) × (0,1)`, `y' ∈ [0,1]`. -/
theorem sk_kernelY_pde {D0 : ℝ} (hD0 : 0 < D0) {t y y' : ℝ} (ht : 0 < t)
    (hy : y ∈ Ioo (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1) :
    deriv (fun s => skKernelY D0 s y y') t =
      D0 / 2 * (y * (1 - y) * deriv (deriv fun z => skKernelY D0 t z y') y +
        (1 - 2 * y) * deriv (fun z => skKernelY D0 t z y') y) := by
  have ht' : (fun s => skKernelY D0 s y y') =ᶠ[𝓝 t] fun s => skSphereSeries D0 s y y' :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht) fun s hs =>
      sk_kernelY_eq hs (Ioo_subset_Icc_self hy) hy'
  have hy1 := sk_kernelY_eventuallyEq_y (D0 := D0) ht hy hy'
  have hy2 : deriv (fun z => skKernelY D0 t z y') =ᶠ[𝓝 y]
      deriv fun z => skSphereSeries D0 t z y' :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hy) fun z hz =>
      (sk_kernelY_eventuallyEq_y ht hz hy').deriv_eq
  rw [ht'.deriv_eq, hy1.deriv_eq, hy2.deriv_eq]
  exact sk_sphereSeries_pde hD0 ht y y'

/-!
### The semigroup `u(t, y) = ∫ pY_t(y, y') f(y') dy'`
-/

/-- `P_t f (y) = ∫ pY_t(y, y') f(y') dy'` for the kernel `skKernelY`. -/
def skSemigroupY (D0 : ℝ) (f : ℝ → ℝ) (t y : ℝ) : ℝ := ∫ y', skKernelY D0 t y y' * f y'

/-- The Legendre coefficients `(2n+1) ∫₀¹ P̃_n f` of `P_t f`. -/
def skCoef (f : ℝ → ℝ) (n : ℕ) : ℝ := (2 * n + 1) * ∫ w in Icc (0 : ℝ) 1, (skLeg n).eval w * f w

theorem sk_integrableOn_of_bound {f : ℝ → ℝ} {M : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) 1)))
    (hfb : ∀ w ∈ Icc (0 : ℝ) 1, |f w| ≤ M) : IntegrableOn f (Icc 0 1) :=
  ⟨hfm, HasFiniteIntegral.restrict_of_bounded (C := M) measure_Icc_lt_top
    (ae_restrict_of_forall_mem measurableSet_Icc fun w hw => by
      rw [Real.norm_eq_abs]; exact hfb w hw)⟩

theorem sk_coef_le {f : ℝ → ℝ} {M : ℝ} (hfb : ∀ w ∈ Icc (0 : ℝ) 1, |f w| ≤ M) (n : ℕ) :
    |skCoef f n| ≤ 2 * M * 16 ^ n := by
  have hI : ‖∫ w in Icc (0 : ℝ) 1, (skLeg n).eval w * f w‖ ≤ 8 ^ n * M := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : ℝ) 1)
      (f := fun w => (skLeg n).eval w * f w) (C := 8 ^ n * M) (by simp) (fun w hw => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (sk_leg_bound n hw) (hfb w hw) (abs_nonneg _) (by positivity))
    simpa using this
  rw [Real.norm_eq_abs] at hI
  have h2 : |(2 * (n : ℝ) + 1)| ≤ 2 * 2 ^ n := by
    rw [abs_of_nonneg (by positivity)]
    linarith [sk_succ_le_two_pow n]
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfb 0 ⟨le_rfl, zero_le_one⟩)
  rw [skCoef, abs_mul]
  calc |(2 * (n : ℝ) + 1)| * |∫ w in Icc (0 : ℝ) 1, (skLeg n).eval w * f w|
      ≤ (2 * 2 ^ n) * (8 ^ n * M) := mul_le_mul h2 hI (abs_nonneg _) (by positivity)
    _ = 2 * M * 16 ^ n := by
        rw [show (16 : ℝ) = 2 * 8 by norm_num, mul_pow]; ring

theorem sk_growth_coef {f : ℝ → ℝ} {M : ℝ} (hfb : ∀ w ∈ Icc (0 : ℝ) 1, |f w| ≤ M) :
    SkGrowth (skLegFam (skCoef f)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfb 0 ⟨le_rfl, zero_le_one⟩)
  exact sk_growth_legFam (by positivity) (by norm_num) (sk_coef_le hfb)

/-- **`P_t f` is a Legendre series** for `t > 0`, `y ∈ [0,1]`, bounded measurable `f`. -/
theorem sk_semigroupY_eq_ser {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} {M : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) 1)))
    (hfb : ∀ w ∈ Icc (0 : ℝ) 1, |f w| ≤ M) {t y : ℝ} (ht : 0 < t) (hy : y ∈ Icc (0 : ℝ) 1) :
    skSemigroupY D0 f t y = skSer D0 (skLegFam (skCoef f)) t y := by
  have hfi := sk_integrableOn_of_bound hfm hfb
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfb 0 ⟨le_rfl, zero_le_one⟩)
  unfold skSemigroupY
  rw [sk_kernelY_eq_indicator ht hy]
  have e1 : (fun y' => (Icc (0 : ℝ) 1).indicator (skSphereSeries D0 t y) y' * f y') =
      (Icc (0 : ℝ) 1).indicator fun y' => skSphereSeries D0 t y y' * f y' := by
    funext y'
    by_cases h : y' ∈ Icc (0 : ℝ) 1 <;> simp [h]
  rw [e1, integral_indicator measurableSet_Icc]
  have hint : ∀ n, Integrable (fun y' => skYTerm D0 t y y' n * f y')
      (volume.restrict (Icc 0 1)) := fun n =>
    hfi.continuousOn_mul (skp_term_continuous_right D0 t y n).continuousOn isCompact_Icc
  have hsum : Summable fun n => ∫ y' in Icc (0 : ℝ) 1, ‖skYTerm D0 t y y' n * f y'‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((sk_summable_bound hD0 ht).mul_right M)
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : ℝ) 1)
      (f := fun y' => ‖skYTerm D0 t y y' n * f y'‖) (C := skYBound D0 t n * M) (by simp)
      (fun y' hy' => by
        rw [norm_norm, norm_mul, Real.norm_eq_abs (f y')]
        exact mul_le_mul (sk_term_le hy hy' n) (hfb y' hy') (abs_nonneg _)
          (skp_bound_nonneg D0 t n))
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at this
    simpa using this
  have e2 : (fun y' => skSphereSeries D0 t y y' * f y') =
      fun y' => ∑' n, skYTerm D0 t y y' n * f y' := by
    funext y'; rw [skSphereSeries, tsum_mul_right]
  rw [e2, ← integral_tsum_of_summable_integral_norm hint hsum]
  unfold skSer
  refine tsum_congr fun n => ?_
  have e3 : (fun y' => skYTerm D0 t y y' n * f y') = fun y' =>
      ((2 * n + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * (skLeg n).eval y) *
        ((skLeg n).eval y' * f y') := by
    funext y'; simp only [skYTerm]; ring
  rw [e3, integral_const_mul]
  simp only [skLegFam, skCoef, eval_mul, eval_C]
  ring

/-- **Continuity of `P_t f` up to the boundary**: on `(0,∞) × [0,1]`. -/
theorem sk_semigroupY_continuousOn {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} {M : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) 1)))
    (hfb : ∀ w ∈ Icc (0 : ℝ) 1, |f w| ≤ M) :
    ContinuousOn (fun p : ℝ × ℝ => skSemigroupY D0 f p.1 p.2) (Ioi 0 ×ˢ Icc 0 1) :=
  ((sk_ser_contDiffOn hD0 (sk_growth_coef hfb)).continuousOn.mono
    (prod_mono subset_rfl (subset_univ _))).congr
    fun _ hp => sk_semigroupY_eq_ser hD0 hfm hfb hp.1 hp.2

/-- The extension `skSer D0 (skLegFam (skCoef f))` of `P_t f` is `C^∞` on `(0,∞) × ℝ`. -/
theorem sk_semigroupY_ext_contDiffOn {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} {M : ℝ}
    (hfb : ∀ w ∈ Icc (0 : ℝ) 1, |f w| ≤ M) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => skSer D0 (skLegFam (skCoef f)) p.1 p.2) (Ioi 0 ×ˢ univ) :=
  sk_ser_contDiffOn hD0 (sk_growth_coef hfb)

/-- The extension of `P_t f` solves the backward equation on `(0,∞) × ℝ`. -/
theorem sk_semigroupY_ext_pde {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} {M : ℝ}
    (hfb : ∀ w ∈ Icc (0 : ℝ) 1, |f w| ≤ M) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    deriv (fun s => skSer D0 (skLegFam (skCoef f)) s y) t =
      D0 / 2 * (y * (1 - y) * deriv (deriv fun z => skSer D0 (skLegFam (skCoef f)) t z) y +
        (1 - 2 * y) * deriv (fun z => skSer D0 (skLegFam (skCoef f)) t z) y) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfb 0 ⟨le_rfl, zero_le_one⟩)
  exact sk_legFam_pde_deriv hD0 (by positivity) (by norm_num) (sk_coef_le hfb) ht y

/-- `P_t f` is `C^∞` on the open set `(0,∞) × (0,1)`. -/
theorem sk_semigroupY_contDiffOn {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} {M : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) 1)))
    (hfb : ∀ w ∈ Icc (0 : ℝ) 1, |f w| ≤ M) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => skSemigroupY D0 f p.1 p.2) (Ioi 0 ×ˢ Ioo 0 1) :=
  ((sk_semigroupY_ext_contDiffOn hD0 hfb).mono (prod_mono subset_rfl (subset_univ _))).congr
    fun _ hp => sk_semigroupY_eq_ser hD0 hfm hfb hp.1 (Ioo_subset_Icc_self hp.2)

/-- `P_t f` is `C^∞` on `(0,∞) × [0,1]` (within-derivatives up to `y ∈ {0, 1}`). -/
theorem sk_semigroupY_contDiffOn_Icc {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} {M : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) 1)))
    (hfb : ∀ w ∈ Icc (0 : ℝ) 1, |f w| ≤ M) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => skSemigroupY D0 f p.1 p.2) (Ioi 0 ×ˢ Icc 0 1) :=
  ((sk_semigroupY_ext_contDiffOn hD0 hfb).mono (prod_mono subset_rfl (subset_univ _))).congr
    fun _ hp => sk_semigroupY_eq_ser hD0 hfm hfb hp.1 hp.2

/-- **The backward equation for `P_t f`** on `(0,∞) × (0,1)`. -/
theorem sk_semigroupY_pde {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} {M : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) 1)))
    (hfb : ∀ w ∈ Icc (0 : ℝ) 1, |f w| ≤ M) {t y : ℝ} (ht : 0 < t) (hy : y ∈ Ioo (0 : ℝ) 1) :
    deriv (fun s => skSemigroupY D0 f s y) t =
      D0 / 2 * (y * (1 - y) * deriv (deriv fun z => skSemigroupY D0 f t z) y +
        (1 - 2 * y) * deriv (fun z => skSemigroupY D0 f t z) y) := by
  have hz : ∀ z ∈ Ioo (0 : ℝ) 1, (fun w => skSemigroupY D0 f t w) =ᶠ[𝓝 z]
      fun w => skSer D0 (skLegFam (skCoef f)) t w := fun z hz =>
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hz) fun w hw =>
      sk_semigroupY_eq_ser hD0 hfm hfb ht (Ioo_subset_Icc_self hw)
  have ht' : (fun s => skSemigroupY D0 f s y) =ᶠ[𝓝 t]
      fun s => skSer D0 (skLegFam (skCoef f)) s y :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht) fun s hs =>
      sk_semigroupY_eq_ser hD0 hfm hfb hs (Ioo_subset_Icc_self hy)
  have hy2 : deriv (fun w => skSemigroupY D0 f t w) =ᶠ[𝓝 y]
      deriv fun w => skSer D0 (skLegFam (skCoef f)) t w :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hy) fun z hz' => (hz z hz').deriv_eq
  rw [ht'.deriv_eq, (hz y hy).deriv_eq, hy2.deriv_eq]
  exact sk_semigroupY_ext_pde hD0 hfb ht y

end BlockBand.Diffusion
