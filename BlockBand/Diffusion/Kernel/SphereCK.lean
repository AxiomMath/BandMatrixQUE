module

public import BlockBand.Diffusion.Kernel.SphereNonneg
public import BlockBand.Diffusion.Kernel.SpherePDE
public import BlockBand.Diffusion.Process.TransitionFdd

/-!
# Chapman–Kolmogorov, symmetry and bounds for the sphere factor

We prove symmetry, the Chapman–Kolmogorov equation, a uniform bound and joint continuity for the
sphere factor `pY = skKernelY`.

* `sk_kernelY_symm`: `pY_t(y, y') = pY_t(y', y)` for all real arguments;
* `sk_kernelY_chapmanKolmogorov`: the Chapman–Kolmogorov equation in the form
  `ChapmanKolmogorov volume (fun t x y => ENNReal.ofReal (skKernelY D0 t x y))`;
* `sk_kernelY_le`: `pY_t(y, y') ≤ skSupY D0 δ := Σ_n (2n+1)e^{-(D₀/2)n(n+1)δ}64ⁿ` for all
  `t ≥ δ > 0` and all `y, y'` (a uniform bound on `[δ, ∞) × ℝ²`);
* `sk_sphereSeries_continuousOn3`: the series is jointly continuous in `(t, y, y')` on
  `(0,∞) × ℝ × ℝ`; `sk_kernelY_continuousOn3`: so is `skKernelY` on `(0,∞) × [0,1] × [0,1]`;
* `sk_kernelY_corner_continuousOn`: `y ↦ pY_t(y, 0)` is continuous on `[0,1]`, and
  `sk_kernelY_corner_continuousOn2`: `(t, y) ↦ pY_t(y, 0)` is continuous on `(0,∞) × [0,1]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Polynomial
open scoped ENNReal

/-!
### Symmetry, nonnegativity, support
-/

theorem sk_kernelY_symm (D0 t y y' : ℝ) : skKernelY D0 t y y' = skKernelY D0 t y' y := by
  unfold skKernelY
  by_cases h : 0 < t ∧ y ∈ Icc (0 : ℝ) 1 ∧ y' ∈ Icc (0 : ℝ) 1
  · rw [ite_eq_left h, ite_eq_left ⟨h.1, h.2.2, h.2.1⟩, skp_series_symm]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.1, h'.2.2, h'.2.1⟩]

theorem sk_kernelY_nonneg {D0 : ℝ} (hD0 : 0 < D0) (t y y' : ℝ) : 0 ≤ skKernelY D0 t y y' := by
  unfold skKernelY
  split_ifs with h
  · exact skp_series_nonneg hD0 h.1 h.2.1 h.2.2
  · exact le_rfl

theorem sk_kernelY_of_notMem_left {D0 t y : ℝ} (hy : y ∉ Icc (0 : ℝ) 1) (y' : ℝ) :
    skKernelY D0 t y y' = 0 := by
  simp [skKernelY, hy]

theorem sk_kernelY_of_notMem_right {D0 t y' : ℝ} (y : ℝ) (hy' : y' ∉ Icc (0 : ℝ) 1) :
    skKernelY D0 t y y' = 0 := by
  simp [skKernelY, hy']

/-!
### Chapman–Kolmogorov
-/

/-- **Chapman–Kolmogorov for `skKernelY`**, at all real start and end points. -/
theorem sk_kernelY_chapman {D0 s u : ℝ} (hD0 : 0 < D0) (hs : 0 < s) (hu : 0 < u) (y y'' : ℝ) :
    skKernelY D0 (s + u) y y'' = ∫ y', skKernelY D0 s y y' * skKernelY D0 u y' y'' := by
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · by_cases hy'' : y'' ∈ Icc (0 : ℝ) 1
    · have e : (fun y' => skKernelY D0 s y y' * skKernelY D0 u y' y'') =
          (Icc (0 : ℝ) 1).indicator
            (fun w => skSphereSeries D0 s y w * skSphereSeries D0 u w y'') := by
        funext w
        by_cases hw : w ∈ Icc (0 : ℝ) 1
        · rw [indicator_of_mem hw, sk_kernelY_eq hs hy hw, sk_kernelY_eq hu hw hy'']
        · rw [indicator_of_notMem hw, sk_kernelY_of_notMem_right y hw, zero_mul]
      rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one, sk_kernelY_eq (add_pos hs hu) hy hy'',
        skp_chapman hD0 hs hu hy hy'']
    · have e : (fun y' => skKernelY D0 s y y' * skKernelY D0 u y' y'') = fun _ => 0 :=
        funext fun w => by rw [sk_kernelY_of_notMem_right w hy'', mul_zero]
      rw [e, integral_zero, sk_kernelY_of_notMem_right y hy'']
  · have e : (fun y' => skKernelY D0 s y y' * skKernelY D0 u y' y'') = fun _ => 0 :=
      funext fun w => by rw [sk_kernelY_of_notMem_left hy w, zero_mul]
    rw [e, integral_zero, sk_kernelY_of_notMem_left hy y'']

/-!
### Uniform bound
-/

/-- The uniform bound `Σ_n (2n+1)e^{-(D₀/2)n(n+1)δ}64ⁿ` for `pY_t`, `t ≥ δ`. -/
def skSupY (D0 δ : ℝ) : ℝ := ∑' n, skYBound D0 δ n

theorem sk_supY_nonneg (D0 δ : ℝ) : 0 ≤ skSupY D0 δ := tsum_nonneg (skp_bound_nonneg D0 δ)

theorem sk_yBound_anti {D0 δ t : ℝ} (hD0 : 0 ≤ D0) (ht : δ ≤ t) (n : ℕ) :
    skYBound D0 t n ≤ skYBound D0 δ n := by
  unfold skYBound
  have := sk_exp_le hD0 ht n
  gcongr

/-- **On-diagonal bound**: `pY_t(y, y') ≤ skSupY D0 δ` for `t ≥ δ > 0` and all `y, y'`. -/
theorem sk_kernelY_le {D0 δ t : ℝ} (hD0 : 0 < D0) (hδ : 0 < δ) (ht : δ ≤ t) (y y' : ℝ) :
    skKernelY D0 t y y' ≤ skSupY D0 δ := by
  unfold skKernelY
  split_ifs with h
  · calc skSphereSeries D0 t y y' ≤ ‖skSphereSeries D0 t y y'‖ := Real.le_norm_self _
      _ ≤ ∑' n, skYBound D0 t n := skp_series_norm_le hD0 h.1 h.2.1 h.2.2
      _ ≤ skSupY D0 δ := Summable.tsum_le_tsum (sk_yBound_anti hD0.le ht)
          (sk_summable_bound hD0 h.1) (sk_summable_bound hD0 hδ)
  · exact sk_supY_nonneg D0 δ

theorem sk_kernelY_measurable_right {D0 : ℝ} (hD0 : 0 < D0) (t y : ℝ) :
    Measurable fun w => skKernelY D0 t y w :=
  (sk_kernelY_measurable hD0).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem sk_kernelY_measurable_left {D0 : ℝ} (hD0 : 0 < D0) (t y' : ℝ) :
    Measurable fun w => skKernelY D0 t w y' :=
  (sk_kernelY_measurable hD0).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))

theorem sk_kernelY_integrable_mul {D0 s u : ℝ} (hD0 : 0 < D0) (hs : 0 < s) (hu : 0 < u)
    (x y : ℝ) : Integrable fun w => skKernelY D0 s x w * skKernelY D0 u w y := by
  have hmeas : Measurable fun w => skKernelY D0 s x w * skKernelY D0 u w y :=
    (sk_kernelY_measurable_right hD0 s x).mul (sk_kernelY_measurable_left hD0 u y)
  have e : (fun w => skKernelY D0 s x w * skKernelY D0 u w y) =
      (Icc (0 : ℝ) 1).indicator fun w => skKernelY D0 s x w * skKernelY D0 u w y := by
    funext w
    by_cases hw : w ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hw]
    · rw [indicator_of_notMem hw, sk_kernelY_of_notMem_right x hw, zero_mul]
  rw [e, integrable_indicator_iff measurableSet_Icc]
  refine Measure.integrableOn_of_bounded (M := skSupY D0 s * skSupY D0 u)
    measure_Icc_lt_top.ne hmeas.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sk_kernelY_nonneg hD0 _ _ _)
    (sk_kernelY_nonneg hD0 _ _ _))]
  exact mul_le_mul (sk_kernelY_le hD0 hs le_rfl _ _) (sk_kernelY_le hD0 hu le_rfl _ _)
    (sk_kernelY_nonneg hD0 _ _ _) (sk_supY_nonneg D0 s)

/-- **Chapman–Kolmogorov in `ChapmanKolmogorov` form**, at all real points. -/
theorem sk_kernelY_chapmanKolmogorov {D0 : ℝ} (hD0 : 0 < D0) :
    ChapmanKolmogorov volume fun t x y => ENNReal.ofReal (skKernelY D0 t x y) := by
  intro s u hs hu x y
  show ∫⁻ w, ENNReal.ofReal (skKernelY D0 s x w) * ENNReal.ofReal (skKernelY D0 u w y) =
    ENNReal.ofReal (skKernelY D0 (s + u) x y)
  calc ∫⁻ w, ENNReal.ofReal (skKernelY D0 s x w) * ENNReal.ofReal (skKernelY D0 u w y)
      = ∫⁻ w, ENNReal.ofReal (skKernelY D0 s x w * skKernelY D0 u w y) :=
        lintegral_congr fun w => (ENNReal.ofReal_mul (sk_kernelY_nonneg hD0 _ _ _)).symm
    _ = ENNReal.ofReal (∫ w, skKernelY D0 s x w * skKernelY D0 u w y) :=
        (ofReal_integral_eq_lintegral_ofReal (sk_kernelY_integrable_mul hD0 hs hu x y)
          (ae_of_all _ fun w =>
            mul_nonneg (sk_kernelY_nonneg hD0 _ _ _) (sk_kernelY_nonneg hD0 _ _ _))).symm
    _ = ENNReal.ofReal (skKernelY D0 (s + u) x y) := by rw [← sk_kernelY_chapman hD0 hs hu]

/-!
### Joint continuity and the corner
-/

/-- **Joint continuity of the series** in `(t, y, y')` on `(0,∞) × ℝ × ℝ`. -/
theorem sk_sphereSeries_continuousOn3 {D0 : ℝ} (hD0 : 0 < D0) :
    ContinuousOn (fun w : ℝ × ℝ × ℝ => skSphereSeries D0 w.1 w.2.1 w.2.2) (Ioi 0 ×ˢ univ) := by
  refine continuousOn_of_locally_continuousOn fun w hw => ?_
  have ht : 0 < w.1 := hw.1
  set R : ℝ := |w.2.1| + |w.2.2| + 1 with hRdef
  have hR : 1 ≤ R := by rw [hRdef]; linarith [abs_nonneg w.2.1, abs_nonneg w.2.2]
  refine ⟨Ioi (w.1 / 2) ×ˢ (Ioo (-R) R ×ˢ Ioo (-R) R),
    isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioo), ?_, ?_⟩
  · refine Set.mk_mem_prod (by show w.1 / 2 < w.1; linarith) (Set.mk_mem_prod ?_ ?_)
    · constructor <;> linarith [neg_abs_le w.2.1, le_abs_self w.2.1, abs_nonneg w.2.2]
    · constructor <;> linarith [neg_abs_le w.2.2, le_abs_self w.2.2, abs_nonneg w.2.1]
  refine ContinuousOn.mono ?_ inter_subset_right
  refine continuousOn_tsum (fun n => (sk_term_continuous D0 n).continuousOn)
    (skp_summable_bound_gen hD0 (half_pos ht) (K := (16 * R) ^ 2) (by positivity))
    (fun n v hv => ?_)
  have h1 := sk_leg_eval_le (y := v.2.1) hR (abs_le.2 ⟨hv.2.1.1.le, hv.2.1.2.le⟩) n
  have h2 := sk_leg_eval_le (y := v.2.2) hR (abs_le.2 ⟨hv.2.2.1.le, hv.2.2.2.le⟩) n
  have he := sk_exp_le hD0.le (le_of_lt (mem_Ioi.1 hv.1)) n
  have hc : 0 ≤ (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * v.1)) := by
    positivity
  rw [Real.norm_eq_abs, skYTerm, abs_mul, abs_mul, abs_of_nonneg hc, mul_assoc,
    ← pow_mul, show 2 * n = n + n by ring, pow_add]
  calc (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * v.1)) *
        (|(skLeg n).eval v.2.1| * |(skLeg n).eval v.2.2|)
      ≤ (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * (w.1 / 2))) *
        ((16 * R) ^ n * (16 * R) ^ n) := by
        gcongr
    _ = _ := by ring

theorem sk_kernelY_continuousOn3 {D0 : ℝ} (hD0 : 0 < D0) :
    ContinuousOn (fun w : ℝ × ℝ × ℝ => skKernelY D0 w.1 w.2.1 w.2.2)
      (Ioi 0 ×ˢ (Icc 0 1 ×ˢ Icc 0 1)) :=
  ((sk_sphereSeries_continuousOn3 hD0).mono (prod_mono subset_rfl (subset_univ _))).congr
    fun _ hw => sk_kernelY_eq hw.1 hw.2.1 hw.2.2

/-- **Corner continuity in the start**: `y ↦ pY_t(y, 0)` is continuous on `[0,1]`. -/
theorem sk_kernelY_corner_continuousOn {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) :
    ContinuousOn (fun y => skKernelY D0 t y 0) (Icc 0 1) :=
  (sk_kernelY_continuousOn3 hD0).comp
    (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn
    fun _ hy => Set.mk_mem_prod ht (Set.mk_mem_prod hy ⟨le_rfl, zero_le_one⟩)

/-- Joint continuity of `(t, y) ↦ pY_t(y, 0)` on `(0,∞) × [0,1]`. -/
theorem sk_kernelY_corner_continuousOn2 {D0 : ℝ} (hD0 : 0 < D0) :
    ContinuousOn (fun p : ℝ × ℝ => skKernelY D0 p.1 p.2 0) (Ioi 0 ×ˢ Icc 0 1) :=
  (sk_kernelY_continuousOn3 hD0).comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
    fun _ hp => Set.mk_mem_prod hp.1 (Set.mk_mem_prod hp.2 ⟨le_rfl, zero_le_one⟩)

end BlockBand.Diffusion
