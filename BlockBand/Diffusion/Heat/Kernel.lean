module

public import BlockBand.Diffusion.Heat.Defs

/-!
# Elementary facts about the product kernel used by the corner heat identity

For `D₀ > 0` and `z ∈ exBaseStrip`: `p_t(z, ·)` vanishes off the strip and for `t ≤ 0`, is
integrable with mass one for `t > 0`, and `P_t F(z)` (`chP`) is bounded by any bound of `|F|` on
the strip, nonnegative for `F ≥ 0` on the strip, and jointly measurable in parameters.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

variable {D0 : ℝ}

theorem ch_exKernel_eq_zero_of_notMem (t : ℝ) (z : ℝ × ℝ) {z' : ℝ × ℝ}
    (hz' : z' ∉ exBaseStrip) : exKernel D0 t z z' = 0 := by
  rw [exKernel_eq]
  by_cases h1 : 0 ≤ z'.1
  · have h2 : z'.2 ∉ Icc (0 : ℝ) 1 := fun h2 => hz' ⟨h1, h2⟩
    rw [sk_kernelY_of_notMem_right _ h2, mul_zero]
  · simp [mkKernelX, h1]

theorem ch_exKernel_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) (z z' : ℝ × ℝ) :
    exKernel D0 t z z' = 0 := by
  rw [exKernel_eq]
  simp [mkKernelX, not_lt.2 ht]

theorem ch_mem_of_exKernel_ne_zero {t : ℝ} {z z' : ℝ × ℝ} (h : exKernel D0 t z z' ≠ 0) :
    z' ∈ exBaseStrip := by
  by_contra hn
  exact h (ch_exKernel_eq_zero_of_notMem t z hn)

theorem ch_integrable_exKernel (hD0 : 0 < D0) {t : ℝ} (ht : 0 < t) {z : ℝ × ℝ}
    (hz : z ∈ exBaseStrip) : Integrable (exKernel D0 t z) := by
  have h := (mk_integrable_kernelX hD0 ht hz.1).mul_prod (sk_integrable_kernelY hD0 t z.2)
  rw [← Measure.volume_eq_prod] at h
  exact h

theorem ch_integral_exKernel (hD0 : 0 < D0) {t : ℝ} (ht : 0 < t) {z : ℝ × ℝ}
    (hz : z ∈ exBaseStrip) : ∫ z', exKernel D0 t z z' = 1 := by
  simp_rw [exKernel_eq]
  rw [Measure.volume_eq_prod, integral_prod_mul (fun x' => mkKernelX D0 t z.1 x')
    (fun y' => skKernelY D0 t z.2 y'), mk_integral_kernelX_univ hD0 ht hz.1,
    sk_integral_kernelY hD0 ht hz.2, one_mul]

theorem ch_abs_exKernel_mul_le (hD0 : 0 < D0) (t : ℝ) (z : ℝ × ℝ) {F : ℝ × ℝ → ℝ} {C : ℝ}
    (hFC : ∀ w ∈ exBaseStrip, |F w| ≤ C) (z' : ℝ × ℝ) :
    |exKernel D0 t z z' * F z'| ≤ exKernel D0 t z z' * C := by
  by_cases hz' : z' ∈ exBaseStrip
  · rw [abs_mul, abs_of_nonneg (exKernel_nonneg hD0 t z z')]
    exact mul_le_mul_of_nonneg_left (hFC z' hz') (exKernel_nonneg hD0 t z z')
  · simp [ch_exKernel_eq_zero_of_notMem t z hz']

theorem ch_integrable_exKernel_mul (hD0 : 0 < D0) {t : ℝ} (ht : 0 < t) {z : ℝ × ℝ}
    (hz : z ∈ exBaseStrip) {F : ℝ × ℝ → ℝ} (hF : AEStronglyMeasurable F volume) {C : ℝ}
    (hFC : ∀ w ∈ exBaseStrip, |F w| ≤ C) : Integrable fun z' => exKernel D0 t z z' * F z' := by
  have hp := ch_integrable_exKernel hD0 ht hz
  refine (hp.mul_const C).mono' (hp.aestronglyMeasurable.mul hF) (ae_of_all _ fun z' => ?_)
  rw [Real.norm_eq_abs]
  exact ch_abs_exKernel_mul_le hD0 t z hFC z'

/-- `|P_t F(z)| ≤ C` whenever `|F| ≤ C` on the strip (every `t`; `P_t = 0` for `t ≤ 0`). -/
theorem ch_abs_chP_le (hD0 : 0 < D0) (t : ℝ) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    {F : ℝ × ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hFC : ∀ w ∈ exBaseStrip, |F w| ≤ C) :
    |chP D0 t F z| ≤ C := by
  rcases le_or_gt t 0 with ht | ht
  · simp [chP, ch_exKernel_eq_zero_of_nonpos ht, hC]
  · unfold chP
    calc |∫ z', exKernel D0 t z z' * F z'| ≤ ∫ z', |exKernel D0 t z z' * F z'| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z', exKernel D0 t z z' * C := by
          by_cases hi : Integrable fun z' => |exKernel D0 t z z' * F z'|
          · exact integral_mono hi ((ch_integrable_exKernel hD0 ht hz).mul_const C)
              (ch_abs_exKernel_mul_le hD0 t z hFC)
          · rw [integral_undef hi]
            exact integral_nonneg fun z' => mul_nonneg (exKernel_nonneg hD0 t z z') hC
      _ = C := by rw [integral_mul_const, ch_integral_exKernel hD0 ht hz, one_mul]

theorem ch_chP_nonneg (hD0 : 0 < D0) (t : ℝ) (z : ℝ × ℝ) {F : ℝ × ℝ → ℝ}
    (hF : ∀ w ∈ exBaseStrip, 0 ≤ F w) : 0 ≤ chP D0 t F z := by
  refine integral_nonneg fun z' => ?_
  by_cases hz' : z' ∈ exBaseStrip
  · exact mul_nonneg (exKernel_nonneg hD0 t z z') (hF z' hz')
  · simp [ch_exKernel_eq_zero_of_notMem t z hz']

/-- Joint measurability of `P_{τ(a)} F_a(z)` in a parameter `a`. -/
theorem ch_stronglyMeasurable_chP (hD0 : 0 < D0) {α : Type*} [MeasurableSpace α]
    {F : α → ℝ × ℝ → ℝ} (hF : Measurable (Function.uncurry F)) {τ : α → ℝ} (hτ : Measurable τ)
    (z : ℝ × ℝ) : StronglyMeasurable fun a => chP D0 (τ a) (F a) z := by
  have hk : Measurable fun q : α × (ℝ × ℝ) => exKernel D0 (τ q.1) z q.2 :=
    (exKernel_measurable hD0).comp (f := fun q : α × (ℝ × ℝ) => (τ q.1, z, q.2)) (by fun_prop)
  have hm : StronglyMeasurable fun q : α × (ℝ × ℝ) => exKernel D0 (τ q.1) z q.2 * F q.1 q.2 :=
    (hk.mul hF).stronglyMeasurable
  exact hm.integral_prod_right'

/-- `ofReal (P_t F(z)) = ∫⁻ ofReal(p_t) ofReal(F)` for `F ≥ 0` bounded on the strip. -/
theorem ch_ofReal_chP (hD0 : 0 < D0) {t : ℝ} (ht : 0 < t) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    {F : ℝ × ℝ → ℝ} (hFm : Measurable F) (hF0 : ∀ w ∈ exBaseStrip, 0 ≤ F w) {C : ℝ}
    (hFC : ∀ w ∈ exBaseStrip, |F w| ≤ C) :
    ENNReal.ofReal (chP D0 t F z) =
      ∫⁻ z', ENNReal.ofReal (exKernel D0 t z z') * ENNReal.ofReal (F z') := by
  have h0 : ∀ z', 0 ≤ exKernel D0 t z z' * F z' := fun z' => by
    by_cases hz' : z' ∈ exBaseStrip
    · exact mul_nonneg (exKernel_nonneg hD0 t z z') (hF0 z' hz')
    · simp [ch_exKernel_eq_zero_of_notMem t z hz']
  unfold chP
  rw [ofReal_integral_eq_lintegral_ofReal
    (ch_integrable_exKernel_mul hD0 ht hz hFm.aestronglyMeasurable hFC) (ae_of_all _ h0)]
  refine lintegral_congr fun z' => ?_
  by_cases hz' : z' ∈ exBaseStrip
  · rw [ENNReal.ofReal_mul (exKernel_nonneg hD0 t z z')]
  · simp [ch_exKernel_eq_zero_of_notMem t z hz']

end BlockBand.Diffusion
