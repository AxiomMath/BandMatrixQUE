module

public import BlockBand.Endpoints.Response.LifetimeBridgeKernelSphere
public import BlockBand.Endpoints.Response.LifetimeBridgeKernelHyperbolic

/-!
# The explicit product base kernel `p_t(z, z') = pX_t(x, x') pY_t(y, y')`

`lbkKernel D0 t z z' = lbkKernelX D0 t z.1 z'.1 * lbkKernelY D0 t z.2 z'.2`, the product of
McKean's hyperbolic radial kernel (`lbkKernelX`) and the Legendre series of the sphere
(`lbkKernelY`). It vanishes for `t ≤ 0` and for `z'` off the closed strip, so it is a density on
`ℝ²` (relative to Lebesgue measure).

For `D₀ > 0` this file proves the factorisation (definitional, everywhere), joint measurability
(`lbk_kernel_measurable`), continuity of `p_t(z, ·)` on the closed strip
(`lbk_kernel_continuousOn`) and, assuming the deterministic sphere positivity
`LbkSphereKernelPos`, nonnegativity everywhere (`lbk_kernel_nonneg`), strict positivity of the
corner value `p_t(z, (0,0))` for `z` in the strip (`lbk_kernel_corner_pos`), the product formula
for integrals over rectangles (`lbk_lintegral_prod`) and the sphere normalisation in `ℝ≥0∞`
(`lbk_lintegral_kernelY`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The explicit base kernel `p_t(z, z') = pX_t(x, x') · pY_t(y, y')`. -/
def lbkKernel (D0 : ℝ) (t : ℝ) (z z' : ℝ × ℝ) : ℝ :=
  lbkKernelX D0 t z.1 z'.1 * lbkKernelY D0 t z.2 z'.2

/-- Strict positivity of the spherical heat kernel on `[0,1]²` for `t > 0`, including the poles
`y' ∈ {0, 1}`: positivity of the smooth elliptic heat kernel on the connected sphere (strong
maximum principle or Harnack inequality for `(D₀/2)Δ_{S²}`, or the probabilistic
representation). -/
def LbkSphereKernelPos (D0 : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ y ∈ Icc (0 : ℝ) 1, ∀ y' ∈ Icc (0 : ℝ) 1, 0 < lbkSphereSeries D0 t y y'

theorem lbk_kernel_measurable {D0 : ℝ} (hD0 : 0 < D0) :
    Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => lbkKernel D0 w.1 w.2.1 w.2.2 := by
  have hX : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => lbkKernelX D0 w.1 w.2.1.1 w.2.2.1 :=
    (lbk_kernelX_measurable D0).comp
      (f := fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1.1, w.2.2.1)) (by fun_prop)
  have hY : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => lbkKernelY D0 w.1 w.2.1.2 w.2.2.2 :=
    (lbk_kernelY_measurable hD0).comp
      (f := fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1.2, w.2.2.2)) (by fun_prop)
  exact hX.mul hY

theorem lbk_kernelY_nonneg {D0 : ℝ} (hpos : LbkSphereKernelPos D0) (t y y' : ℝ) :
    0 ≤ lbkKernelY D0 t y y' := by
  unfold lbkKernelY
  split_ifs with h
  · exact (hpos t h.1 y h.2.1 y' h.2.2).le
  · exact le_rfl

theorem lbk_kernel_nonneg {D0 : ℝ} (hD0 : 0 < D0) (hpos : LbkSphereKernelPos D0) (t : ℝ)
    (z z' : ℝ × ℝ) : 0 ≤ lbkKernel D0 t z z' :=
  mul_nonneg (lbk_kernelX_nonneg hD0 _ _ _) (lbk_kernelY_nonneg hpos _ _ _)

theorem lbk_kernel_continuousOn {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) {z : ℝ × ℝ}
    (hz : z ∈ baseStrip) : ContinuousOn (lbkKernel D0 t z) baseStrip := by
  have hX : ContinuousOn (fun z' : ℝ × ℝ => lbkHypRadial (D0 * t / 2) z.1 z'.1) baseStrip :=
    ((lbk_hypRadial_continuous (by positivity) z.1).comp continuous_fst).continuousOn
  have hY : ContinuousOn (fun z' : ℝ × ℝ => lbkSphereSeries D0 t z.2 z'.2) baseStrip :=
    (lbk_sphereSeries_continuousOn hD0 ht hz.2).comp continuous_snd.continuousOn
      fun z' hz' => hz'.2
  refine (hX.mul hY).congr fun z' hz' => ?_
  simp only [lbkKernel]
  rw [lbk_kernelX_eq ht hz'.1, lbk_kernelY_eq ht hz.2 hz'.2]
  rfl

theorem lbk_kernel_corner_pos {D0 t : ℝ} (hD0 : 0 < D0) (hpos : LbkSphereKernelPos D0)
    (ht : 0 < t) {z : ℝ × ℝ} (hz : z ∈ baseStrip) : 0 < lbkKernel D0 t z (0, 0) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine mul_pos (lbk_kernelX_zero_pos hD0 ht z.1) ?_
  rw [lbk_kernelY_eq ht hz.2 h0]
  exact hpos t ht z.2 hz.2 0 h0

theorem lbk_kernelY_integrable {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) : Integrable (lbkKernelY D0 t y) := by
  rw [lbk_kernelY_eq_indicator ht hy]
  exact (lbk_sphereSeries_continuousOn hD0 ht hy).integrableOn_Icc.integrable_indicator
    measurableSet_Icc

/-- The sphere normalisation in `ℝ≥0∞`: `∫⁻ pY_t(y, ·) = 1`. -/
theorem lbk_lintegral_kernelY {D0 t y : ℝ} (hD0 : 0 < D0) (hpos : LbkSphereKernelPos D0)
    (ht : 0 < t) (hy : y ∈ Icc (0 : ℝ) 1) :
    ∫⁻ y', ENNReal.ofReal (lbkKernelY D0 t y y') = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (lbk_kernelY_integrable hD0 ht hy)
    (ae_of_all _ fun y' => lbk_kernelY_nonneg hpos t y y'), lbk_integral_kernelY hD0 ht hy,
    ENNReal.ofReal_one]

/-- Integrals of the product kernel over rectangles factorise. -/
theorem lbk_lintegral_prod {D0 t : ℝ} (hD0 : 0 < D0) (z : ℝ × ℝ) (A B : Set ℝ) :
    ∫⁻ z' in A ×ˢ B, ENNReal.ofReal (lbkKernel D0 t z z') =
      (∫⁻ x' in A, ENNReal.ofReal (lbkKernelX D0 t z.1 x')) *
        ∫⁻ y' in B, ENNReal.ofReal (lbkKernelY D0 t z.2 y') := by
  have hX : Measurable fun x' => ENNReal.ofReal (lbkKernelX D0 t z.1 x') :=
    ((lbk_kernelX_measurable D0).comp (f := fun x' : ℝ => (t, z.1, x')) (by fun_prop)).ennreal_ofReal
  have hY : Measurable fun y' => ENNReal.ofReal (lbkKernelY D0 t z.2 y') :=
    ((lbk_kernelY_measurable hD0).comp (f := fun y' : ℝ => (t, z.2, y')) (by fun_prop)).ennreal_ofReal
  simp_rw [lbkKernel, ENNReal.ofReal_mul (lbk_kernelX_nonneg hD0 _ _ _)]
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
  exact lintegral_prod_mul hX.aemeasurable hY.aemeasurable

end BlockBand.Endpoints
