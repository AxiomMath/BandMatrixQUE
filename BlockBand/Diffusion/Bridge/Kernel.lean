module

public import BlockBand.Diffusion.Base.TransitionLawHolds
public import BlockBand.Diffusion.Kernel.SphereCK
public import BlockBand.Diffusion.Process.TransitionFdd

/-!
# The source-indicator adapter of the base kernel and its Chapman–Kolmogorov identity

`D₀ > 0`; Lebesgue measure on `ℝ`, `ℝ × ℝ`; `S = exBaseStrip = [0,∞) × [0,1]`. The adapter
`brKernel D0 t a b = 1_S(a) p_t(a, b)` extends the base kernel by zero to sources off the strip.

* `br_mk_kernelX_chapmanKolmogorov`: Chapman–Kolmogorov for the X factor at every point of the
  half-line, unconditionally (from `mcKeanBackwardFacts_holds` and `timeMollifyDuality_holds`).
* `brKernel_chapmanKolmogorov : ChapmanKolmogorov volume (brKernel D0)`:
  `∫⁻ w, q s a w * q u w b = q (s + u) a b` for `0 < s`, `0 < u` and **all** `a, b ∈ ℝ × ℝ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-!
### Chapman–Kolmogorov for the X factor, unconditional
-/

/-- **Chapman–Kolmogorov for the X factor at all points of the half-line**
(`mk_kernelX_chapmanKolmogorov` with `McKeanBackwardFacts` and `TimeMollifyDuality` supplied by
`mcKeanBackwardFacts_holds` and `timeMollifyDuality_holds`). -/
theorem br_mk_kernelX_chapmanKolmogorov {D0 : ℝ} (hD0 : 0 < D0) {s T : ℝ} (hs : 0 < s)
    (hsT : s < T) {x x'' : ℝ} (hx : 0 ≤ x) (hx'' : 0 ≤ x'') :
    ∫⁻ x', ENNReal.ofReal (mkKernelX D0 s x x') * ENNReal.ofReal (mkKernelX D0 (T - s) x' x'') =
      ENNReal.ofReal (mkKernelX D0 T x x'') :=
  mk_kernelX_chapmanKolmogorov hD0 (mcKeanBackwardFacts_holds D0 hD0)
    (timeMollifyDuality_holds D0 hD0) hs hsT hx hx''

/-!
### The adapter
-/

/-- **The source-indicator adapter** `q′_t(a, b) = 1_S(a) · ofReal (p_t(a, b))` of the base
kernel `p = exKernel D0`.
-/
def brKernel (D0 : ℝ) (t : ℝ) (a b : ℝ × ℝ) : ℝ≥0∞ :=
  exBaseStrip.indicator (fun a => ENNReal.ofReal (exKernel D0 t a b)) a

theorem measurableSet_exBaseStrip : MeasurableSet exBaseStrip :=
  measurableSet_Ici.prod measurableSet_Icc

theorem brKernel_of_mem {D0 t : ℝ} {a : ℝ × ℝ} (ha : a ∈ exBaseStrip) (b : ℝ × ℝ) :
    brKernel D0 t a b = ENNReal.ofReal (exKernel D0 t a b) := by
  simp [brKernel, ha]

theorem brKernel_of_notMem {D0 t : ℝ} {a : ℝ × ℝ} (ha : a ∉ exBaseStrip) (b : ℝ × ℝ) :
    brKernel D0 t a b = 0 := by
  simp [brKernel, ha]

/-- The product kernel vanishes at targets off the strip. -/
theorem exKernel_of_notMem_right {D0 t : ℝ} (a : ℝ × ℝ) {b : ℝ × ℝ} (hb : b ∉ exBaseStrip) :
    exKernel D0 t a b = 0 := by
  rw [exKernel_eq]
  by_cases h1 : 0 ≤ b.1
  · have h2 : b.2 ∉ Icc (0 : ℝ) 1 := fun h2 => hb ⟨h1, h2⟩
    rw [sk_kernelY_of_notMem_right _ h2, mul_zero]
  · simp [mkKernelX, h1]

/-- The product kernel vanishes at nonpositive times. -/
theorem exKernel_of_nonpos {D0 t : ℝ} (ht : t ≤ 0) (a b : ℝ × ℝ) : exKernel D0 t a b = 0 := by
  rw [exKernel_eq]
  simp [mkKernelX, not_lt.2 ht]

theorem brKernel_of_notMem_right {D0 t : ℝ} (a : ℝ × ℝ) {b : ℝ × ℝ} (hb : b ∉ exBaseStrip) :
    brKernel D0 t a b = 0 := by
  by_cases ha : a ∈ exBaseStrip
  · rw [brKernel_of_mem ha, exKernel_of_notMem_right a hb, ENNReal.ofReal_zero]
  · exact brKernel_of_notMem ha b

theorem brKernel_le_ofReal (D0 t : ℝ) (a b : ℝ × ℝ) :
    brKernel D0 t a b ≤ ENNReal.ofReal (exKernel D0 t a b) := by
  by_cases ha : a ∈ exBaseStrip
  · rw [brKernel_of_mem ha]
  · rw [brKernel_of_notMem ha]
    exact zero_le

theorem brKernel_ne_top (D0 t : ℝ) (a b : ℝ × ℝ) : brKernel D0 t a b ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (brKernel_le_ofReal D0 t a b)

/-- `exKernel` is symmetric on the strip. -/
theorem exKernel_symm {D0 t : ℝ} {a b : ℝ × ℝ} (ha : a ∈ exBaseStrip) (hb : b ∈ exBaseStrip) :
    exKernel D0 t a b = exKernel D0 t b a := by
  rw [exKernel_eq, exKernel_eq, mk_kernelX_comm ha.1 hb.1, sk_kernelY_symm]

/-- **The adapter is symmetric at all points.** -/
theorem brKernel_symm (D0 t : ℝ) (a b : ℝ × ℝ) : brKernel D0 t a b = brKernel D0 t b a := by
  by_cases ha : a ∈ exBaseStrip <;> by_cases hb : b ∈ exBaseStrip
  · rw [brKernel_of_mem ha, brKernel_of_mem hb, exKernel_symm ha hb]
  · rw [brKernel_of_notMem_right a hb, brKernel_of_notMem hb]
  · rw [brKernel_of_notMem ha, brKernel_of_notMem_right b ha]
  · rw [brKernel_of_notMem ha, brKernel_of_notMem hb]

/-- **Joint measurability** of the adapter in the two space variables. -/
theorem measurable_brKernel {D0 : ℝ} (hD0 : 0 < D0) (t : ℝ) :
    Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => brKernel D0 t p.1 p.2 := by
  have e : (fun p : (ℝ × ℝ) × (ℝ × ℝ) => brKernel D0 t p.1 p.2) =
      (Prod.fst ⁻¹' exBaseStrip).indicator
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (exKernel D0 t p.1 p.2)) := by
    funext p
    by_cases hp : p.1 ∈ exBaseStrip
    · rw [brKernel_of_mem hp, indicator_of_mem (show p ∈ Prod.fst ⁻¹' exBaseStrip from hp)]
    · rw [brKernel_of_notMem hp,
        indicator_of_notMem (show p ∉ Prod.fst ⁻¹' exBaseStrip from hp)]
  rw [e]
  refine Measurable.indicator ?_ (measurable_fst measurableSet_exBaseStrip)
  exact ((exKernel_measurable hD0).comp
    (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => (t, p.1, p.2)) (by fun_prop)).ennreal_ofReal

theorem measurable_brKernel_right {D0 : ℝ} (hD0 : 0 < D0) (t : ℝ) (a : ℝ × ℝ) :
    Measurable fun b => brKernel D0 t a b :=
  (measurable_brKernel hD0 t).comp (measurable_const.prodMk measurable_id)

theorem measurable_brKernel_left {D0 : ℝ} (hD0 : 0 < D0) (t : ℝ) (b : ℝ × ℝ) :
    Measurable fun a => brKernel D0 t a b :=
  (measurable_brKernel hD0 t).comp (measurable_id.prodMk measurable_const)

/-!
### Chapman–Kolmogorov at all points
-/

/-- Chapman–Kolmogorov for the X factor in the form needed below: for `0 < s`, `0 < u`, `x ≥ 0` and
**all** `x''`. -/
theorem br_mk_ck_all {D0 : ℝ} (hD0 : 0 < D0) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) {x : ℝ}
    (hx : 0 ≤ x) (x'' : ℝ) :
    ∫⁻ x', ENNReal.ofReal (mkKernelX D0 s x x') * ENNReal.ofReal (mkKernelX D0 u x' x'') =
      ENNReal.ofReal (mkKernelX D0 (s + u) x x'') := by
  by_cases hx'' : 0 ≤ x''
  · have h := br_mk_kernelX_chapmanKolmogorov hD0 hs (show s < s + u by linarith) hx hx''
    rwa [show s + u - s = u by ring] at h
  · simp [mkKernelX, hx'']

/-- **Chapman–Kolmogorov for the adapter at all points**, in the form `ChapmanKolmogorov`. -/
theorem brKernel_chapmanKolmogorov {D0 : ℝ} (hD0 : 0 < D0) :
    ChapmanKolmogorov volume (brKernel D0) := by
  intro s u hs hu a b
  by_cases ha : a ∈ exBaseStrip
  · have hint : ∀ w : ℝ × ℝ, brKernel D0 s a w * brKernel D0 u w b =
        (ENNReal.ofReal (mkKernelX D0 s a.1 w.1) * ENNReal.ofReal (mkKernelX D0 u w.1 b.1)) *
          (ENNReal.ofReal (skKernelY D0 s a.2 w.2) *
            ENNReal.ofReal (skKernelY D0 u w.2 b.2)) := by
      intro w
      rw [brKernel_of_mem ha]
      by_cases hw : w ∈ exBaseStrip
      · rw [brKernel_of_mem hw, exKernel_eq, exKernel_eq,
          ENNReal.ofReal_mul (mk_kernelX_nonneg hD0 _ _ _),
          ENNReal.ofReal_mul (mk_kernelX_nonneg hD0 _ _ _)]
        ring
      · rw [brKernel_of_notMem hw, mul_zero]
        by_cases hw1 : 0 ≤ w.1
        · have hw2 : w.2 ∉ Icc (0 : ℝ) 1 := fun h2 => hw ⟨hw1, h2⟩
          simp [sk_kernelY_of_notMem_right _ hw2]
        · simp [mkKernelX, hw1]
    simp_rw [hint]
    have hX : Measurable fun x' : ℝ =>
        ENNReal.ofReal (mkKernelX D0 s a.1 x') * ENNReal.ofReal (mkKernelX D0 u x' b.1) :=
      (mk_kernelX_measurable_snd D0 s a.1).ennreal_ofReal.mul
        ((mk_kernelX_measurable D0).comp (f := fun x' : ℝ => (u, x', b.1))
          (by fun_prop)).ennreal_ofReal
    have hY : Measurable fun y' : ℝ =>
        ENNReal.ofReal (skKernelY D0 s a.2 y') * ENNReal.ofReal (skKernelY D0 u y' b.2) :=
      (sk_kernelY_measurable_right hD0 s a.2).ennreal_ofReal.mul
        (sk_kernelY_measurable_left hD0 u b.2).ennreal_ofReal
    rw [Measure.volume_eq_prod, lintegral_prod_mul hX.aemeasurable hY.aemeasurable,
      br_mk_ck_all hD0 hs hu ha.1, sk_kernelY_chapmanKolmogorov hD0 s u hs hu a.2 b.2,
      brKernel_of_mem ha, exKernel_eq, ENNReal.ofReal_mul (mk_kernelX_nonneg hD0 _ _ _)]
  · simp [brKernel_of_notMem ha]

end BlockBand.Diffusion
