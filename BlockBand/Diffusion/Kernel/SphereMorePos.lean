module

public import BlockBand.Diffusion.Kernel.SphereMoreAnalytic
public import BlockBand.Diffusion.Kernel.SphereCK

/-!
# Strict positivity and `lintegral` normalisation of the sphere factor

We prove that the sphere factor `pY` is strictly positive on `[0,1]²` for `t > 0` and that it is
a probability density in `y'`. For `D₀ > 0`:
* `sk_kernelY_pos`: `0 < pY_t(y, y')` for `t > 0`, `y, y' ∈ [0,1]`;
  `sk_kernelY_corner_pos`: in particular `0 < pY_t(y, 0)`;
* `sk_kernelY_pos_iff`: `0 < pY_t(y, y') ↔ t > 0 ∧ y, y' ∈ [0,1]` (all real arguments);
* `sk_integrable_kernelY`: `pY_t(y, ·)` is Lebesgue integrable for every `t`, `y`;
* `sk_lintegral_kernelY_one`: `∫⁻ y', ofReal (pY_t(y, y')) = 1` for `t > 0`, `y ∈ [0,1]`;
  `sk_lintegral_kernelY_Icc`: the same over `y' ∈ [0,1]`;
  `sk_lintegral_kernelY_compl`: the mass off `[0,1]` is `0`;
* `sk_lintegral_kernelY_of_not`: `∫⁻ y', ofReal (pY_t(y, y')) = 0` if `t ≤ 0` or `y ∉ [0,1]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Polynomial
open scoped ENNReal

/-!
### Strict positivity of the Legendre series
-/

/-- Strict positivity of the spherical heat kernel series on `[0,1]²` for `t > 0`, including the
poles `y' ∈ {0, 1}`. -/
def SkSphereKernelPos (D0 : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ y ∈ Icc (0 : ℝ) 1, ∀ y' ∈ Icc (0 : ℝ) 1, 0 < skSphereSeries D0 t y y'

/-- **Strict positivity of the spherical heat kernel on `[0,1]²`**, from Chapman–Kolmogorov,
nonnegativity and unique continuation. -/
theorem skSphereKernelPos_holds (D0 : ℝ) (hD0 : 0 < D0) : SkSphereKernelPos D0 := by
  intro t ht y hy y' hy'
  have ht2 : 0 < t / 2 := by positivity
  have hCK := skp_chapman hD0 ht2 ht2 hy hy'
  rw [add_halves] at hCK
  rw [hCK]
  set f := skSphereSeries D0 (t / 2) y with hfdef
  set g := skSphereSeries D0 (t / 2) y' with hgdef
  have hfc : ContinuousOn f (Icc 0 1) := sk_sphereSeries_continuousOn hD0 ht2 hy
  have hgc : ContinuousOn g (Icc 0 1) := sk_sphereSeries_continuousOn hD0 ht2 hy'
  have hsym : (fun w => f w * skSphereSeries D0 (t / 2) w y') = fun w => f w * g w := by
    funext w; rw [skp_series_symm D0 (t / 2) w y']
  rw [hsym]
  have hnn : ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ f w * g w := fun w hw =>
    mul_nonneg (skp_series_nonneg hD0 ht2 hy hw) (skp_series_nonneg hD0 ht2 hy' hw)
  have hI0 : 0 ≤ ∫ w in (0 : ℝ)..1, f w * g w :=
    intervalIntegral.integral_nonneg zero_le_one hnn
  by_contra hle
  have h0 : ∫ w in (0 : ℝ)..1, f w * g w = 0 := le_antisymm (not_lt.1 hle) hI0
  have hfg := skp_eq_zero_of_integral_eq_zero (hfc.mul hgc) hnn h0
  have hf1 := skp_integral_series_one hD0 ht2 hy
  have hg1 := skp_integral_series_one hD0 ht2 hy'
  have hzero_int : ∀ h : ℝ → ℝ, (∀ w ∈ Icc (0 : ℝ) 1, h w = 0) →
      ∫ w in (0 : ℝ)..1, h w = 0 := by
    intro h hh
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun w hw => by
      rw [uIcc_of_le zero_le_one] at hw; exact hh w hw]
    simp
  obtain ⟨w0, hw0, hfw0⟩ : ∃ w0 ∈ Icc (0 : ℝ) 1, f w0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hzero_int f hcon
    rw [hfdef] at this
    linarith
  obtain ⟨c, d, hc0, hcd, hd1, hcdf⟩ :=
    skp_exists_Icc_sub hfc hw0 isOpen_compl_singleton (mem_compl_singleton_iff.2 hfw0)
  have hgz : ∀ w ∈ Icc c d, g w = 0 := fun w hw =>
    (mul_eq_zero.1 (hfg w ⟨hc0.trans hw.1, hw.2.trans hd1⟩)).resolve_left
      (mem_compl_singleton_iff.1 (hcdf w hw))
  have hg0 := skp_series_unique_continuation hD0 ht2 hy' hc0 hcd hd1 hgz
  have := hzero_int g hg0
  rw [hgdef] at this
  linarith

/-!
### Strict positivity of `skKernelY`
-/

/-- **Strict positivity**: `0 < pY_t(y, y')` for `t > 0`, `y, y' ∈ [0,1]`. -/
theorem sk_kernelY_pos {D0 t y y' : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hy : y ∈ Icc (0 : ℝ) 1)
    (hy' : y' ∈ Icc (0 : ℝ) 1) : 0 < skKernelY D0 t y y' := by
  rw [sk_kernelY_eq ht hy hy']
  exact skSphereKernelPos_holds D0 hD0 t ht y hy y' hy'

/-- **Corner positivity**: `0 < pY_t(y, 0)` for `t > 0`, `y ∈ [0,1]`. -/
theorem sk_kernelY_corner_pos {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 < skKernelY D0 t y 0 :=
  sk_kernelY_pos hD0 ht hy ⟨le_rfl, zero_le_one⟩

/-- `0 < pY_t(y, y')` exactly when `t > 0` and `y, y' ∈ [0,1]` (all real arguments). -/
theorem sk_kernelY_pos_iff {D0 : ℝ} (hD0 : 0 < D0) (t y y' : ℝ) :
    0 < skKernelY D0 t y y' ↔ 0 < t ∧ y ∈ Icc (0 : ℝ) 1 ∧ y' ∈ Icc (0 : ℝ) 1 := by
  constructor
  · intro h
    by_contra hn
    have : skKernelY D0 t y y' = 0 := by simp only [skKernelY, hn, ↓reduceIte]
    linarith
  · exact fun h => sk_kernelY_pos hD0 h.1 h.2.1 h.2.2

/-!
### `lintegral` normalisation
-/

/-- `pY_t(y, ·)` is Lebesgue integrable, for all `t`, `y`. -/
theorem sk_integrable_kernelY {D0 : ℝ} (hD0 : 0 < D0) (t y : ℝ) :
    Integrable (skKernelY D0 t y) := by
  by_cases h : 0 < t ∧ y ∈ Icc (0 : ℝ) 1
  · rw [sk_kernelY_eq_indicator h.1 h.2]
    exact (sk_sphereSeries_continuousOn hD0 h.1 h.2).integrableOn_Icc.integrable_indicator
      measurableSet_Icc
  · have e : skKernelY D0 t y = fun _ => 0 := by
      funext y'
      simp only [skKernelY]
      rw [ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩]
    rw [e]
    exact integrable_zero _ _ _

/-- **Normalisation in `ℝ≥0∞`**: `∫⁻ y', ofReal (pY_t(y, y')) = 1` for `t > 0`,
`y ∈ [0,1]`. -/
theorem sk_lintegral_kernelY_one {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) : ∫⁻ y', ENNReal.ofReal (skKernelY D0 t y y') = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (sk_integrable_kernelY hD0 t y)
    (ae_of_all _ fun y' => sk_kernelY_nonneg hD0 t y y'), sk_integral_kernelY hD0 ht hy,
    ENNReal.ofReal_one]

/-- The mass of `pY_t(y, ·)` off `[0,1]` is `0` (all `t`, `y`). -/
theorem sk_lintegral_kernelY_compl (D0 t y : ℝ) :
    ∫⁻ y' in (Icc (0 : ℝ) 1)ᶜ, ENNReal.ofReal (skKernelY D0 t y y') = 0 := by
  rw [setLIntegral_congr_fun measurableSet_Icc.compl (g := fun _ => 0) fun y' hy' => by
    rw [sk_kernelY_of_notMem_right y hy', ENNReal.ofReal_zero]]
  exact lintegral_zero

/-- **Normalisation on `[0,1]`**: `∫⁻ y' in [0,1], ofReal (pY_t(y, y')) = 1` for `t > 0`,
`y ∈ [0,1]`. -/
theorem sk_lintegral_kernelY_Icc {D0 t y : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ∫⁻ y' in Icc (0 : ℝ) 1, ENNReal.ofReal (skKernelY D0 t y y') = 1 := by
  have h := lintegral_add_compl (μ := volume) (fun y' => ENNReal.ofReal (skKernelY D0 t y y'))
    (measurableSet_Icc (a := (0 : ℝ)) (b := 1))
  rw [sk_lintegral_kernelY_compl, add_zero, sk_lintegral_kernelY_one hD0 ht hy] at h
  exact h

/-- Zero mass for `t ≤ 0` or `y ∉ [0,1]` (where `skKernelY` vanishes identically). -/
theorem sk_lintegral_kernelY_of_not {D0 t y : ℝ} (h : ¬ (0 < t ∧ y ∈ Icc (0 : ℝ) 1)) :
    ∫⁻ y', ENNReal.ofReal (skKernelY D0 t y y') = 0 := by
  have e : (fun y' => ENNReal.ofReal (skKernelY D0 t y y')) = fun _ => 0 := by
    funext y'
    simp only [skKernelY]
    rw [ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩, ENNReal.ofReal_zero]
  rw [e, lintegral_zero]

end BlockBand.Diffusion
