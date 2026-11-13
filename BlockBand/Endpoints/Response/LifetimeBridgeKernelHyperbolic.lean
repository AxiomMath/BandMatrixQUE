module

public import BlockBand.Endpoints.Response.LifetimeBridgeDefs
public import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# The hyperbolic radial factor `pX` of the base heat kernel

For `D₀ > 0` this file proves `lbk_sdivSinh_continuous` (`s / sinh s` extended by `1`),
`lbk_mcKeanG_le` (the integrable majorant `2e^T/(1+v²)`), `lbk_hypKernel_continuous`,
`lbk_hypKernel_pos`, `lbk_hypRadial_continuous` (continuity in `x'` on all of `ℝ`),
`lbk_kernelX_nonneg`, `lbk_kernelX_continuousOn` (on `[0, ∞)`), `lbk_kernelX_zero_pos`
(`pX_t(x, 0) = 4π K_T(r) > 0`: the pole value is strictly positive) and `lbk_kernelX_measurable`
(joint measurability in `(t, x, x')`).

That McKean's function is the heat kernel (mass one, backward/forward heat equation,
Chapman–Kolmogorov) is not shown in this file; it is part of the transition law
`LbkBaseTransitionLaw`, proved as `lbkBaseTransitionLaw_holds`.
Only `∫ pX = 1` is used, and it is derived from the transition law and the sphere normalisation.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

/-!
### `s / sinh s`
-/

/-- `s / sinh s`, continuously extended by `1` at `s = 0`. -/
def lbkSdivSinh (s : ℝ) : ℝ := if s = 0 then 1 else s / Real.sinh s

theorem lbk_sdivSinh_continuous : Continuous lbkSdivSinh := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s = 0
  · subst hs
    rw [← continuousWithinAt_compl_self]
    have hd : Tendsto (fun t => t⁻¹ • (Real.sinh (0 + t) - Real.sinh 0)) (𝓝[≠] 0)
        (𝓝 (Real.cosh 0)) := hasDerivAt_iff_tendsto_slope_zero.1 (Real.hasDerivAt_sinh 0)
    simp only [zero_add, Real.sinh_zero, sub_zero, smul_eq_mul, Real.cosh_zero] at hd
    have hinv := hd.inv₀ one_ne_zero
    rw [inv_one] at hinv
    show Tendsto lbkSdivSinh (𝓝[≠] 0) (𝓝 (lbkSdivSinh 0))
    rw [show lbkSdivSinh 0 = 1 by simp [lbkSdivSinh]]
    refine hinv.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have ht' : t ≠ 0 := ht
    simp only [lbkSdivSinh, ht', ↓reduceIte]
    rw [mul_inv, inv_inv, div_eq_mul_inv]
  · have hsh : Real.sinh s ≠ 0 := fun h => hs (Real.sinh_eq_zero.1 h)
    refine (continuousAt_id.div Real.continuous_sinh.continuousAt hsh).congr ?_
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht
    have ht' : t ≠ 0 := ht
    simp [lbkSdivSinh, ht']

theorem lbk_sdivSinh_pos (s : ℝ) : 0 < lbkSdivSinh s := by
  unfold lbkSdivSinh
  split_ifs with hs
  · exact one_pos
  · rcases lt_or_gt_of_ne hs with h | h
    · exact div_pos_of_neg_of_neg h (Real.sinh_neg_iff.2 h)
    · exact div_pos h (Real.sinh_pos_iff.2 h)

theorem lbk_sdivSinh_le_one (s : ℝ) : lbkSdivSinh s ≤ 1 := by
  unfold lbkSdivSinh
  split_ifs with hs
  · exact le_rfl
  · rcases lt_or_gt_of_ne hs with h | h
    · exact (div_le_one_of_neg (Real.sinh_neg_iff.2 h)).2 (Real.sinh_le_self_iff.2 h.le)
    · exact (div_le_one (Real.sinh_pos_iff.2 h)).2 (Real.self_le_sinh_iff.2 h.le)

/-!
### McKean's kernel
-/

/-- McKean's integrand after the substitution `cosh s = w`:
`G_T(w) = 2 (s / sinh s) e^{-s²/(4T)}`, `s = arcosh w`. -/
def lbkMcKeanG (T w : ℝ) : ℝ :=
  2 * lbkSdivSinh (Real.arcosh w) * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T))

/-- McKean's heat kernel of `e^{TΔ}` on `H²` as a function of `c = cosh ρ`:
`K_T = √2 e^{-T/4}(4πT)^{-3/2} ∫_0^∞ G_T(c + v²) dv` (with `c` clamped at `1`). -/
def lbkHypKernel (T c : ℝ) : ℝ :=
  Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T) ^ (3 / 2 : ℝ) *
    ∫ v in Ioi (0 : ℝ), lbkMcKeanG T (max c 1 + v ^ 2)

/-- The hyperbolic law of cosines in the coordinates `x = (cosh r - 1)/2`:
`cosh d = (1+2x)(1+2x') - 4√(x(1+x)x'(1+x')) cos φ`. -/
def lbkHypCos (x x' φ : ℝ) : ℝ :=
  (1 + 2 * x) * (1 + 2 * x') - 4 * Real.sqrt (x * (1 + x) * (x' * (1 + x'))) * Real.cos φ

/-- The angle-averaged kernel: the density relative to `dx'` of the radial coordinate at time
`T` (for `e^{TΔ}`) started from `x`: `2 ∫_0^{2π} K_T(cosh d) dφ`. -/
def lbkHypRadial (T x x' : ℝ) : ℝ :=
  2 * ∫ φ in (0 : ℝ)..(2 * π), lbkHypKernel T (lbkHypCos x x' φ)

/-- The hyperbolic radial heat kernel `pX_t(x, x')` of the generator
`(D₀/2)[x(1+x)∂²_x + (1+2x)∂_x]`: `lbkHypRadial (D₀t/2) x x'` for `t > 0`, `x' ≥ 0`, else `0`. -/
def lbkKernelX (D0 : ℝ) (t x x' : ℝ) : ℝ :=
  if 0 < t ∧ 0 ≤ x' then lbkHypRadial (D0 * t / 2) x x' else 0

theorem lbk_mcKeanG_pos (T w : ℝ) : 0 < lbkMcKeanG T w := by
  unfold lbkMcKeanG
  have := lbk_sdivSinh_pos (Real.arcosh w)
  positivity

theorem lbk_mcKeanG_le {T w v : ℝ} (hT : 0 < T) (hw : 1 + v ^ 2 ≤ w) :
    lbkMcKeanG T w ≤ 2 * Real.exp T * (1 + v ^ 2)⁻¹ := by
  have hv : (0 : ℝ) < 1 + v ^ 2 := by positivity
  have hw0 : 0 < w := lt_of_lt_of_le hv hw
  have hw1 : 1 ≤ w := le_trans (by nlinarith [sq_nonneg v]) hw
  have ha : Real.log (1 + v ^ 2) ≤ Real.arcosh w := by
    refine (Real.log_le_log hv hw).trans ?_
    rw [Real.log_le_iff_le_exp hw0, Real.exp_arcosh hw1]
    linarith [Real.sqrt_nonneg (w ^ 2 - 1)]
  have hexp : Real.exp (-(Real.arcosh w) ^ 2 / (4 * T)) ≤ Real.exp T * (1 + v ^ 2)⁻¹ := by
    have hinv : (1 + v ^ 2)⁻¹ = Real.exp (-Real.log (1 + v ^ 2)) := by
      rw [Real.exp_neg, Real.exp_log hv]
    rw [hinv, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h4 : Real.arcosh w ≤ (Real.arcosh w) ^ 2 / (4 * T) + T := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (Real.arcosh w - 2 * T)]
    have : -(Real.arcosh w) ^ 2 / (4 * T) = -((Real.arcosh w) ^ 2 / (4 * T)) := by ring
    linarith
  have hσ0 := (lbk_sdivSinh_pos (Real.arcosh w)).le
  have hσ1 := lbk_sdivSinh_le_one (Real.arcosh w)
  unfold lbkMcKeanG
  calc 2 * lbkSdivSinh (Real.arcosh w) * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T))
      ≤ 2 * 1 * (Real.exp T * (1 + v ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

theorem lbk_arc_continuous : Continuous fun p : ℝ × ℝ => Real.arcosh (max p.1 1 + p.2 ^ 2) :=
  Real.continuousOn_arcosh.comp_continuous (by fun_prop) fun p => by
    simp only [mem_Ici]
    nlinarith [le_max_right p.1 1, sq_nonneg p.2]

theorem lbk_G_continuous (T : ℝ) :
    Continuous fun p : ℝ × ℝ => lbkMcKeanG T (max p.1 1 + p.2 ^ 2) := by
  unfold lbkMcKeanG
  have h := lbk_arc_continuous
  exact (continuous_const.mul (lbk_sdivSinh_continuous.comp h)).mul
    (Real.continuous_exp.comp ((h.pow 2).neg.div_const _))

theorem lbk_G_le {T : ℝ} (hT : 0 < T) (c v : ℝ) :
    ‖lbkMcKeanG T (max c 1 + v ^ 2)‖ ≤ 2 * Real.exp T * (1 + v ^ 2)⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_pos (lbk_mcKeanG_pos _ _)]
  exact lbk_mcKeanG_le hT (by linarith [le_max_right c 1])

theorem lbk_integrableOn_G {T : ℝ} (hT : 0 < T) (c : ℝ) :
    IntegrableOn (fun v => lbkMcKeanG T (max c 1 + v ^ 2)) (Ioi 0) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * Real.exp T)).integrableOn
    ((lbk_G_continuous T).comp (continuous_const.prodMk continuous_id :
      Continuous fun v : ℝ => (c, v))).aestronglyMeasurable (ae_of_all _ fun v => lbk_G_le hT c v)

theorem lbk_hypKernel_continuous {T : ℝ} (hT : 0 < T) : Continuous (lbkHypKernel T) := by
  unfold lbkHypKernel
  refine continuous_const.mul ?_
  refine continuous_of_dominated (bound := fun v => 2 * Real.exp T * (1 + v ^ 2)⁻¹)
    (fun c => ?_) (fun c => ae_of_all _ fun v => lbk_G_le hT c v)
    (integrable_inv_one_add_sq.const_mul _).integrableOn
    (ae_of_all _ fun v => (lbk_G_continuous T).comp (continuous_id.prodMk continuous_const :
      Continuous fun c : ℝ => (c, v)))
  exact ((lbk_G_continuous T).comp (continuous_const.prodMk continuous_id :
    Continuous fun v : ℝ => (c, v))).aestronglyMeasurable

theorem lbk_hypKernel_pos {T : ℝ} (hT : 0 < T) (c : ℝ) : 0 < lbkHypKernel T c := by
  unfold lbkHypKernel
  have hb : 0 < 4 * π * T := mul_pos (mul_pos (by norm_num) Real.pi_pos) hT
  have h1 : 0 < Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T) ^ (3 / 2 : ℝ) := by
    have := Real.rpow_pos_of_pos hb (3 / 2 : ℝ)
    positivity
  refine mul_pos h1 ?_
  rw [integral_pos_iff_support_of_nonneg (fun v => (lbk_mcKeanG_pos _ _).le)
    (lbk_integrableOn_G hT c)]
  have : Function.support (fun v => lbkMcKeanG T (max c 1 + v ^ 2)) = univ := by
    ext v
    simp [(lbk_mcKeanG_pos T _).ne']
  rw [this]
  simp

/-!
### The radial kernel
-/

theorem lbk_hypCos_zero (x φ : ℝ) : lbkHypCos x 0 φ = 1 + 2 * x := by
  simp [lbkHypCos]

theorem lbk_hypRadial_continuous {T : ℝ} (hT : 0 < T) (x : ℝ) : Continuous (lbkHypRadial T x) := by
  unfold lbkHypRadial
  refine continuous_const.mul ?_
  have hc : Continuous fun p : ℝ × ℝ => lbkHypCos x p.1 p.2 := by unfold lbkHypCos; fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun x' φ => lbkHypKernel T (lbkHypCos x x' φ)) ((lbk_hypKernel_continuous hT).comp hc)
    continuous_const

theorem lbk_hypRadial_nonneg {T : ℝ} (hT : 0 < T) (x x' : ℝ) : 0 ≤ lbkHypRadial T x x' := by
  unfold lbkHypRadial
  have := intervalIntegral.integral_nonneg (μ := volume) (a := 0) (b := 2 * π) (by positivity)
    (fun φ _ => (lbk_hypKernel_pos hT (lbkHypCos x x' φ)).le)
  positivity

theorem lbk_hypRadial_zero_pos {T : ℝ} (hT : 0 < T) (x : ℝ) : 0 < lbkHypRadial T x 0 := by
  unfold lbkHypRadial
  simp only [lbk_hypCos_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have := lbk_hypKernel_pos hT (1 + 2 * x)
  have := Real.pi_pos
  positivity

theorem lbk_hypKernel_measurable : Measurable fun p : ℝ × ℝ => lbkHypKernel p.1 p.2 := by
  unfold lbkHypKernel
  refine Measurable.mul (by fun_prop) ?_
  have h : Measurable fun q : (ℝ × ℝ) × ℝ => Real.arcosh (max q.1.2 1 + q.2 ^ 2) :=
    lbk_arc_continuous.measurable.comp (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => (q.1.2, q.2))
  have hm : StronglyMeasurable (Function.uncurry fun (p : ℝ × ℝ) (v : ℝ) =>
      lbkMcKeanG p.1 (max p.2 1 + v ^ 2)) := by
    apply Measurable.stronglyMeasurable
    unfold lbkMcKeanG
    exact (measurable_const.mul (lbk_sdivSinh_continuous.measurable.comp h)).mul
      (Real.measurable_exp.comp ((h.pow_const 2).neg.div
        (measurable_const.mul (measurable_fst.comp measurable_fst))))
  exact (hm.integral_prod_right (ν := volume.restrict (Ioi 0))).measurable

theorem lbk_hypRadial_measurable :
    Measurable fun w : ℝ × ℝ × ℝ => lbkHypRadial w.1 w.2.1 w.2.2 := by
  unfold lbkHypRadial
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  refine measurable_const.mul ?_
  have hc : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => (q.1.1, lbkHypCos q.1.2.1 q.1.2.2 q.2) := by
    unfold lbkHypCos; fun_prop
  have hm : StronglyMeasurable (Function.uncurry fun (w : ℝ × ℝ × ℝ) (φ : ℝ) =>
      lbkHypKernel w.1 (lbkHypCos w.2.1 w.2.2 φ)) :=
    (lbk_hypKernel_measurable.comp hc).stronglyMeasurable
  exact (hm.integral_prod_right (ν := volume.restrict (Ioc 0 (2 * π)))).measurable

/-!
### The factor `pX`
-/

theorem lbk_kernelX_nonneg {D0 : ℝ} (hD0 : 0 < D0) (t x x' : ℝ) : 0 ≤ lbkKernelX D0 t x x' := by
  unfold lbkKernelX
  split_ifs with h
  · exact lbk_hypRadial_nonneg (by have := h.1; positivity) x x'
  · exact le_rfl

theorem lbk_kernelX_eq {D0 t x x' : ℝ} (ht : 0 < t) (hx' : 0 ≤ x') :
    lbkKernelX D0 t x x' = lbkHypRadial (D0 * t / 2) x x' := by
  simp [lbkKernelX, ht, hx']

theorem lbk_kernelX_continuousOn {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (x : ℝ) :
    ContinuousOn (lbkKernelX D0 t x) (Ici 0) :=
  (lbk_hypRadial_continuous (by positivity) x).continuousOn.congr fun _ hx' =>
    lbk_kernelX_eq ht hx'

theorem lbk_kernelX_zero_pos {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (x : ℝ) :
    0 < lbkKernelX D0 t x 0 := by
  rw [lbk_kernelX_eq ht le_rfl]
  exact lbk_hypRadial_zero_pos (by positivity) x

theorem lbk_kernelX_measurable (D0 : ℝ) :
    Measurable fun w : ℝ × ℝ × ℝ => lbkKernelX D0 w.1 w.2.1 w.2.2 := by
  have h1 : MeasurableSet {w : ℝ × ℝ × ℝ | 0 < w.1} :=
    measurableSet_lt measurable_const (by fun_prop : Measurable fun w : ℝ × ℝ × ℝ => w.1)
  have h2 : MeasurableSet {w : ℝ × ℝ × ℝ | 0 ≤ w.2.2} :=
    measurableSet_le measurable_const (by fun_prop : Measurable fun w : ℝ × ℝ × ℝ => w.2.2)
  have hS : MeasurableSet {w : ℝ × ℝ × ℝ | 0 < w.1 ∧ 0 ≤ w.2.2} := h1.inter h2
  have h : Measurable fun w : ℝ × ℝ × ℝ => lbkHypRadial (D0 * w.1 / 2) w.2.1 w.2.2 :=
    lbk_hypRadial_measurable.comp (f := fun w : ℝ × ℝ × ℝ => (D0 * w.1 / 2, w.2.1, w.2.2))
      (by fun_prop)
  have h' : Measurable fun w : ℝ × ℝ × ℝ =>
      if 0 < w.1 ∧ 0 ≤ w.2.2 then lbkHypRadial (D0 * w.1 / 2) w.2.1 w.2.2 else 0 :=
    Measurable.ite hS h measurable_const
  exact h'

end BlockBand.Endpoints
