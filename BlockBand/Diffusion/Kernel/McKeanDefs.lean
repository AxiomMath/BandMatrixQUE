module

public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# McKean's kernel and the radial factor `pX`

This file defines McKean's kernel
`K_T(c) = √2 e^{-T/4}(4πT)^{-3/2} ∫_0^∞ G_T(max c 1 + v²) dv`,
`G_T(w) = 2 (s/sinh s) e^{-s²/(4T)}`, `s = arcosh w`, and the radial factor
`mkKernelX D0 t x x' = 2 ∫_0^{2π} K_{D₀t/2}((1+2x)(1+2x') - 4√(x(1+x)x'(1+x')) cos φ) dφ` for
`t > 0`, `x' ≥ 0`, and `0` otherwise.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

/-!
### `s / sinh s`
-/

/-- `s / sinh s`, continuously extended by `1` at `s = 0`. -/
def mkSdivSinh (s : ℝ) : ℝ := if s = 0 then 1 else s / Real.sinh s

theorem mk_sdivSinh_continuous : Continuous mkSdivSinh := by
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
    show Tendsto mkSdivSinh (𝓝[≠] 0) (𝓝 (mkSdivSinh 0))
    rw [show mkSdivSinh 0 = 1 by simp [mkSdivSinh]]
    refine hinv.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have ht' : t ≠ 0 := ht
    simp only [mkSdivSinh, ht', ↓reduceIte]
    rw [mul_inv, inv_inv, div_eq_mul_inv]
  · have hsh : Real.sinh s ≠ 0 := fun h => hs (Real.sinh_eq_zero.1 h)
    refine (continuousAt_id.div Real.continuous_sinh.continuousAt hsh).congr ?_
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht
    have ht' : t ≠ 0 := ht
    simp [mkSdivSinh, ht']

theorem mk_sdivSinh_pos (s : ℝ) : 0 < mkSdivSinh s := by
  unfold mkSdivSinh
  split_ifs with hs
  · exact one_pos
  · rcases lt_or_gt_of_ne hs with h | h
    · exact div_pos_of_neg_of_neg h (Real.sinh_neg_iff.2 h)
    · exact div_pos h (Real.sinh_pos_iff.2 h)

theorem mk_sdivSinh_le_one (s : ℝ) : mkSdivSinh s ≤ 1 := by
  unfold mkSdivSinh
  split_ifs with hs
  · exact le_rfl
  · rcases lt_or_gt_of_ne hs with h | h
    · exact (div_le_one_of_neg (Real.sinh_neg_iff.2 h)).2 (Real.sinh_le_self_iff.2 h.le)
    · exact (div_le_one (Real.sinh_pos_iff.2 h)).2 (Real.self_le_sinh_iff.2 h.le)

/-!
### McKean's kernel
-/

/-- McKean's integrand after the substitution `cosh s = w`:
`G_T(w) = 2 (s / sinh s) e^{-s²/(4T)}`, `s = arcosh w`.
-/
def mkMcKeanG (T w : ℝ) : ℝ :=
  2 * mkSdivSinh (Real.arcosh w) * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T))

/-- **McKean's heat kernel of `e^{TΔ}` on `H²`** as a function of `c = cosh ρ`:
`K_T = √2 e^{-T/4}(4πT)^{-3/2} ∫_0^∞ G_T(c + v²) dv` (with `c` clamped at `1`).
-/
def mkHypKernel (T c : ℝ) : ℝ :=
  Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T) ^ (3 / 2 : ℝ) *
    ∫ v in Ioi (0 : ℝ), mkMcKeanG T (max c 1 + v ^ 2)

/-- The hyperbolic law of cosines in the coordinates `x = (cosh r - 1)/2`:
`cosh d = (1+2x)(1+2x') - 4√(x(1+x)x'(1+x')) cos φ`.
-/
def mkHypCos (x x' φ : ℝ) : ℝ :=
  (1 + 2 * x) * (1 + 2 * x') - 4 * Real.sqrt (x * (1 + x) * (x' * (1 + x'))) * Real.cos φ

/-- The angle-averaged kernel: the density relative to `dx'` of the radial coordinate at time
`T` (for `e^{TΔ}`) started from `x`:
`2 ∫_0^{2π} K_T(cosh d) dφ`.
-/
def mkHypRadial (T x x' : ℝ) : ℝ :=
  2 * ∫ φ in (0 : ℝ)..(2 * π), mkHypKernel T (mkHypCos x x' φ)

/-- **The hyperbolic radial heat kernel** `pX_t(x, x')` of the generator
`(D₀/2)[x(1+x)∂²_x + (1+2x)∂_x]`:
`mkHypRadial (D₀t/2) x x'` for `t > 0`, `x' ≥ 0`, else `0`.
-/
def mkKernelX (D0 : ℝ) (t x x' : ℝ) : ℝ :=
  if 0 < t ∧ 0 ≤ x' then mkHypRadial (D0 * t / 2) x x' else 0

theorem mk_mcKeanG_pos (T w : ℝ) : 0 < mkMcKeanG T w := by
  unfold mkMcKeanG
  have := mk_sdivSinh_pos (Real.arcosh w)
  positivity

theorem mk_mcKeanG_le {T w v : ℝ} (hT : 0 < T) (hw : 1 + v ^ 2 ≤ w) :
    mkMcKeanG T w ≤ 2 * Real.exp T * (1 + v ^ 2)⁻¹ := by
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
  have hσ0 := (mk_sdivSinh_pos (Real.arcosh w)).le
  have hσ1 := mk_sdivSinh_le_one (Real.arcosh w)
  unfold mkMcKeanG
  calc 2 * mkSdivSinh (Real.arcosh w) * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T))
      ≤ 2 * 1 * (Real.exp T * (1 + v ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

theorem mk_arc_continuous : Continuous fun p : ℝ × ℝ => Real.arcosh (max p.1 1 + p.2 ^ 2) :=
  Real.continuousOn_arcosh.comp_continuous (by fun_prop) fun p => by
    simp only [mem_Ici]
    nlinarith [le_max_right p.1 1, sq_nonneg p.2]

theorem mk_G_continuous (T : ℝ) :
    Continuous fun p : ℝ × ℝ => mkMcKeanG T (max p.1 1 + p.2 ^ 2) := by
  unfold mkMcKeanG
  have h := mk_arc_continuous
  exact (continuous_const.mul (mk_sdivSinh_continuous.comp h)).mul
    (Real.continuous_exp.comp ((h.pow 2).neg.div_const _))

theorem mk_G_le {T : ℝ} (hT : 0 < T) (c v : ℝ) :
    ‖mkMcKeanG T (max c 1 + v ^ 2)‖ ≤ 2 * Real.exp T * (1 + v ^ 2)⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_pos (mk_mcKeanG_pos _ _)]
  exact mk_mcKeanG_le hT (by linarith [le_max_right c 1])

theorem mk_integrableOn_G {T : ℝ} (hT : 0 < T) (c : ℝ) :
    IntegrableOn (fun v => mkMcKeanG T (max c 1 + v ^ 2)) (Ioi 0) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * Real.exp T)).integrableOn
    ((mk_G_continuous T).comp (continuous_const.prodMk continuous_id :
      Continuous fun v : ℝ => (c, v))).aestronglyMeasurable (ae_of_all _ fun v => mk_G_le hT c v)

theorem mk_hypKernel_continuous {T : ℝ} (hT : 0 < T) : Continuous (mkHypKernel T) := by
  unfold mkHypKernel
  refine continuous_const.mul ?_
  refine continuous_of_dominated (bound := fun v => 2 * Real.exp T * (1 + v ^ 2)⁻¹)
    (fun c => ?_) (fun c => ae_of_all _ fun v => mk_G_le hT c v)
    (integrable_inv_one_add_sq.const_mul _).integrableOn
    (ae_of_all _ fun v => (mk_G_continuous T).comp (continuous_id.prodMk continuous_const :
      Continuous fun c : ℝ => (c, v)))
  exact ((mk_G_continuous T).comp (continuous_const.prodMk continuous_id :
    Continuous fun v : ℝ => (c, v))).aestronglyMeasurable

theorem mk_hypKernel_pos {T : ℝ} (hT : 0 < T) (c : ℝ) : 0 < mkHypKernel T c := by
  unfold mkHypKernel
  have hb : 0 < 4 * π * T := mul_pos (mul_pos (by norm_num) Real.pi_pos) hT
  have h1 : 0 < Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T) ^ (3 / 2 : ℝ) := by
    have := Real.rpow_pos_of_pos hb (3 / 2 : ℝ)
    positivity
  refine mul_pos h1 ?_
  rw [integral_pos_iff_support_of_nonneg (fun v => (mk_mcKeanG_pos _ _).le)
    (mk_integrableOn_G hT c)]
  have : Function.support (fun v => mkMcKeanG T (max c 1 + v ^ 2)) = univ := by
    ext v
    simp [(mk_mcKeanG_pos T _).ne']
  rw [this]
  simp

/-!
### The radial kernel
-/

theorem mk_hypCos_zero (x φ : ℝ) : mkHypCos x 0 φ = 1 + 2 * x := by
  simp [mkHypCos]

theorem mk_hypRadial_continuous {T : ℝ} (hT : 0 < T) (x : ℝ) : Continuous (mkHypRadial T x) := by
  unfold mkHypRadial
  refine continuous_const.mul ?_
  have hc : Continuous fun p : ℝ × ℝ => mkHypCos x p.1 p.2 := by unfold mkHypCos; fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun x' φ => mkHypKernel T (mkHypCos x x' φ)) ((mk_hypKernel_continuous hT).comp hc)
    continuous_const

theorem mk_hypRadial_nonneg {T : ℝ} (hT : 0 < T) (x x' : ℝ) : 0 ≤ mkHypRadial T x x' := by
  unfold mkHypRadial
  have := intervalIntegral.integral_nonneg (μ := volume) (a := 0) (b := 2 * π) (by positivity)
    (fun φ _ => (mk_hypKernel_pos hT (mkHypCos x x' φ)).le)
  positivity

theorem mk_hypRadial_zero_pos {T : ℝ} (hT : 0 < T) (x : ℝ) : 0 < mkHypRadial T x 0 := by
  unfold mkHypRadial
  simp only [mk_hypCos_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have := mk_hypKernel_pos hT (1 + 2 * x)
  have := Real.pi_pos
  positivity

theorem mk_hypKernel_measurable : Measurable fun p : ℝ × ℝ => mkHypKernel p.1 p.2 := by
  unfold mkHypKernel
  refine Measurable.mul (by fun_prop) ?_
  have h : Measurable fun q : (ℝ × ℝ) × ℝ => Real.arcosh (max q.1.2 1 + q.2 ^ 2) :=
    mk_arc_continuous.measurable.comp (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => (q.1.2, q.2))
  have hm : StronglyMeasurable (Function.uncurry fun (p : ℝ × ℝ) (v : ℝ) =>
      mkMcKeanG p.1 (max p.2 1 + v ^ 2)) := by
    apply Measurable.stronglyMeasurable
    unfold mkMcKeanG
    exact (measurable_const.mul (mk_sdivSinh_continuous.measurable.comp h)).mul
      (Real.measurable_exp.comp ((h.pow_const 2).neg.div
        (measurable_const.mul (measurable_fst.comp measurable_fst))))
  exact (hm.integral_prod_right (ν := volume.restrict (Ioi 0))).measurable

theorem mk_hypRadial_measurable :
    Measurable fun w : ℝ × ℝ × ℝ => mkHypRadial w.1 w.2.1 w.2.2 := by
  unfold mkHypRadial
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  refine measurable_const.mul ?_
  have hc : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => (q.1.1, mkHypCos q.1.2.1 q.1.2.2 q.2) := by
    unfold mkHypCos; fun_prop
  have hm : StronglyMeasurable (Function.uncurry fun (w : ℝ × ℝ × ℝ) (φ : ℝ) =>
      mkHypKernel w.1 (mkHypCos w.2.1 w.2.2 φ)) :=
    (mk_hypKernel_measurable.comp hc).stronglyMeasurable
  exact (hm.integral_prod_right (ν := volume.restrict (Ioc 0 (2 * π)))).measurable

/-!
### The factor `pX`
-/

theorem mk_kernelX_nonneg {D0 : ℝ} (hD0 : 0 < D0) (t x x' : ℝ) : 0 ≤ mkKernelX D0 t x x' := by
  unfold mkKernelX
  split_ifs with h
  · exact mk_hypRadial_nonneg (by have := h.1; positivity) x x'
  · exact le_rfl

theorem mk_kernelX_eq {D0 t x x' : ℝ} (ht : 0 < t) (hx' : 0 ≤ x') :
    mkKernelX D0 t x x' = mkHypRadial (D0 * t / 2) x x' := by
  simp [mkKernelX, ht, hx']

theorem mk_kernelX_continuousOn {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (x : ℝ) :
    ContinuousOn (mkKernelX D0 t x) (Ici 0) :=
  (mk_hypRadial_continuous (by positivity) x).continuousOn.congr fun _ hx' =>
    mk_kernelX_eq ht hx'

theorem mk_kernelX_zero_pos {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (x : ℝ) :
    0 < mkKernelX D0 t x 0 := by
  rw [mk_kernelX_eq ht le_rfl]
  exact mk_hypRadial_zero_pos (by positivity) x

theorem mk_kernelX_measurable (D0 : ℝ) :
    Measurable fun w : ℝ × ℝ × ℝ => mkKernelX D0 w.1 w.2.1 w.2.2 := by
  have h1 : MeasurableSet {w : ℝ × ℝ × ℝ | 0 < w.1} :=
    measurableSet_lt measurable_const (by fun_prop : Measurable fun w : ℝ × ℝ × ℝ => w.1)
  have h2 : MeasurableSet {w : ℝ × ℝ × ℝ | 0 ≤ w.2.2} :=
    measurableSet_le measurable_const (by fun_prop : Measurable fun w : ℝ × ℝ × ℝ => w.2.2)
  have hS : MeasurableSet {w : ℝ × ℝ × ℝ | 0 < w.1 ∧ 0 ≤ w.2.2} := h1.inter h2
  have h : Measurable fun w : ℝ × ℝ × ℝ => mkHypRadial (D0 * w.1 / 2) w.2.1 w.2.2 :=
    mk_hypRadial_measurable.comp (f := fun w : ℝ × ℝ × ℝ => (D0 * w.1 / 2, w.2.1, w.2.2))
      (by fun_prop)
  have h' : Measurable fun w : ℝ × ℝ × ℝ =>
      if 0 < w.1 ∧ 0 ≤ w.2.2 then mkHypRadial (D0 * w.1 / 2) w.2.1 w.2.2 else 0 :=
    Measurable.ite hS h measurable_const
  exact h'

end BlockBand.Diffusion

