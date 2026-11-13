module

public import BlockBand.Diffusion.Kernel.McKeanDefs
public import BlockBand.Diffusion.Kernel.McKeanGauss
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Radial mass of McKean's kernel

For `T > 0` (Lebesgue measure on `(1, ∞)`):

* `mk_lintegral_hypKernel`: `∫_1^∞ K_T(c) dc = 1/(2π)`, where `K_T = mkHypKernel T` is the
  McKean kernel. Proof: Tonelli in `(c, v)`, the substitution `w = c + v²`, the
  `v`-integral `∫ 1[1 + v² < w] dv = √(w - 1)`, the substitution `w = cosh s`
  (`√(cosh s - 1) = √2 sinh(s/2)`) and the Gaussian moment of `McKeanGauss`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

theorem mk_arcosh_measurable : Measurable Real.arcosh := by
  unfold Real.arcosh; fun_prop

theorem mk_mcKeanG_measurable (T : ℝ) : Measurable (mkMcKeanG T) := by
  unfold mkMcKeanG
  exact (measurable_const.mul (mk_sdivSinh_continuous.measurable.comp mk_arcosh_measurable)).mul
    (Real.measurable_exp.comp ((mk_arcosh_measurable.pow_const 2).neg.div_const _))

theorem mk_ofReal_hypKernel {T c : ℝ} (hT : 0 < T) (hc : 1 ≤ c) :
    ENNReal.ofReal (mkHypKernel T c) =
      ENNReal.ofReal (Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T) ^ (3 / 2 : ℝ)) *
        ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (mkMcKeanG T (c + v ^ 2)) := by
  have hint := mk_integrableOn_G hT c
  rw [max_eq_left hc] at hint
  unfold mkHypKernel
  rw [max_eq_left hc, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun v => (mk_mcKeanG_pos _ _).le)]

/-- Tonelli in `(c, v)` and `w = c + v²`:
`∫_1^∞ ∫_0^∞ g(c + v²) dv dc = ∫_1^∞ √(w - 1) g(w) dw` for measurable `g ≥ 0`. -/
theorem mk_lintegral_swap_sqrt {g : ℝ → ℝ≥0∞} (hgm : Measurable g) :
    ∫⁻ c in Ioi (1 : ℝ), ∫⁻ v in Ioi (0 : ℝ), g (c + v ^ 2) =
      ∫⁻ w in Ioi (1 : ℝ), ENNReal.ofReal (Real.sqrt (w - 1)) * g w := by
  rw [lintegral_lintegral_swap (f := fun c v => g (c + v ^ 2)) ((hgm.comp (by fun_prop :
    Measurable fun p : ℝ × ℝ => p.1 + p.2 ^ 2)).aemeasurable)]
  have h1 : ∀ v : ℝ, ∫⁻ c in Ioi (1 : ℝ), g (c + v ^ 2) =
      ∫⁻ w in Ioi (1 : ℝ), ({p : ℝ × ℝ | 1 + p.1 ^ 2 < p.2}.indicator (fun p => g p.2)) (v, w) := by
    intro v
    have him := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (1 : ℝ))
      (f := fun c => c + v ^ 2) (f' := fun _ => 1) measurableSet_Ioi
      (fun c _ => ((hasDerivAt_id c).add_const _).hasDerivWithinAt)
      (fun a _ b _ h => by simpa using h) g
    rw [image_add_const_Ioi] at him
    simp only [abs_one, ENNReal.ofReal_one, one_mul] at him
    rw [← him]
    have : ∀ w, ({p : ℝ × ℝ | 1 + p.1 ^ 2 < p.2}.indicator (fun p => g p.2)) (v, w) =
        (Ioi (1 + v ^ 2)).indicator g w := by
      intro w
      by_cases hw : 1 + v ^ 2 < w <;> simp [indicator, hw]
    simp_rw [this]
    rw [setLIntegral_indicator measurableSet_Ioi,
      inter_eq_left.2 (Ioi_subset_Ioi (by nlinarith [sq_nonneg v]))]
  simp_rw [h1]
  have hFm : Measurable ({p : ℝ × ℝ | 1 + p.1 ^ 2 < p.2}.indicator (fun p => g p.2)) :=
    (hgm.comp measurable_snd).indicator (measurableSet_lt (by fun_prop) (by fun_prop))
  rw [lintegral_lintegral_swap (f := fun v w =>
    ({p : ℝ × ℝ | 1 + p.1 ^ 2 < p.2}.indicator (fun p => g p.2)) (v, w)) hFm.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw1 : (0 : ℝ) ≤ w - 1 := by have := mem_Ioi.1 hw; linarith
  have : ∀ v ∈ Ioi (0 : ℝ), ({p : ℝ × ℝ | 1 + p.1 ^ 2 < p.2}.indicator (fun p => g p.2)) (v, w) =
      (Iio (Real.sqrt (w - 1))).indicator (fun _ => g w) v := by
    intro v hv
    have hv0 : 0 ≤ v := (mem_Ioi.1 hv).le
    have hiff : 1 + v ^ 2 < w ↔ v < Real.sqrt (w - 1) := by
      rw [Real.lt_sqrt hv0]; constructor <;> intro h <;> linarith
    by_cases h : 1 + v ^ 2 < w
    · simp [indicator, h, hiff.1 h]
    · simp [indicator, h, mt hiff.2 h]
  rw [setLIntegral_congr_fun measurableSet_Ioi this, setLIntegral_indicator measurableSet_Iio,
    setLIntegral_const, inter_comm, Ioi_inter_Iio, Real.volume_Ioo, sub_zero, mul_comm]

theorem mk_lintegral_G_swap (T : ℝ) :
    ∫⁻ c in Ioi (1 : ℝ), ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (mkMcKeanG T (c + v ^ 2)) =
      ∫⁻ w in Ioi (1 : ℝ), ENNReal.ofReal (Real.sqrt (w - 1)) *
        ENNReal.ofReal (mkMcKeanG T w) :=
  mk_lintegral_swap_sqrt (g := fun w => ENNReal.ofReal (mkMcKeanG T w))
    (ENNReal.measurable_ofReal.comp (mk_mcKeanG_measurable T))

theorem mk_cosh_image_Ioi : Real.cosh '' Ioi (0 : ℝ) = Ioi 1 := by
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact Real.one_lt_cosh.2 (ne_of_gt hs)
  · intro hw
    have hw1 : (1 : ℝ) ≤ w := (mem_Ioi.1 hw).le
    exact ⟨Real.arcosh w, Real.arcosh_pos hw, Real.cosh_arcosh hw1⟩

theorem mk_sqrt_cosh_sub_one {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (Real.cosh s - 1) = Real.sqrt 2 * Real.sinh (s / 2) := by
  have h : Real.cosh s - 1 = 2 * Real.sinh (s / 2) ^ 2 := by
    have := Real.cosh_two_mul (s / 2)
    rw [show 2 * (s / 2) = s by ring, Real.cosh_sq] at this
    linarith
  rw [h, Real.sqrt_mul (by norm_num), Real.sqrt_sq (Real.sinh_nonneg_iff.2 (by linarith))]

theorem mk_lintegral_G_sqrt {T : ℝ} (hT : 0 < T) :
    ∫⁻ w in Ioi (1 : ℝ), ENNReal.ofReal (Real.sqrt (w - 1)) * ENNReal.ofReal (mkMcKeanG T w) =
      ENNReal.ofReal (2 * Real.sqrt 2 * (T * Real.sqrt (4 * π * T) * Real.exp (T / 4) / 2)) := by
  have him := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ)) (f := Real.cosh)
    (f' := Real.sinh) measurableSet_Ioi (fun s _ => (Real.hasDerivAt_cosh s).hasDerivWithinAt)
    (Real.cosh_injOn.mono Ioi_subset_Ici_self)
    (fun w => ENNReal.ofReal (Real.sqrt (w - 1)) * ENNReal.ofReal (mkMcKeanG T w))
  rw [mk_cosh_image_Ioi] at him
  rw [him]
  have hint : IntegrableOn (fun s : ℝ => 2 * Real.sqrt 2 *
      (s * Real.sinh (s / 2) * Real.exp (-s ^ 2 / (4 * T)))) (Ioi 0) :=
    ((mk_integrable_gauss_sinh hT).const_mul _).integrableOn
  rw [← mk_integral_Ioi_gauss_sinh hT, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal hint ?_]
  · refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hs
    have hsh : 0 < Real.sinh s := Real.sinh_pos_iff.2 hs0
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    unfold mkMcKeanG mkSdivSinh
    rw [Real.arcosh_cosh hs0.le, abs_of_pos hsh, mk_sqrt_cosh_sub_one hs0.le]
    simp only [ne_of_gt hs0, ↓reduceIte]
    field_simp
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_)
    have hs0 : 0 < s := hs
    have := Real.sinh_pos_iff.2 (by linarith : 0 < s / 2)
    positivity

/-- **McKean's kernel has total radial mass `1/(2π)`**: `∫_1^∞ K_T(c) dc = 1/(2π)` (`T > 0`). -/
theorem mk_lintegral_hypKernel {T : ℝ} (hT : 0 < T) :
    ∫⁻ c in Ioi (1 : ℝ), ENNReal.ofReal (mkHypKernel T c) = ENNReal.ofReal (1 / (2 * π)) := by
  rw [setLIntegral_congr_fun measurableSet_Ioi fun c hc => mk_ofReal_hypKernel hT (le_of_lt hc),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mk_lintegral_G_swap, mk_lintegral_G_sqrt hT,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h4 : 0 < 4 * π * T := by positivity
  have hr : (4 * π * T) ^ (3 / 2 : ℝ) = 4 * π * T * Real.sqrt (4 * π * T) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h4, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt (4 * π * T) := Real.sqrt_pos.2 h4
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have he : Real.exp (-T / 4) = (Real.exp (T / 4))⁻¹ := by
    rw [neg_div, Real.exp_neg]
  rw [hr, he]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring
end BlockBand.Diffusion
