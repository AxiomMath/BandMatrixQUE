module
public import Mathlib

/-!
# Poisson kernel mass and tail estimates

The Poisson kernel `P_δ(t) = δ / (π (t² + δ²))` is a nonnegative, even, integrable function
of total mass one, and its mass outside `[-h,h]` is at most `2 δ / (π h)`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set Filter
open scoped Topology

def poissonKernel (δ t : ℝ) : ℝ := δ / (Real.pi * (t ^ 2 + δ ^ 2))

theorem poissonKernel_nonneg {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ poissonKernel δ t := by unfold poissonKernel; positivity

theorem poissonKernel_even (δ t : ℝ) : poissonKernel δ (-t) = poissonKernel δ t := by
  simp [poissonKernel]

theorem poissonKernel_scale {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    poissonKernel δ t = (1 / (Real.pi * δ)) * (1 + (δ⁻¹ * t) ^ 2)⁻¹ := by
  unfold poissonKernel
  have hden : t ^ 2 + δ ^ 2 ≠ 0 := by positivity
  field_simp [hδ.ne', Real.pi_ne_zero, hden]
  ring

theorem integrable_poissonKernel {δ : ℝ} (hδ : 0 < δ) :
    Integrable (poissonKernel δ) := by
  have h := (integrable_inv_one_add_mul_sq (inv_ne_zero hδ.ne')).const_mul
    (1 / (Real.pi * δ))
  exact h.congr (Filter.Eventually.of_forall (fun t => (poissonKernel_scale hδ t).symm))

theorem integral_poissonKernel {δ : ℝ} (hδ : 0 < δ) :
    (∫ t : ℝ, poissonKernel δ t) = 1 := by
  simp_rw [poissonKernel_scale hδ]
  rw [integral_const_mul, integral_univ_inv_one_add_mul_sq,
    abs_of_pos (inv_pos.mpr hδ)]
  field_simp [Real.pi_ne_zero, hδ.ne']

theorem lintegral_poissonKernel {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ t : ℝ, ENNReal.ofReal (poissonKernel δ t)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_poissonKernel hδ)
    (ae_of_all _ (poissonKernel_nonneg hδ)), integral_poissonKernel hδ]
  simp

theorem integrableOn_inv_sq_Ioi {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun t : ℝ => t⁻¹ ^ 2) (Ioi h) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := fun t : ℝ => -t⁻¹)
  · intro t ht
    have ht0 : t ≠ 0 := (hh.trans_le ht).ne'
    convert ((hasDerivAt_id t).inv ht0).neg using 1
    · rfl
    · dsimp
      field_simp
  · intro t _
    exact sq_nonneg _
  · simpa using (tendsto_inv_atTop_zero.neg :
      Tendsto (fun t : ℝ => -t⁻¹) atTop (𝓝 (-0)))

theorem integral_inv_sq_Ioi {h : ℝ} (hh : 0 < h) :
    (∫ t : ℝ in Ioi h, t⁻¹ ^ 2) = h⁻¹ := by
  have hd : ∀ t ∈ Ici h, HasDerivAt (fun t : ℝ => -t⁻¹) (t⁻¹ ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := (hh.trans_le ht).ne'
    convert ((hasDerivAt_id t).inv ht0).neg using 1
    · rfl
    · dsimp
      field_simp
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd
    (fun t _ => sq_nonneg t⁻¹)
    (by simpa using (tendsto_inv_atTop_zero.neg :
      Tendsto (fun t : ℝ => -t⁻¹) atTop (𝓝 (-0))))
  simpa using he

theorem poissonKernel_le_inv_sq {δ t : ℝ} (hδ : 0 < δ) (ht : t ≠ 0) :
    poissonKernel δ t ≤ (δ / Real.pi) * t⁻¹ ^ 2 := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  unfold poissonKernel
  calc
    δ / (Real.pi * (t ^ 2 + δ ^ 2)) ≤ δ / (Real.pi * t ^ 2) := by
      apply div_le_div_of_nonneg_left hδ.le (mul_pos Real.pi_pos ht2)
      gcongr
      exact le_add_of_nonneg_right (sq_nonneg δ)
    _ = (δ / Real.pi) * t⁻¹ ^ 2 := by field_simp

theorem integral_poissonKernel_Ioi_le {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) :
    (∫ t : ℝ in Ioi h, poissonKernel δ t) ≤ δ / (Real.pi * h) := by
  calc
    (∫ t : ℝ in Ioi h, poissonKernel δ t) ≤
        ∫ t : ℝ in Ioi h, (δ / Real.pi) * t⁻¹ ^ 2 := by
      apply setIntegral_mono_on (integrable_poissonKernel hδ).integrableOn
        ((integrableOn_inv_sq_Ioi hh).const_mul _) measurableSet_Ioi
      intro t ht
      exact poissonKernel_le_inv_sq hδ (hh.trans ht).ne'
    _ = δ / (Real.pi * h) := by
      rw [integral_const_mul, integral_inv_sq_Ioi hh]
      field_simp

theorem integral_poissonKernel_tail_eq_two {δ h : ℝ} (hh : 0 < h) :
    (∫ t : ℝ in {t | h < |t|}, poissonKernel δ t) =
      2 * ∫ t : ℝ in Ioi h, poissonKernel δ t := by
  have hm : MeasurableSet {t : ℝ | h < |t|} := measurableSet_lt measurable_const measurable_abs
  have heq : (fun t : ℝ => (Ioi h).indicator (poissonKernel δ) |t|) =
      ({t : ℝ | h < |t|}).indicator (poissonKernel δ) := by
    funext t
    change (if h < |t| then poissonKernel δ |t| else 0) =
      (if h < |t| then poissonKernel δ t else 0)
    split_ifs
    · simp only [poissonKernel, sq_abs]
    · rfl
  have he := integral_comp_abs (f := (Ioi h).indicator (poissonKernel δ))
  rw [heq, integral_indicator hm, setIntegral_indicator measurableSet_Ioi] at he
  have hi : Ioi (0 : ℝ) ∩ Ioi h = Ioi h := by
    apply Set.inter_eq_right.mpr
    intro t ht
    exact hh.trans ht
  simpa only [hi] using he

theorem integral_poissonKernel_tail_le {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) :
    (∫ t : ℝ in {t | h < |t|}, poissonKernel δ t) ≤ 2 * δ / (Real.pi * h) := by
  rw [integral_poissonKernel_tail_eq_two hh]
  calc
    2 * (∫ t : ℝ in Ioi h, poissonKernel δ t) ≤ 2 * (δ / (Real.pi * h)) :=
      mul_le_mul_of_nonneg_left (integral_poissonKernel_Ioi_le hδ hh) (by norm_num)
    _ = _ := by ring

theorem lintegral_poissonKernel_tail_le {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) :
    (∫⁻ t : ℝ in {t | h < |t|}, ENNReal.ofReal (poissonKernel δ t)) ≤
      ENNReal.ofReal (2 * δ / (Real.pi * h)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_poissonKernel hδ).integrableOn
    (ae_of_all _ (poissonKernel_nonneg hδ))]
  exact ENNReal.ofReal_le_ofReal (integral_poissonKernel_tail_le hδ hh)

end BlockBand.Counting
