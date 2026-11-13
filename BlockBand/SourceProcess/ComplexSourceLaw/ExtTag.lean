module

public import BlockBand.SourceProcess.ComplexSourceLaw.Marginal
public import BlockBand.SourceProcess.ComplexSourceLaw.GaussianForms

/-!
# Unit-mass tag forms: expansion and conditional Gaussian moments

For unit-mass tags
`ξ_k = W^{-1/2} ι_k g`:

* `tagForm_tagVector`: `ξ_k*Gξ'_l = W⁻¹ Σ_{a,b} conj(g_a) G_{(k,a),(l,b)} h_b`;
* `integral_tagZ`: `E_g[ξ_k*Gξ_k] = W⁻¹ Σ_a G_{(k,a),(k,a)}` (with integrability);
* `lintegral_tagY_sq`: `E_{g,h}|ξ_k*Gξ'_l|² = W⁻² Σ_{a,b}|G_{(k,a),(l,b)}|²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionLaws
open scoped ComplexConjugate

variable {W n : ℕ}

theorem sqrt_inv_mul_self (W : ℕ) :
    ((Real.sqrt (1 / W) : ℝ) : ℂ) * ((Real.sqrt (1 / W) : ℝ) : ℂ) = (W : ℂ)⁻¹ := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast; ring

theorem tagForm_tagVector (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (k l : Fin n)
    (g h : Fin W → ℂ) :
    tagForm G (tagVector W n k 1 g) (tagVector W n l 1 h) =
      (W : ℂ)⁻¹ * ∑ a, ∑ b, conj (g a) * G (k, a) (l, b) * h b := by
  simp only [tagForm, tagVector, dotProduct, mulVec, Fintype.sum_prod_type, Pi.star_apply]
  simp only [one_div, Real.sqrt_inv, Complex.ofReal_inv, mul_ite, mul_zero]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
  have hs : ((Real.sqrt W : ℝ) : ℂ)⁻¹ * ((Real.sqrt W : ℝ) : ℂ)⁻¹ = (W : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg W)]
    simp
  simp only [ite_true, Complex.star_def, map_mul, map_inv₀, Complex.conj_ofReal]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single l (fun x _ hx => by simp [hx]) (by simp)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ite_eq_left rfl]
  linear_combination (conj (g a) * G (k, a) (l, b) * h b) * hs

theorem tagForm_tagVector_fun (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (k l : Fin n) :
    (fun g : Fin W → ℂ => tagForm G (tagVector W n k 1 g) (tagVector W n l 1 g)) =
      fun g => (W : ℂ)⁻¹ * ∑ a, ∑ b, conj (g a) * G (k, a) (l, b) * g b :=
  funext fun g => tagForm_tagVector G k l g g

theorem integrable_tagZ (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (k : Fin n) :
    Integrable (fun g => tagForm G (tagVector W n k 1 g) (tagVector W n k 1 g))
      (circularVectorLaw (Fin W)) := by
  rw [tagForm_tagVector_fun]
  exact (integrable_quad fun a b => G (k, a) (k, b)).const_mul _

/-- `E_g[ξ_k*Gξ_k] = W⁻¹ Σ_a G_{(k,a),(k,a)}`. -/
theorem integral_tagZ (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (k : Fin n) :
    ∫ g, tagForm G (tagVector W n k 1 g) (tagVector W n k 1 g) ∂circularVectorLaw (Fin W) =
      (W : ℂ)⁻¹ * ∑ a, G (k, a) (k, a) := by
  rw [tagForm_tagVector_fun, integral_const_mul, integral_quad fun a b => G (k, a) (k, b)]

theorem tagForm_tagVector_sq (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (k l : Fin n)
    (g h : Fin W → ℂ) :
    ‖tagForm G (tagVector W n k 1 g) (tagVector W n l 1 h)‖ ^ 2 = ((W : ℝ)⁻¹) ^ 2 *
      ‖∑ b, (∑ a, G (k, a) (l, b) * conj (g a)) * h b‖ ^ 2 := by
  have e : (∑ a, ∑ b, conj (g a) * G (k, a) (l, b) * h b) =
      ∑ b, (∑ a, G (k, a) (l, b) * conj (g a)) * h b := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  rw [tagForm_tagVector, norm_mul, mul_pow, norm_inv, Complex.norm_natCast, e]

/-- **`E_{g,h}|ξ_k*Gξ'_l|² = W⁻² Σ_{a,b}|G_{(k,a),(l,b)}|²`.** -/
theorem lintegral_tagY_sq (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (k l : Fin n) :
    ∫⁻ x, ENNReal.ofReal (‖tagForm G (tagVector W n k 1 x.1) (tagVector W n l 1 x.2)‖ ^ 2)
      ∂(circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W)) =
      ENNReal.ofReal (((W : ℝ)⁻¹) ^ 2 * ∑ a, ∑ b, ‖G (k, a) (l, b)‖ ^ 2) := by
  have hm : Measurable fun x : (Fin W → ℂ) × (Fin W → ℂ) => ENNReal.ofReal
      (‖tagForm G (tagVector W n k 1 x.1) (tagVector W n l 1 x.2)‖ ^ 2) :=
    ((measurable_tagForm measurable_const ((measurable_tagVector n k 1).comp measurable_fst)
      ((measurable_tagVector n l 1).comp measurable_snd)).norm.pow_const 2).ennreal_ofReal
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [tagForm_tagVector_sq, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((W : ℝ)⁻¹) ^ 2)]
  have hc : ∀ b : Fin W, Measurable fun g : Fin W → ℂ =>
      ENNReal.ofReal (‖∑ a, G (k, a) (l, b) * conj (g a)‖ ^ 2) := fun b =>
    ((Finset.measurable_sum _ fun a _ => measurable_const.mul
      (Complex.continuous_conj.measurable.comp (measurable_pi_apply a))).norm.pow_const
        2).ennreal_ofReal
  have inner : ∀ g : Fin W → ℂ, ∫⁻ h, ENNReal.ofReal (((W : ℝ)⁻¹) ^ 2) *
      ENNReal.ofReal (‖∑ b, (∑ a, G (k, a) (l, b) * conj (g a)) * h b‖ ^ 2)
        ∂circularVectorLaw (Fin W) = ENNReal.ofReal (((W : ℝ)⁻¹) ^ 2) *
      ∑ b, ENNReal.ofReal (‖∑ a, G (k, a) (l, b) * conj (g a)‖ ^ 2) := fun g => by
    have hmeas : Measurable fun h : Fin W → ℂ =>
        ENNReal.ofReal (‖∑ b, (∑ a, G (k, a) (l, b) * conj (g a)) * h b‖ ^ 2) :=
      ((Finset.measurable_sum _ fun b _ =>
        measurable_const.mul (measurable_pi_apply b)).norm.pow_const 2).ennreal_ofReal
    rw [lintegral_const_mul _ hmeas, lintegral_norm_sq_lin,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  rw [lintegral_congr fun g => inner g]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun b _ => hc b),
    lintegral_finsetSum _ fun b _ => hc b]
  simp_rw [lintegral_norm_sq_conj_lin]
  rw [Finset.sum_comm (f := fun a b => ‖G (k, a) (l, b)‖ ^ 2),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]

end BlockBand.SourceProcess.ComplexSourceLaw
