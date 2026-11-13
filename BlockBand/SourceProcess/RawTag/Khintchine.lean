module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Gaussian moments of linear and quadratic forms of a circular vector

* `pi_gaussian_map_linear`: `Σαᵢρᵢ` with iid `ρᵢ ~ N(0,v)` has law `N(0, (Σαᵢ²)v)`;
* `lintegral_gaussianReal_rpow`: `E|N(0,v)|^s = v^{s/2} M_s`;
* `lintegral_linear_circular_le`: `E_g|Σ cₐgₐ|^s ≤ 2M_s(Σ|cₐ|²)^{s/2}` (`s ≥ 2`);
* `lintegral_normSq_rpow_le` (proved from it in a sibling module): `E_g(‖Sg‖²)^r ≤ 2M_{2r}‖S‖_HS^{2r}` (`r ≥ 1`, Minkowski in `L^r`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal

/-- **Law of a linear combination** of iid centred real Gaussians. -/
theorem pi_gaussian_map_linear {ι : Type*} [Fintype ι] (α : ι → ℝ) (v : ℝ≥0) :
    (Measure.pi fun _ : ι => gaussianReal 0 v).map (fun ρ => ∑ i, α i * ρ i) =
      gaussianReal 0 (Real.toNNReal (∑ i, α i ^ 2) * v) := by
  have hm : Measurable fun ρ : ι → ℝ => fun i => α i * ρ i := by fun_prop
  have hsum : Measurable fun p : ι → ℝ => ∑ i, p i := by fun_prop
  have h1 : (Measure.pi fun _ : ι => gaussianReal 0 v).map (fun ρ i => α i * ρ i) =
      Measure.pi fun i => gaussianReal 0 (Real.toNNReal (α i ^ 2) * v) := by
    rw [Measure.pi_map_pi (fun i => (measurable_const_mul (α i)).aemeasurable)]
    congr 1; funext i
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 2; ext; simp [Real.coe_toNNReal _ (sq_nonneg _)]
  have e : (fun ρ : ι → ℝ => ∑ i, α i * ρ i) = (fun p => ∑ i, p i) ∘ (fun ρ i => α i * ρ i) :=
    rfl
  rw [e, ← Measure.map_map hsum hm, h1]
  apply Measure.ext_of_charFun
  rw [charFun_map_sum_pi_eq_prod]
  funext t
  rw [Finset.prod_apply]
  simp only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Real.coe_toNNReal _ (sq_nonneg _),
    Real.coe_toNNReal _ (Finset.sum_nonneg fun i _ => sq_nonneg (α i))]
  push_cast
  rw [Finset.sum_neg_distrib, Finset.sum_mul, Finset.sum_mul, Finset.sum_div]

/-- `M_s = E|Z|^s` for `Z ~ N(0,1)`. -/
def gaussMoment (s : ℝ) : ℝ := ∫ x, |x| ^ s ∂gaussianReal 0 1

theorem integrable_abs_rpow_gaussianReal (s : ℝ) (hs : 0 < s) (v : ℝ≥0) :
    Integrable (fun x : ℝ => |x| ^ s) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := v) (ENNReal.ofReal s)
    ENNReal.ofReal_ne_top).integrable_norm_rpow (by simpa using hs) ENNReal.ofReal_ne_top
  simpa [ENNReal.toReal_ofReal hs.le, Real.norm_eq_abs] using h

theorem gaussMoment_nonneg (s : ℝ) : 0 ≤ gaussMoment s :=
  integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) s

/-- **`E|N(0,v)|^s = v^{s/2} M_s`**. -/
theorem lintegral_gaussianReal_rpow (s : ℝ) (hs : 0 < s) (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂gaussianReal 0 v =
      ENNReal.ofReal ((v : ℝ) ^ (s / 2) * gaussMoment s) := by
  have hv : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1; ext; simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [hv, lintegral_map (by fun_prop) (by fun_prop)]
  have e : ∀ x : ℝ, ENNReal.ofReal (|Real.sqrt v * x| ^ s) =
      ENNReal.ofReal ((v : ℝ) ^ (s / 2)) * ENNReal.ofReal (|x| ^ s) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (NNReal.coe_nonneg v) _), abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.mul_rpow (Real.sqrt_nonneg _) (abs_nonneg _),
      Real.sqrt_eq_rpow, ← Real.rpow_mul (NNReal.coe_nonneg v)]
    congr 3; ring
  simp_rw [e]
  rw [lintegral_const_mul _ (by fun_prop),
    ENNReal.ofReal_mul (Real.rpow_nonneg (NNReal.coe_nonneg v) _),
    gaussMoment, ofReal_integral_eq_lintegral_ofReal (integrable_abs_rpow_gaussianReal s hs 1)
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg x) s)]

theorem rpow_sq_add_sq_le (u v s : ℝ) (hs : 0 ≤ s) :
    (u ^ 2 + v ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) * (|u| ^ s + |v| ^ s) := by
  have key : ∀ a c : ℝ, |a| ≤ |c| → (a ^ 2 + c ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) * |c| ^ s := by
    intro a c h
    have h2 : a ^ 2 + c ^ 2 ≤ 2 * |c| ^ 2 := by
      have := sq_le_sq.mpr h
      rw [sq_abs]; linarith
    calc (a ^ 2 + c ^ 2) ^ (s / 2) ≤ (2 * |c| ^ 2) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) h2 (by positivity)
      _ = 2 ^ (s / 2) * |c| ^ s := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul (abs_nonneg c)]
          congr 2; push_cast; ring
  have h2s : 0 ≤ (2 : ℝ) ^ (s / 2) := by positivity
  rcases le_total |u| |v| with h | h
  · have := key u v h
    nlinarith [Real.rpow_nonneg (abs_nonneg u) s]
  · have := key v u h
    rw [add_comm] at this
    nlinarith [Real.rpow_nonneg (abs_nonneg v) s]

/-- Real-part coefficients of `Σ cₐgₐ` in the real coordinates `ρ` of `g`. -/
def reCoef {W : ℕ} (c : Fin W → ℂ) (p : Fin W × Fin 2) : ℝ :=
  if p.2 = 0 then (c p.1).re else -(c p.1).im

/-- Imaginary-part coefficients of `Σ cₐgₐ`. -/
def imCoef {W : ℕ} (c : Fin W → ℂ) (p : Fin W × Fin 2) : ℝ :=
  if p.2 = 0 then (c p.1).im else (c p.1).re

theorem linear_circular_eq {W : ℕ} (c : Fin W → ℂ) (ρ : Fin W × Fin 2 → ℝ) :
    ∑ a, c a * ((ρ (a, 0) : ℂ) + (ρ (a, 1) : ℂ) * Complex.I) =
      ((∑ p, reCoef c p * ρ p : ℝ) : ℂ) + ((∑ p, imCoef c p * ρ p : ℝ) : ℂ) * Complex.I := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, reCoef, imCoef]
  apply Complex.ext <;>
    simp [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] <;> ring

theorem sum_reCoef_sq {W : ℕ} (c : Fin W → ℂ) : ∑ p, reCoef c p ^ 2 = ∑ a, ‖c a‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.sum_univ_two, reCoef, Complex.sq_norm, Complex.normSq_apply]
  simp; ring

theorem sum_imCoef_sq {W : ℕ} (c : Fin W → ℂ) : ∑ p, imCoef c p ^ 2 = ∑ a, ‖c a‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.sum_univ_two, imCoef, Complex.sq_norm, Complex.normSq_apply]
  simp; ring

theorem lintegral_pi_linear (ι : Type*) [Fintype ι] (α : ι → ℝ) (s : ℝ) (hs : 0 < s) :
    ∫⁻ ρ, ENNReal.ofReal (|∑ i, α i * ρ i| ^ s) ∂(Measure.pi fun _ : ι => gaussianReal 0 (1 / 2)) =
      ENNReal.ofReal (((∑ i, α i ^ 2) / 2) ^ (s / 2) * gaussMoment s) := by
  have hL : Measurable fun ρ : ι → ℝ => ∑ i, α i * ρ i := by fun_prop
  rw [← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (|x| ^ s)) (by fun_prop) hL,
    pi_gaussian_map_linear, lintegral_gaussianReal_rpow s hs]
  congr 3
  simp [Real.coe_toNNReal _ (Finset.sum_nonneg fun i _ => sq_nonneg (α i))]
  ring

/-- **`E_g|Σ cₐgₐ|^s ≤ 2M_s(Σ|cₐ|²)^{s/2}`** for a standard circular vector and `s ≥ 2`. -/
theorem lintegral_linear_circular_le {W : ℕ} (c : Fin W → ℂ) {s : ℝ} (hs : 2 ≤ s) :
    ∫⁻ g, ENNReal.ofReal (‖∑ a, c a * g a‖ ^ s) ∂circularVectorLaw (Fin W) ≤
      ENNReal.ofReal (2 * gaussMoment s * (∑ a, ‖c a‖ ^ 2) ^ (s / 2)) := by
  have hs0 : 0 < s := by linarith
  have hmap : Measurable fun (r : Fin W × Fin 2 → ℝ) (a : Fin W) =>
      (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I := by fun_prop
  have hF : Measurable fun g : Fin W → ℂ => ENNReal.ofReal (‖∑ a, c a * g a‖ ^ s) := by
    fun_prop
  rw [circularVectorLaw, lintegral_map hF hmap]
  set σ := ∑ a, ‖c a‖ ^ 2
  have hσ : 0 ≤ σ := Finset.sum_nonneg fun a _ => by positivity
  have hpt : ∀ ρ : Fin W × Fin 2 → ℝ,
      ENNReal.ofReal (‖∑ a, c a * ((ρ (a, 0) : ℂ) + (ρ (a, 1) : ℂ) * Complex.I)‖ ^ s) ≤
        ENNReal.ofReal (2 ^ (s / 2)) * (ENNReal.ofReal (|∑ p, reCoef c p * ρ p| ^ s) +
          ENNReal.ofReal (|∑ p, imCoef c p * ρ p| ^ s)) := by
    intro ρ
    rw [linear_circular_eq, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Complex.norm_def, Complex.normSq_add_mul_I, Real.sqrt_eq_rpow, ← Real.rpow_mul
      (by positivity)]
    calc _ = ((∑ p, reCoef c p * ρ p) ^ 2 + (∑ p, imCoef c p * ρ p) ^ 2) ^ (s / 2) := by
          congr 1; ring
      _ ≤ _ := rpow_sq_add_sq_le _ _ s hs0.le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop),
    lintegral_pi_linear _ _ s hs0, lintegral_pi_linear _ _ s hs0, sum_reCoef_sq, sum_imCoef_sq,
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) (gaussMoment_nonneg s))
      (mul_nonneg (by positivity) (gaussMoment_nonneg s)), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [Real.div_rpow hσ (by norm_num)]
  have h2 : (2 : ℝ) ^ (s / 2) ≠ 0 := by positivity
  field_simp
  ring

end BlockBand.SourceProcess.RawTag
