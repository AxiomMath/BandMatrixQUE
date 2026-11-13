module

public import BlockBand.SourceProcess.ComplexSourceLaw.Gaussian

/-!
# Gaussian linear and quadratic forms

* `lintegral_norm_sq_lin`: `E|Σ_a c_a g_a|² = Σ_a |c_a|²` (and with `conj g`,
  `lintegral_norm_sq_conj_lin`);
* `integral_quad`: `E Σ_{a,b} conj(g_a) B_ab g_b = Σ_a B_aa`, with integrability.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem normSq_lin_eq (c g : ι → ℂ) :
    ((‖∑ a, c a * g a‖ ^ 2 : ℝ) : ℂ) =
      ∑ a, ∑ b, (conj (c a) * c b) * (conj (g a) * g b) := by
  rw [Complex.ofReal_pow, ← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul]; ring

omit [DecidableEq ι] in
theorem integrable_normSq_lin_complex (c : ι → ℂ) :
    Integrable (fun g : ι → ℂ => ∑ a, ∑ b, (conj (c a) * c b) * (conj (g a) * g b))
      (circularVectorLaw ι) :=
  integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_conj_mul a b).const_mul _

theorem integral_normSq_lin (c : ι → ℂ) :
    ∫ g, ‖∑ a, c a * g a‖ ^ 2 ∂circularVectorLaw ι = ∑ a, ‖c a‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [normSq_lin_eq]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_conj_mul a b).const_mul _]
  simp_rw [integral_finsetSum _ fun b _ => (integrable_conj_mul _ b).const_mul _,
    integral_const_mul, integral_conj_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.conj_mul']

omit [DecidableEq ι] in
theorem integrable_normSq_lin (c : ι → ℂ) :
    Integrable (fun g : ι → ℂ => ‖∑ a, c a * g a‖ ^ 2) (circularVectorLaw ι) := by
  have h := (integrable_normSq_lin_complex c).re
  refine h.congr (ae_of_all _ fun g => ?_)
  simp only
  rw [← normSq_lin_eq]
  exact Complex.ofReal_re _

/-- **`E|Σ c_a g_a|² = Σ|c_a|²`.** -/
theorem lintegral_norm_sq_lin (c : ι → ℂ) :
    ∫⁻ g, ENNReal.ofReal (‖∑ a, c a * g a‖ ^ 2) ∂circularVectorLaw ι =
      ENNReal.ofReal (∑ a, ‖c a‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_normSq_lin c)
    (ae_of_all _ fun _ => by positivity), integral_normSq_lin]

/-- **`E|Σ c_a conj(g_a)|² = Σ|c_a|²`.** -/
theorem lintegral_norm_sq_conj_lin (c : ι → ℂ) :
    ∫⁻ g, ENNReal.ofReal (‖∑ a, c a * conj (g a)‖ ^ 2) ∂circularVectorLaw ι =
      ENNReal.ofReal (∑ a, ‖c a‖ ^ 2) := by
  have e : ∀ g : ι → ℂ, ‖∑ a, c a * conj (g a)‖ = ‖∑ a, conj (c a) * g a‖ := fun g => by
    rw [← Complex.norm_conj, map_sum]
    simp only [map_mul, Complex.conj_conj]
  simp_rw [e]
  rw [lintegral_norm_sq_lin]
  simp only [Complex.norm_conj]

omit [DecidableEq ι] in
theorem integrable_quad (B : ι → ι → ℂ) :
    Integrable (fun g : ι → ℂ => ∑ a, ∑ b, conj (g a) * B a b * g b) (circularVectorLaw ι) := by
  refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
  have := (integrable_conj_mul a b).const_mul (B a b)
  refine this.congr (ae_of_all _ fun g => ?_)
  simp only; ring

/-- **`E Σ conj(g_a) B_ab g_b = Σ_a B_aa`.** -/
theorem integral_quad (B : ι → ι → ℂ) :
    ∫ g, ∑ a, ∑ b, conj (g a) * B a b * g b ∂circularVectorLaw ι = ∑ a, B a a := by
  have e : ∀ g : ι → ℂ, ∑ a, ∑ b, conj (g a) * B a b * g b =
      ∑ a, ∑ b, B a b * (conj (g a) * g b) := fun g => by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_conj_mul a b).const_mul _]
  simp_rw [integral_finsetSum _ fun b _ => (integrable_conj_mul _ b).const_mul _,
    integral_const_mul, integral_conj_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

end BlockBand.SourceProcess.ComplexSourceLaw
