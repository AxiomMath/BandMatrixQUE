module
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Second-order generator terms are determined by complex brackets

Let `E` be a real vector space with complex coordinates `coord e : E → ℂ` (`e ∈ X`) and vectors
`u e, v e` such that `x = ∑_e (Re coord e x) u e + (Im coord e x) v e` for all `x`. For a real
bilinear `T` and finite families `ν : κ → E`, `ν' : κ' → E`, if the complex-bilinear brackets
`∑_a coord e (ν a) · coord e' (ν a)` and the sesquilinear brackets
`∑_a coord e (ν a) · conj (coord e' (ν a))` agree, then `∑_a T (ν a) (ν a) = ∑_b T (ν' b) (ν' b)`
(`sum_bilin_eq_of_brackets`). This is the algebraic reason why the generator of a function of
the Gram pair depends only on the Gram covariance.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness

/-- The real-linear form reproducing `Re z Re w α + Re z Im w β + Im z Re w γ + Im z Im w δ`
from `zw` and `z w̄`. -/
def bracketForm (α β γ δ : ℝ) (p q : ℂ) : ℝ :=
  (α - δ) / 2 * p.re + (β + γ) / 2 * p.im + (α + δ) / 2 * q.re + (γ - β) / 2 * q.im

theorem real_quad_eq_bracketForm (α β γ δ : ℝ) (z w : ℂ) :
    z.re * w.re * α + z.re * w.im * β + z.im * w.re * γ + z.im * w.im * δ =
      bracketForm α β γ δ (z * w) (z * star w) := by
  simp only [bracketForm, Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

theorem sum_bracketForm {κ : Type*} (s : Finset κ) (α β γ δ : ℝ) (p q : κ → ℂ) :
    ∑ a ∈ s, bracketForm α β γ δ (p a) (q a) =
      bracketForm α β γ δ (∑ a ∈ s, p a) (∑ a ∈ s, q a) := by
  simp only [bracketForm, Complex.re_sum, Complex.im_sum, Finset.mul_sum,
    Finset.sum_add_distrib]

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {X : Type*} [Fintype X]

theorem bilin_self_eq (T : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (coord : X → E → ℂ) (u v : X → E)
    (hdec : ∀ x, x = ∑ e, ((coord e x).re • u e + (coord e x).im • v e)) (x : E) :
    T x x = ∑ e, ∑ e', ((coord e x).re * (coord e' x).re * T (u e) (u e') +
      (coord e x).re * (coord e' x).im * T (u e) (v e') +
      (coord e x).im * (coord e' x).re * T (v e) (u e') +
      (coord e x).im * (coord e' x).im * T (v e) (v e')) := by
  refine (congrArg (fun z => T z z) (hdec x)).trans ?_
  simp only [map_sum, map_add, map_smul, LinearMap.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
  ring

/-- **Bracket determination.** -/
theorem sum_bilin_eq_of_brackets (T : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (coord : X → E → ℂ) (u v : X → E)
    (hdec : ∀ x, x = ∑ e, ((coord e x).re • u e + (coord e x).im • v e))
    {κ κ' : Type*} [Fintype κ] [Fintype κ'] (ν : κ → E) (ν' : κ' → E)
    (h1 : ∀ e e', ∑ a, coord e (ν a) * coord e' (ν a) = ∑ b, coord e (ν' b) * coord e' (ν' b))
    (h2 : ∀ e e', ∑ a, coord e (ν a) * star (coord e' (ν a)) =
      ∑ b, coord e (ν' b) * star (coord e' (ν' b))) :
    ∑ a, T (ν a) (ν a) = ∑ b, T (ν' b) (ν' b) := by
  simp only [bilin_self_eq T coord u v hdec, real_quad_eq_bracketForm]
  rw [Finset.sum_comm, Finset.sum_comm (γ := κ')]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (γ := κ')]
  refine Finset.sum_congr rfl fun e' _ => ?_
  rw [sum_bracketForm, sum_bracketForm, h1, h2]

end BlockBand.SourceProcess.Stochastic.GramUniqueness
