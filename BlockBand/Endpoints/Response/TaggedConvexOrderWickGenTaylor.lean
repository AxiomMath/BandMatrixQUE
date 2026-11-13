module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic

/-!
# Second-order Taylor coefficients of a substituted polynomial

Purely algebraic; no measure. Substitute into `Φ ∈ ℂ[x_w : w ∈ σ]` univariate polynomials
`F_w(s) ∈ ℂ[s]`, perturbing only the variables of a finite set `S` (`wg_restrict`). With base point
`x_w = F_w(0)` (`wg_base`), the coefficients of `s` and `s²` of `Φ(F(s))` are

* `wg_taylor1`: `[s]Φ(F) = Σ_{w∈S} ∂_wΦ(x) [s]F_w`;
* `wg_taylor2`: `[s²]Φ(F) = Σ_{w∈S} ∂_wΦ(x) [s²]F_w + ½ Σ_{w,v∈S} ∂_v∂_wΦ(x) [s]F_w [s]F_v`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Finset

variable {σ : Type*} [DecidableEq σ]

/-- The perturbation restricted to `S`: `F_w` for `w ∈ S`, the constant `F_w(0)` otherwise. -/
def wg_restrict (F : σ → Polynomial ℂ) (S : Finset σ) (w : σ) : Polynomial ℂ :=
  if w ∈ S then F w else Polynomial.C ((F w).coeff 0)

/-- The base point `x_w = F_w(0)`. -/
def wg_base (F : σ → Polynomial ℂ) (w : σ) : ℂ := (F w).coeff 0

theorem wg_coeff_one_mul (p q : Polynomial ℂ) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  simp [Finset.Nat.antidiagonal_succ]

theorem wg_coeff_two_mul (p q : Polynomial ℂ) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 + p.coeff 2 * q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  simp [Finset.Nat.antidiagonal_succ]
  ring

theorem wg_restrict_coeff_zero (F : σ → Polynomial ℂ) (S : Finset σ) (w : σ) :
    (wg_restrict F S w).coeff 0 = wg_base F w := by
  unfold wg_restrict wg_base
  split_ifs <;> simp

theorem wg_restrict_coeff_pos (F : σ → Polynomial ℂ) (S : Finset σ) (w : σ) {n : ℕ}
    (hn : n ≠ 0) : (wg_restrict F S w).coeff n = if w ∈ S then (F w).coeff n else 0 := by
  unfold wg_restrict
  split_ifs <;> simp [Polynomial.coeff_C, hn]

theorem wg_eval_pderiv_X (x : σ → ℂ) (w n : σ) :
    MvPolynomial.eval x (MvPolynomial.pderiv w (MvPolynomial.X n : MvPolynomial σ ℂ)) =
      if n = w then 1 else 0 := by
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

theorem wg_pderiv_pderiv_X (w v n : σ) :
    MvPolynomial.pderiv v (MvPolynomial.pderiv w (MvPolynomial.X n : MvPolynomial σ ℂ)) = 0 := by
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs
  · exact (MvPolynomial.pderiv v).map_one_eq_zero
  · exact map_zero _

theorem wg_sum_ite_eq (S : Finset σ) (n : σ) (f : σ → ℂ) :
    ∑ w ∈ S, (if n = w then (1 : ℂ) else 0) * f w = if n ∈ S then f n else 0 := by
  simp only [ite_mul, one_mul, zero_mul]
  exact Finset.sum_ite_eq S n f

/-- **Order zero**: `Φ(F)(0) = Φ(x)`. -/
theorem wg_taylor0 (F : σ → Polynomial ℂ) (S : Finset σ) (Φ : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval (wg_restrict F S) Φ).coeff 0 = MvPolynomial.eval (wg_base F) Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp, MvPolynomial.aeval_X, wg_restrict_coeff_zero,
      map_mul, MvPolynomial.eval_X]

/-- **Order one**: `[s]Φ(F) = Σ_{w∈S} ∂_wΦ(x) [s]F_w`. -/
theorem wg_taylor1 (F : σ → Polynomial ℂ) (S : Finset σ) (Φ : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval (wg_restrict F S) Φ).coeff 1 =
      ∑ w ∈ S, MvPolynomial.eval (wg_base F) (MvPolynomial.pderiv w Φ) * (F w).coeff 1 := by
  induction Φ using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, hp, hq, ← Finset.sum_add_distrib, add_mul]
  | mul_X p n hp =>
    rw [map_mul, wg_coeff_one_mul, wg_taylor0, hp, MvPolynomial.aeval_X, wg_restrict_coeff_zero,
      wg_restrict_coeff_pos F S n one_ne_zero]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval_X, wg_eval_pderiv_X,
      add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, wg_sum_ite_eq]
    rw [Finset.sum_mul, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun w _ => by ring

/-- **Order two**: `[s²]Φ(F) = Σ_{w∈S} ∂_wΦ(x)[s²]F_w + ½Σ_{w,v∈S} ∂_v∂_wΦ(x)[s]F_w[s]F_v`. -/
theorem wg_taylor2 (F : σ → Polynomial ℂ) (S : Finset σ) (Φ : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval (wg_restrict F S) Φ).coeff 2 =
      ∑ w ∈ S, MvPolynomial.eval (wg_base F) (MvPolynomial.pderiv w Φ) * (F w).coeff 2 +
        1 / 2 * ∑ w ∈ S, ∑ v ∈ S,
          MvPolynomial.eval (wg_base F) (MvPolynomial.pderiv v (MvPolynomial.pderiv w Φ)) *
            ((F w).coeff 1 * (F v).coeff 1) := by
  induction Φ using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    rw [map_add, Polynomial.coeff_add, hp, hq]
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X p n hp =>
    rw [map_mul, wg_coeff_two_mul, wg_taylor0, wg_taylor1, hp, MvPolynomial.aeval_X,
      wg_restrict_coeff_zero, wg_restrict_coeff_pos F S n one_ne_zero,
      wg_restrict_coeff_pos F S n two_ne_zero]
    set e := MvPolynomial.eval (wg_base F)
    set c1 := fun w => (F w).coeff 1
    set c2 := fun w => (F w).coeff 2
    have hd1 : ∀ w, e (MvPolynomial.pderiv w (p * MvPolynomial.X n)) =
        e (MvPolynomial.pderiv w p) * wg_base F n + e p * (if n = w then 1 else 0) := by
      intro w
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, MvPolynomial.eval_X,
        wg_eval_pderiv_X]
    have hd2 : ∀ w v, e (MvPolynomial.pderiv v (MvPolynomial.pderiv w (p * MvPolynomial.X n))) =
        e (MvPolynomial.pderiv v (MvPolynomial.pderiv w p)) * wg_base F n +
          e (MvPolynomial.pderiv w p) * (if n = v then 1 else 0) +
          e (MvPolynomial.pderiv v p) * (if n = w then 1 else 0) := by
      intro w v
      rw [MvPolynomial.pderiv_mul, map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
        wg_pderiv_pderiv_X, mul_zero, add_zero]
      simp only [map_add, map_mul, MvPolynomial.eval_X, wg_eval_pderiv_X, e]
    simp only [hd1, hd2]
    have s1 : ∑ w ∈ S, (e (MvPolynomial.pderiv w p) * wg_base F n +
        e p * (if n = w then 1 else 0)) * c2 w =
        wg_base F n * ∑ w ∈ S, e (MvPolynomial.pderiv w p) * c2 w +
          e p * (if n ∈ S then c2 n else 0) := by
      rw [← wg_sum_ite_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => by ring
    have s2 : ∑ w ∈ S, ∑ v ∈ S, (e (MvPolynomial.pderiv v (MvPolynomial.pderiv w p)) *
          wg_base F n + e (MvPolynomial.pderiv w p) * (if n = v then 1 else 0) +
          e (MvPolynomial.pderiv v p) * (if n = w then 1 else 0)) * (c1 w * c1 v) =
        wg_base F n * ∑ w ∈ S, ∑ v ∈ S,
            e (MvPolynomial.pderiv v (MvPolynomial.pderiv w p)) * (c1 w * c1 v) +
          2 * ((∑ w ∈ S, e (MvPolynomial.pderiv w p) * c1 w) *
            (if n ∈ S then c1 n else 0)) := by
      have hA : ∀ w ∈ S, ∑ v ∈ S, e (MvPolynomial.pderiv w p) * (if n = v then 1 else 0) *
          (c1 w * c1 v) = e (MvPolynomial.pderiv w p) * c1 w * (if n ∈ S then c1 n else 0) := by
        intro w _
        rw [← wg_sum_ite_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => by ring
      have hB : ∑ w ∈ S, ∑ v ∈ S, e (MvPolynomial.pderiv v p) * (if n = w then 1 else 0) *
          (c1 w * c1 v) = (∑ v ∈ S, e (MvPolynomial.pderiv v p) * c1 v) *
            (if n ∈ S then c1 n else 0) := by
        rw [Finset.sum_comm]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← wg_sum_ite_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => by ring
      have hC : ∑ w ∈ S, ∑ v ∈ S, e (MvPolynomial.pderiv v (MvPolynomial.pderiv w p)) *
          wg_base F n * (c1 w * c1 v) = wg_base F n * ∑ w ∈ S, ∑ v ∈ S,
            e (MvPolynomial.pderiv v (MvPolynomial.pderiv w p)) * (c1 w * c1 v) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => by ring
      simp only [add_mul, Finset.sum_add_distrib]
      rw [hC, Finset.sum_congr rfl hA, hB, ← Finset.sum_mul]
      ring
    rw [s1, s2]
    ring

end BlockBand.Endpoints
