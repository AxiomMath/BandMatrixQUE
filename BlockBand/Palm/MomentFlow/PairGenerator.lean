module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic

/-!
# The two-variable radial generator on normalized monomials

The algebraic core of the complex moment generator: on the two
radial variables `x = X_i`, `y = X_j` the angular generator is
`c_ij {xy(∂_x - ∂_y)² + (y - x)(∂_x - ∂_y)}`, and applied to `x^a y^b/(a! b!)` it has transfer
coefficients `a(b+1)` (to `x^{a-1}y^{b+1}`) and `b(a+1)` (to `x^{a+1}y^{b-1}`).

The derivative `∂_x - ∂_y` is taken along the line `t ↦ (x + t, y - t)`: with
`g(t) = (x+t)^a (y-t)^b/(a! b!)`, `pairOperator_line` proves
`x y g''(0) + (y - x) g'(0) = a(b+1)[mono(a-1,b+1) - mono(a,b)] + b(a+1)[mono(a+1,b-1) - mono(a,b)]`.
`ℕ` subtraction in exponents is harmless because the corresponding coefficient vanishes.
No measure, no limit.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

/-- `x^a y^b / (a! b!)`. -/
def pairMono (a b : ℕ) (x y : ℝ) : ℝ := x ^ a * y ^ b / ((a.factorial : ℝ) * (b.factorial : ℝ))

/-- First line derivative of `x^a y^b` along `(1,-1)`: `a x^{a-1} y^b - b x^a y^{b-1}`. -/
def pairD1 (a b : ℕ) (x y : ℝ) : ℝ := a * x ^ (a - 1) * y ^ b - b * x ^ a * y ^ (b - 1)

/-- Second line derivative: `a(a-1)x^{a-2}y^b - 2ab x^{a-1}y^{b-1} + b(b-1)x^a y^{b-2}`. -/
def pairD2 (a b : ℕ) (x y : ℝ) : ℝ :=
  a * ((a : ℝ) - 1) * x ^ (a - 2) * y ^ b - 2 * a * b * x ^ (a - 1) * y ^ (b - 1) +
    b * ((b : ℝ) - 1) * x ^ a * y ^ (b - 2)

set_option linter.unusedSimpArgs false in
/-- **Transfer coefficients** `a(b+1)` and `b(a+1)`. -/
theorem pairOperator_mono (a b : ℕ) (x y : ℝ) :
    (x * y * pairD2 a b x y + (y - x) * pairD1 a b x y) /
        ((a.factorial : ℝ) * (b.factorial : ℝ)) =
      (a : ℝ) * ((b : ℝ) + 1) * (pairMono (a - 1) (b + 1) x y - pairMono a b x y) +
        (b : ℝ) * ((a : ℝ) + 1) * (pairMono (a + 1) (b - 1) x y - pairMono a b x y) := by
  unfold pairD1 pairD2 pairMono
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;>
    simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.zero_sub,
      Nat.sub_self, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Nat.cast_succ,
      pow_zero, pow_one, show ∀ n : ℕ, n + 1 + 1 - 2 = n from fun n => by omega,
      show ∀ n : ℕ, n + 1 + 1 - 1 = n + 1 from fun n => by omega] <;>
    field_simp <;> ring

theorem hasDerivAt_addPow (n : ℕ) (x t : ℝ) :
    HasDerivAt (fun t => (x + t) ^ n) (n * (x + t) ^ (n - 1)) t := by
  have h : HasDerivAt (fun t => x + t) 1 t := HasDerivAt.const_add x (hasDerivAt_id t)
  simpa using HasDerivAt.fun_pow h n

theorem hasDerivAt_subPow (n : ℕ) (y t : ℝ) :
    HasDerivAt (fun t => (y - t) ^ n) (n * (y - t) ^ (n - 1) * (-1)) t := by
  have h : HasDerivAt (fun t => y - t) (-1) t := HasDerivAt.const_sub y (hasDerivAt_id t)
  exact HasDerivAt.fun_pow h n

/-- `t ↦ (x+t)^a (y-t)^b` has derivative `pairD1 a b (x+t) (y-t)`. -/
theorem hasDerivAt_pairLine (a b : ℕ) (x y t : ℝ) :
    HasDerivAt (fun t => (x + t) ^ a * (y - t) ^ b) (pairD1 a b (x + t) (y - t)) t := by
  have h := HasDerivAt.fun_mul (hasDerivAt_addPow a x t) (hasDerivAt_subPow b y t)
  refine h.congr_deriv ?_
  unfold pairD1; ring

set_option linter.unusedSimpArgs false in
/-- `t ↦ pairD1 a b (x+t) (y-t)` has derivative `pairD2 a b (x+t) (y-t)`. -/
theorem hasDerivAt_pairD1Line (a b : ℕ) (x y t : ℝ) :
    HasDerivAt (fun t => pairD1 a b (x + t) (y - t)) (pairD2 a b (x + t) (y - t)) t := by
  have h1 := HasDerivAt.const_mul (a : ℝ)
    (HasDerivAt.fun_mul (hasDerivAt_addPow (a - 1) x t) (hasDerivAt_subPow b y t))
  have h2 := HasDerivAt.const_mul (b : ℝ)
    (HasDerivAt.fun_mul (hasDerivAt_addPow a x t) (hasDerivAt_subPow (b - 1) y t))
  have h := HasDerivAt.fun_sub h1 h2
  have hfun : (fun t => pairD1 a b (x + t) (y - t)) =
      (fun t => (a : ℝ) * ((x + t) ^ (a - 1) * (y - t) ^ b) -
        (b : ℝ) * ((x + t) ^ a * (y - t) ^ (b - 1))) := by
    funext s; unfold pairD1; ring
  rw [hfun]
  refine h.congr_deriv ?_
  unfold pairD2
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.zero_sub, Nat.sub_self,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, pow_zero, pow_one,
      show ∀ n : ℕ, n + 1 + 1 - 2 = n from fun n => by omega,
      show ∀ n : ℕ, n + 1 + 1 - 1 = n + 1 from fun n => by omega] <;> ring

/-- **The radial pair operator on a normalized monomial, along the line**:
for `g(t) = (x+t)^a (y-t)^b/(a!b!)`, `xy g''(0) + (y-x) g'(0)` equals the jump form with
coefficients `a(b+1)` and `b(a+1)`. -/
theorem pairOperator_line (a b : ℕ) (x y : ℝ) :
    let g : ℝ → ℝ := fun t => (x + t) ^ a * (y - t) ^ b / ((a.factorial : ℝ) * (b.factorial : ℝ))
    x * y * deriv (deriv g) 0 + (y - x) * deriv g 0 =
      (a : ℝ) * ((b : ℝ) + 1) * (pairMono (a - 1) (b + 1) x y - pairMono a b x y) +
        (b : ℝ) * ((a : ℝ) + 1) * (pairMono (a + 1) (b - 1) x y - pairMono a b x y) := by
  intro g
  set K : ℝ := (a.factorial : ℝ) * (b.factorial : ℝ)
  have hd : ∀ t, HasDerivAt g (pairD1 a b (x + t) (y - t) / K) t := fun t =>
    HasDerivAt.div_const (hasDerivAt_pairLine a b x y t) K
  have hderiv : deriv g = fun t => pairD1 a b (x + t) (y - t) / K := funext fun t => (hd t).deriv
  have hdd : deriv (deriv g) 0 = pairD2 a b x y / K := by
    rw [hderiv]
    simpa using (HasDerivAt.div_const (hasDerivAt_pairD1Line a b x y 0) K).deriv
  rw [hdd, (hd 0).deriv, ← pairOperator_mono]
  simp only [add_zero, sub_zero]
  ring

end BlockBand.Palm.MomentFlow
