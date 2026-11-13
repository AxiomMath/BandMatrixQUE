module

public import Mathlib

/-!
# Decomposition of a test function into block averages and centred parts

A real function `v` on `B × A`, with `A` finite and nonempty, splits as `v = v̄ + (v - v̄)`, where
`v̄(b, a) = |A|⁻¹ Σ_{a'} v(b, a')` is constant on each block `{b} × A` and `v - v̄` has zero sum on
each block. This file proves the elementary properties of this decomposition.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Foundations.FiniteBlock

open scoped BigOperators

variable {B A : Type*} [Fintype A] [Nonempty A]

/-- The average `|A|⁻¹ Σ_a v(b, a)` of `v` over the block `b`. -/
def average (v : B × A → ℝ) (b : B) : ℝ :=
  (∑ a : A, v (b, a)) / (Fintype.card A : ℝ)

/-- The block-constant part `x ↦ average v x.1`. -/
def constantPart (v : B × A → ℝ) (x : B × A) : ℝ :=
  average v x.1

/-- The centred part `v - constantPart v`, with zero sum on every block. -/
def centeredPart (v : B × A → ℝ) (x : B × A) : ℝ :=
  v x - constantPart v x

omit [Nonempty A] in
/-- `v = constantPart v + centeredPart v`. -/
theorem constant_add_centered (v : B × A → ℝ) :
    constantPart v + centeredPart v = v := by
  funext x
  simp [centeredPart]

/-- The centred part has zero sum on every block. -/
theorem sum_centered (v : B × A → ℝ) (b : B) :
    ∑ a : A, centeredPart v (b, a) = 0 := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A).ne'
  simp only [centeredPart, constantPart, average, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]
  ring

/-- Averaging a block-constant test recovers the original block value. -/
theorem average_blockConstant (f : B → ℝ) (b : B) :
    average (fun x : B × A => f x.1) b = f b := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A).ne'
  simp [average, nsmul_eq_mul, hcard]

/-- Taking the block-constant part is idempotent. -/
theorem constantPart_idempotent (v : B × A → ℝ) :
    constantPart (constantPart v) = constantPart v := by
  funext x
  exact average_blockConstant (average v) x.1

/-- A centered test has zero block average. -/
theorem average_centered (v : B × A → ℝ) (b : B) :
    average (centeredPart v) b = 0 := by
  simp [average, sum_centered]

/-- With finitely many blocks, the block-constant part has the same total sum as `v`. -/
theorem sum_constant [Fintype B] (v : B × A → ℝ) :
    ∑ x : B × A, constantPart v x = ∑ x : B × A, v x := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A).ne'
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  simp only [constantPart, average, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp [hcard]

end BlockBand.Foundations.FiniteBlock
