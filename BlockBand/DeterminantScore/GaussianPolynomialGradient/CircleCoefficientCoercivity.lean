module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Polynomial.Fourier
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Coefficient coercivity of linear-factor quotients

For a complex polynomial `A` and a root `z`, the coefficients of the quotient of `A` by `X - z`
are bounded by those of `A`, uniformly in `z`; consequently the values of the quotient on the unit
circle are bounded by a degree-only multiple of the normalized circle `L²` mass of the product
(`eval_sq_le_actual_circle_mass`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.GaussianGradient
open Polynomial
open scoped BigOperators

/-- Descending finite recurrence, with terminal coefficient zero. -/
theorem backward_sum_bound (a b : ℕ → ℝ)
    (hstep : ∀ j, a j ≤ b (j + 1) + a (j + 1))
    (n j : ℕ) (hend : a (j + n) = 0) :
    a j ≤ ∑ r ∈ Finset.range n, b (j + r + 1) := by
  induction n generalizing j with
  | zero => simpa using le_of_eq hend
  | succ n ih =>
    have ht : a ((j + 1) + n) = 0 := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend
    calc
      a j ≤ b (j + 1) + a (j + 1) := hstep j
      _ ≤ b (j + 1) + ∑ r ∈ Finset.range n, b ((j + 1) + r + 1) := add_le_add le_rfl (ih (j + 1) ht)
      _ = ∑ r ∈ Finset.range (n + 1), b (j + r + 1) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.add_left_comm, add_comm]

/-- Ascending finite recurrence, including the constant coefficient. -/
theorem forward_sum_bound (a b : ℕ → ℝ)
    (hzero : a 0 ≤ b 0)
    (hstep : ∀ j, a (j + 1) ≤ b (j + 1) + a j) (j : ℕ) :
    a j ≤ ∑ r ∈ Finset.range (j + 1), b r := by
  induction j with
  | zero => simpa using hzero
  | succ j ih =>
    calc
      a (j + 1) ≤ b (j + 1) + a j := hstep j
      _ ≤ b (j + 1) + ∑ r ∈ Finset.range (j + 1), b r := add_le_add le_rfl ih
      _ = ∑ r ∈ Finset.range (j + 1 + 1), b r := by
        rw [Finset.sum_range_succ (n := j + 1)]
        exact add_comm _ _

/-- Every coefficient of a linear-factor quotient is controlled by the upper coefficient tail of
the product when the root is in the unit disk. -/
theorem coeff_norm_le_backward_tail (A : Polynomial ℂ) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (n j : ℕ) (hend : A.coeff (j + n) = 0) :
    ‖A.coeff j‖ ≤ ∑ r ∈ Finset.range n,
      ‖(((X - C z) * A).coeff (j + r + 1))‖ := by
  refine backward_sum_bound (fun l => ‖A.coeff l‖)
    (fun l => ‖((X - C z) * A).coeff l‖) ?_ n j ?_
  · intro l
    have heq : A.coeff l = ((X - C z) * A).coeff (l + 1) + z * A.coeff (l + 1) := by
      rw [coeff_X_sub_C_mul]
      ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have hm : ‖z‖ * ‖A.coeff (l + 1)‖ ≤ ‖A.coeff (l + 1)‖ := by
      nlinarith [norm_nonneg (A.coeff (l + 1))]
    exact add_le_add le_rfl hm
  · simp [hend]

/-- Every coefficient of a linear-factor quotient is controlled by the lower coefficient prefix of
the product when the root is outside the unit disk. -/
theorem coeff_norm_le_forward_prefix (A : Polynomial ℂ) (z : ℂ)
    (hz : 1 ≤ ‖z‖) (j : ℕ) :
    ‖A.coeff j‖ ≤ ∑ r ∈ Finset.range (j + 1),
      ‖(((X - C z) * A).coeff r)‖ := by
  refine forward_sum_bound (fun l => ‖A.coeff l‖)
    (fun l => ‖((X - C z) * A).coeff l‖) ?_ ?_ j
  · have hb : ((X - C z) * A).coeff 0 = -(z * A.coeff 0) := by simp [sub_mul]
    rw [hb, norm_neg, norm_mul]
    nlinarith [norm_nonneg (A.coeff 0)]
  · intro l
    have hb : z * A.coeff (l + 1) = A.coeff l - ((X - C z) * A).coeff (l + 1) := by
      rw [coeff_X_sub_C_mul]
      ring
    have hnorm : ‖z‖ * ‖A.coeff (l + 1)‖ ≤
        ‖A.coeff l‖ + ‖((X - C z) * A).coeff (l + 1)‖ := by
      rw [← norm_mul, hb]
      exact norm_sub_le _ _
    nlinarith [norm_nonneg (A.coeff (l + 1))]

/-- Coefficient-uniform linear-factor coercivity. The root is any complex number, and the only
restriction is on the quotient degree. -/
theorem coeff_norm_le_product_l1 (A : Polynomial ℂ) (z : ℂ) (m j : ℕ)
    (hdeg : A.natDegree ≤ m) (hj : j ≤ m) :
    ‖A.coeff j‖ ≤ ∑ r ∈ Finset.range (m + 2), ‖((X - C z) * A).coeff r‖ := by
  by_cases hz : ‖z‖ ≤ 1
  · have hend : A.coeff (j + (m + 1 - j)) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      omega
    have hb := coeff_norm_le_backward_tail A z hz (m + 1 - j) j hend
    refine hb.trans ?_
    apply Finset.sum_le_sum_of_injOn (fun r : ℕ => j + r + 1)
    · intro a ha b hb hab
      dsimp at hab
      omega
    · intro l hl
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hl
      simp only [Finset.mem_range] at hr ⊢
      omega
    · intro r hr
      exact le_rfl
    · intro r hr hnot
      exact norm_nonneg _
  · refine (coeff_norm_le_forward_prefix A z (le_of_not_ge hz) j).trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro r hr hnot
    exact norm_nonneg _

/-- Each quotient coefficient square is bounded by a degree-only multiple of all coefficient
squares of the linear-factor product. -/
theorem coeff_sq_le_product_mass (A : Polynomial ℂ) (z : ℂ) (m j : ℕ)
    (hdeg : A.natDegree ≤ m) (hj : j ≤ m) :
    ‖A.coeff j‖ ^ 2 ≤ (m + 2 : ℝ) *
      ∑ r ∈ Finset.range (m + 2), ‖((X - C z) * A).coeff r‖ ^ 2 := by
  have hb := coeff_norm_le_product_l1 A z m j hdeg hj
  have hs : 0 ≤ ∑ r ∈ Finset.range (m + 2), ‖((X - C z) * A).coeff r‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    ‖A.coeff j‖ ^ 2 ≤ (∑ r ∈ Finset.range (m + 2), ‖((X - C z) * A).coeff r‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hs).2 hb
    _ ≤ _ := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 2))
        (f := fun r => ‖((X - C z) * A).coeff r‖)

/-- The squared coefficient norm of the quotient is bounded, uniformly in the root, by that of the
product with a linear factor. -/
theorem coefficient_mass_le_product_mass (A : Polynomial ℂ) (z : ℂ) (m : ℕ)
    (hdeg : A.natDegree ≤ m) :
    (∑ j ∈ Finset.range (m + 1), ‖A.coeff j‖ ^ 2) ≤
      (m + 1 : ℝ) * (m + 2 : ℝ) *
        ∑ r ∈ Finset.range (m + 2), ‖((X - C z) * A).coeff r‖ ^ 2 := by
  calc
    (∑ j ∈ Finset.range (m + 1), ‖A.coeff j‖ ^ 2) ≤
        ∑ _j ∈ Finset.range (m + 1), (m + 2 : ℝ) *
          ∑ r ∈ Finset.range (m + 2), ‖((X - C z) * A).coeff r‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact coeff_sq_le_product_mass A z m j hdeg (by simpa using hj)
    _ = _ := by simp; ring

/-- Pointwise unit-circle evaluation is controlled by coefficient mass. -/
theorem eval_sq_le_coefficient_mass (A : Polynomial ℂ) (m : ℕ)
    (hdeg : A.natDegree ≤ m) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖A.eval w‖ ^ 2 ≤ (m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1), ‖A.coeff j‖ ^ 2 := by
  have he : A.eval w = ∑ j ∈ Finset.range (m + 1), A.coeff j * w ^ j :=
    eval_eq_sum_range' (by omega) w
  have hn : ‖A.eval w‖ ≤ ∑ j ∈ Finset.range (m + 1), ‖A.coeff j‖ := by
    rw [he]
    calc
      ‖∑ j ∈ Finset.range (m + 1), A.coeff j * w ^ j‖ ≤
          ∑ j ∈ Finset.range (m + 1), ‖A.coeff j * w ^ j‖ := norm_sum_le _ _
      _ = _ := by simp [norm_pow, hw]
  have hs : 0 ≤ ∑ j ∈ Finset.range (m + 1), ‖A.coeff j‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hc : (∑ j ∈ Finset.range (m + 1), ‖A.coeff j‖) ^ 2 ≤
      (m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1), ‖A.coeff j‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1))
      (f := fun j => ‖A.coeff j‖)
  exact ((sq_le_sq₀ (norm_nonneg _) hs).2 hn).trans hc

/-- Uniform unit-circle quotient bound for every complex root. -/
theorem eval_sq_le_product_mass (A : Polynomial ℂ) (z : ℂ) (m : ℕ)
    (hdeg : A.natDegree ≤ m) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖A.eval w‖ ^ 2 ≤ (m + 1 : ℝ) ^ 2 * (m + 2 : ℝ) *
      ∑ r ∈ Finset.range (m + 2), ‖((X - C z) * A).coeff r‖ ^ 2 := by
  calc
    ‖A.eval w‖ ^ 2 ≤ (m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1), ‖A.coeff j‖ ^ 2 :=
      eval_sq_le_coefficient_mass A m hdeg w hw
    _ ≤ (m + 1 : ℝ) * ((m + 1 : ℝ) * (m + 2 : ℝ) *
        ∑ r ∈ Finset.range (m + 2), ‖((X - C z) * A).coeff r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (coefficient_mass_le_product_mass A z m hdeg) (by positivity)
    _ = _ := by ring

/-- The finite coefficient mass is the normalized circle `L²` mass. -/
theorem sum_coeff_sq_eq_circleAverage (B : Polynomial ℂ) (n : ℕ)
    (hdeg : B.natDegree < n) :
    (∑ r ∈ Finset.range n, ‖B.coeff r‖ ^ 2) =
      Real.circleAverage (fun w => ‖B.eval w‖ ^ 2) 0 1 := by
  calc
    (∑ r ∈ Finset.range n, ‖B.coeff r‖ ^ 2) = B.sum (fun _ a => ‖a‖ ^ 2) :=
      (B.sum_over_range' (f := fun _ a => ‖a‖ ^ 2) (fun _ => by simp) n hdeg).symm
    _ = ∑ r ∈ B.support, ‖B.coeff r‖ ^ 2 := rfl
    _ = _ := B.sum_sq_norm_coeff_eq_circleAverage

/-- The linear-factor quotient bound against the normalized circle `L²` mass, uniformly for every
complex root and every point of the unit circle. -/
theorem eval_sq_le_actual_circle_mass (A : Polynomial ℂ) (z : ℂ) (m : ℕ)
    (hdeg : A.natDegree ≤ m) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖A.eval w‖ ^ 2 ≤ (m + 1 : ℝ) ^ 2 * (m + 2 : ℝ) *
      Real.circleAverage (fun u => ‖(((X - C z) * A).eval u)‖ ^ 2) 0 1 := by
  have hprod : ((X - C z) * A).natDegree < m + 2 := by
    have hm := natDegree_mul_le (p := X - C z) (q := A)
    simp only [natDegree_X_sub_C] at hm
    omega
  have h := eval_sq_le_product_mass A z m hdeg w hw
  rw [sum_coeff_sq_eq_circleAverage _ _ hprod] at h
  exact h

end BlockBand.DeterminantScore.GaussianGradient
