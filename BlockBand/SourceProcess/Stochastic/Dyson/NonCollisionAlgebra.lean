module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.BigOperators

/-!
# The log-Vandermonde drift identity

For pairwise distinct reals `l_i` and `x_ij = (l_i - l_j)⁻¹`, `S_i = ∑_{k ≠ i} x_ik`:
* `sum_sq_rowSum`: `∑_i S_i² = ∑_{i ≠ j} x_ij²` (the three-term identity
  `x_ij x_ik + x_jk x_ji + x_ki x_kj = 0` for distinct `i, j, k`);
* `lyap_drift_identity`: `∑_{i ≠ j} (x_ij (2S_i - 2S_j) - 2 x_ij²) = 2 ∑_{i ≠ j} x_ij²`.
The second is the cancellation which makes the Itô drift of `∑_{i ≠ j} log|λ_i - λ_j|` under
β = 2 Dyson dynamics equal to `(1/N) ∑_{i ≠ j} (λ_i - λ_j)⁻² ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Finset

variable {N : ℕ}

/-- `x_ij = (l_i - l_j)⁻¹` (zero on the diagonal). -/
def pinv (l : Fin N → ℝ) (i j : Fin N) : ℝ := (l i - l j)⁻¹

/-- `S_i = ∑_{k ≠ i} x_ik`. -/
def rowSum (l : Fin N → ℝ) (i : Fin N) : ℝ := ∑ k ∈ univ.erase i, pinv l i k

theorem pinv_self (l : Fin N → ℝ) (i : Fin N) : pinv l i i = 0 := by simp [pinv]

theorem pinv_swap (l : Fin N → ℝ) (i j : Fin N) : pinv l j i = -pinv l i j := by
  simp only [pinv]; rw [← inv_neg, neg_sub]

theorem rowSum_eq (l : Fin N → ℝ) (i : Fin N) : rowSum l i = ∑ k, pinv l i k :=
  sum_erase _ (pinv_self l i)

theorem sum_erase_eq_sum {f : Fin N → Fin N → ℝ} (hf : ∀ i, f i i = 0) :
    ∑ i, ∑ j ∈ univ.erase i, f i j = ∑ i, ∑ j, f i j :=
  sum_congr rfl fun i _ => sum_erase _ (hf i)

/-- The three-term identity, with the off-diagonal convention. -/
theorem cyclic_zero {l : Fin N → ℝ} (hl : Function.Injective l) (i j k : Fin N) :
    (if j = k then 0 else pinv l i j * pinv l i k) +
      (if k = i then 0 else pinv l j k * pinv l j i) +
      (if i = j then 0 else pinv l k i * pinv l k j) = 0 := by
  by_cases hjk : j = k
  · subst hjk; simp [pinv_self]
  by_cases hki : k = i
  · subst hki; simp [pinv_self]
  by_cases hij : i = j
  · subst hij; simp [pinv_self]
  simp only [hjk, hki, hij, ite_false, pinv]
  have h1 : l i - l j ≠ 0 := sub_ne_zero.mpr (hl.ne hij)
  have h2 : l j - l k ≠ 0 := sub_ne_zero.mpr (hl.ne hjk)
  have h3 : l k - l i ≠ 0 := sub_ne_zero.mpr (hl.ne hki)
  have h4 : l i - l k ≠ 0 := sub_ne_zero.mpr (hl.ne (Ne.symm hki))
  have h5 : l j - l i ≠ 0 := sub_ne_zero.mpr (hl.ne (Ne.symm hij))
  have h6 : l k - l j ≠ 0 := sub_ne_zero.mpr (hl.ne (Ne.symm hjk))
  field_simp
  ring

/-- `∑_i S_i² = ∑_{i,j} x_ij²`. -/
theorem sum_sq_rowSum {l : Fin N → ℝ} (hl : Function.Injective l) :
    ∑ i, rowSum l i ^ 2 = ∑ i, ∑ j, pinv l i j ^ 2 := by
  set g : Fin N → Fin N → Fin N → ℝ := fun i j k => if j = k then 0 else pinv l i j * pinv l i k
  have hsplit : ∀ i, rowSum l i ^ 2 = ∑ j, pinv l i j ^ 2 + ∑ j, ∑ k, g i j k := by
    intro i
    rw [rowSum_eq, sq, sum_mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← add_sum_erase _ _ (mem_univ j), ← sum_erase _ (show g i j j = 0 by simp [g]), sq]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    simp [g, Ne.symm (ne_of_mem_erase hk)]
  have hrot1 : ∑ i, ∑ j, ∑ k, g j k i = ∑ i, ∑ j, ∑ k, g i j k := by
    rw [sum_comm]; exact sum_congr rfl fun j _ => sum_comm
  have hrot2 : ∑ i, ∑ j, ∑ k, g k i j = ∑ i, ∑ j, ∑ k, g i j k := by
    rw [show (∑ i, ∑ j, ∑ k, g k i j) = ∑ i, ∑ k, ∑ j, g k i j from
      sum_congr rfl fun i _ => sum_comm, sum_comm]
  have hT : ∑ i, ∑ j, ∑ k, g i j k = 0 := by
    have h3 : ∑ i, ∑ j, ∑ k, (g i j k + g j k i + g k i j) = 0 := by
      simp only [g, cyclic_zero hl, sum_const_zero]
    simp only [sum_add_distrib, hrot1, hrot2] at h3
    linarith
  simp only [hsplit, sum_add_distrib, hT, add_zero]

/-- **The log-Vandermonde drift identity.** -/
theorem lyap_drift_identity {l : Fin N → ℝ} (hl : Function.Injective l) :
    ∑ i, ∑ j ∈ univ.erase i, (pinv l i j * (2 * rowSum l i - 2 * rowSum l j) -
        pinv l i j ^ 2 * 2) = 2 * ∑ i, ∑ j ∈ univ.erase i, pinv l i j ^ 2 := by
  rw [sum_erase_eq_sum (f := fun i j => pinv l i j * (2 * rowSum l i - 2 * rowSum l j) -
      pinv l i j ^ 2 * 2) (fun i => by simp [pinv_self]),
    sum_erase_eq_sum (f := fun i j => pinv l i j ^ 2) (fun i => by simp [pinv_self])]
  have hA : ∑ i, ∑ j, pinv l i j * rowSum l i = ∑ i, rowSum l i ^ 2 := by
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_mul, ← rowSum_eq, sq]
  have hB : ∑ i, ∑ j, pinv l i j * rowSum l j = -∑ j, rowSum l j ^ 2 := by
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_mul]
    simp_rw [pinv_swap l j]
    rw [sum_neg_distrib, ← rowSum_eq, neg_mul, sq]
  have hC := sum_sq_rowSum hl
  have e : ∀ i j, pinv l i j * (2 * rowSum l i - 2 * rowSum l j) - pinv l i j ^ 2 * 2 =
      2 * (pinv l i j * rowSum l i) - 2 * (pinv l i j * rowSum l j) - 2 * pinv l i j ^ 2 := by
    intro i j; ring
  simp only [e, sum_sub_distrib, ← mul_sum, hA, hB]
  rw [hC]
  ring

end BlockBand.SourceProcess.Stochastic.Dyson
