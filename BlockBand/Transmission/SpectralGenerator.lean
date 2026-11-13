module

public import BlockBand.Prelude

/-!
# Exact finite spectral transmission coefficients

For transmission eigenvalues `t_i`, the power traces `P_k = ∑_i t_i^k` (`powerTrace`), their drift
`powerDrift` and bracket `powerBracket`, written in spectral form (`powerDrift_eq_spectral`,
`powerBracket_eq_spectral`), with nonnegativity of the bracket and its quadratic forms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Transmission

open Finset

variable {ι : Type*} [Fintype ι]

/-- Unnormalized trace in an eigenbasis, including the finite zeroth power. -/
def powerTrace (t : ι → ℝ) (k : ℕ) : ℝ := ∑ i, t i ^ k

/-- Exact drift of the power traces, with the empty sum at k=1. -/
def powerDrift (D : ℝ) (t : ι → ℝ) (k : ℕ) : ℝ :=
  -(D * k / 2) * powerTrace t 1 * powerTrace t k +
    (D * k / 2) * ∑ j ∈ range k, if j = 0 then 0 else
      powerTrace t j * powerTrace t (k-j) -
        powerTrace t (j+1) * powerTrace t (k-j)

/-- The complete bracket; the final negative trace is essential. -/
def powerBracket (D : ℝ) (t : ι → ℝ) (k l : ℕ) : ℝ :=
  D * k * l * (powerTrace t (k+l) - powerTrace t (k+l+1))

/-- First-power drift has exactly the conductance coefficient -D₀/2. -/
theorem powerDrift_one (D : ℝ) (t : ι → ℝ) :
    powerDrift D t 1 = -(D / 2) * powerTrace t 1 ^ 2 := by
  simp [powerDrift]
  ring

/-- Second-power drift is D₀ P₁² - 2 D₀ P₁P₂. -/
theorem powerDrift_two (D : ℝ) (t : ι → ℝ) :
    powerDrift D t 2 = D * powerTrace t 1 ^ 2 -
      2 * D * powerTrace t 1 * powerTrace t 2 := by
  simp [powerDrift, Finset.sum_range_succ]
  ring

/-- Exact factorization of each drift summand in a finite eigenbasis. -/
theorem powerTrace_product_difference (t : ι → ℝ) (j l : ℕ) :
    powerTrace t j * powerTrace t l - powerTrace t (j+1) * powerTrace t l =
      ∑ i, ∑ m, t i ^ j * t m ^ l * (1-t i) := by
  rw [← sub_mul]
  unfold powerTrace
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [pow_succ]
  ring

/-- All-power drift expressed in exact finite spectral coordinates.
This is coefficient algebra, not a stochastic generator identification. -/
theorem powerDrift_eq_spectral (D : ℝ) (t : ι → ℝ) (k : ℕ) :
    powerDrift D t k =
      -(D * k / 2) * powerTrace t 1 * powerTrace t k +
      (D * k / 2) * ∑ j ∈ range k, if j = 0 then 0 else
        ∑ i, ∑ m, t i ^ j * t m ^ (k-j) * (1-t i) := by
  unfold powerDrift
  simp_rw [powerTrace_product_difference]

/-- Entrywise first differentials give the complete all-power bracket. -/
theorem powerBracket_eq_spectral (D : ℝ) (t : ι → ℝ) (k l : ℕ) :
    powerBracket D t k l =
      ∑ i, D * k * l * t i ^ k * t i ^ l * (1-t i) := by
  unfold powerBracket powerTrace
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add, pow_succ]
  ring

/-- On the physical spectral domain every fixed power is bounded by conductance. -/
theorem powerTrace_le_conductance (t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ powerTrace t k ∧ powerTrace t k ≤ powerTrace t 1 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => pow_nonneg (ht i).1 k
  · apply Finset.sum_le_sum
    intro i _
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hn : t i ^ n ≤ 1 := pow_le_one₀ (ht i).1 (ht i).2
    simpa [pow_add] using mul_le_mul_of_nonneg_left hn (ht i).1

/-- Complete bracket nonnegativity, with no small-channel approximation. -/
theorem powerBracket_nonneg (D : ℝ) (t : ι → ℝ)
    (hD : 0 ≤ D) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (k l : ℕ) :
    0 ≤ powerBracket D t k l := by
  rw [powerBracket_eq_spectral]
  apply Finset.sum_nonneg
  intro i _
  have hi := (ht i).1
  have hi1 := sub_nonneg.mpr (ht i).2
  positivity

/-- Full finite covariance quadratic form is a weighted sum of squares.
The test vector a is arbitrary real and its exponents k are arbitrary naturals;
no positivity/entrance/process hypotheses are used for this exact identity. -/
theorem powerBracket_quadratic {α : Type*} [Fintype α]
    (D : ℝ) (t : ι → ℝ) (k : α → ℕ) (a : α → ℝ) :
    (∑ u, ∑ v, a u * a v * powerBracket D t (k u) (k v)) =
      ∑ i, D * (1-t i) * (∑ u, a u * k u * t i ^ k u) ^ 2 := by
  simp_rw [powerBracket_eq_spectral, Finset.mul_sum]
  calc
    _ = ∑ u, ∑ i, ∑ v, a u * a v *
        (D * k u * k v * t i ^ k u * t i ^ k v * (1-t i)) := by
      apply Finset.sum_congr rfl
      intro u _
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      ring

/-- Positive semidefiniteness of every finite collection of power brackets. -/
theorem powerBracket_quadratic_nonneg {α : Type*} [Fintype α]
    (D : ℝ) (t : ι → ℝ) (k : α → ℕ) (a : α → ℝ)
    (hD : 0 ≤ D) (ht : ∀ i, t i ≤ 1) :
    0 ≤ ∑ u, ∑ v, a u * a v * powerBracket D t (k u) (k v) := by
  rw [powerBracket_quadratic]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg hD (sub_nonneg.mpr (ht i))) (sq_nonneg _)

end BlockBand.Transmission
