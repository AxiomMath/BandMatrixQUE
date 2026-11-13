module

public import Mathlib.Tactic

/-!
# Finite block-mass profile functional

This is the pointwise finite component of the first and last steps of the joint
recovery theorem.  For nonnegative block masses with sum one, spatial readback is a positive
unit-mass linear functional and is Lipschitz in the uniform test bound.
The finite index set is arbitrary, so both ring parities are allowed.
No Gaussian measure, eigenvector construction, determinant derivative
identity, infinite mark reconstruction or convergence is assumed or proved.
To apply it, these masses are identified with squared block norms of
a normalized physical eigenvector.
-/

set_option autoImplicit false
@[expose] public section
open scoped BigOperators
namespace BlockBand.Critical

/-- The exact finite block-mass functional, without a change of measure. -/
def finiteProfileValue {ι : Type*} (s : Finset ι) (p q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, p i * q i

/-- A nonnegative test has nonnegative profile readback. -/
theorem finiteProfileValue_nonneg {ι : Type*} (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i) :
    0 ≤ finiteProfileValue s p q :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hp i hi) (hq i hi))

/-- Unit test reads exactly one from a unit-mass profile. -/
theorem finiteProfileValue_one {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∑ i ∈ s, p i = 1) : finiteProfileValue s p (fun _ => 1) = 1 := by
  simpa [finiteProfileValue] using hp

/-- Additivity in the test function. -/
theorem finiteProfileValue_add {ι : Type*} (s : Finset ι) (p q r : ι → ℝ) :
    finiteProfileValue s p (fun i => q i+r i) =
      finiteProfileValue s p q + finiteProfileValue s p r := by
  simp only [finiteProfileValue, mul_add, Finset.sum_add_distrib]

/-- Pointwise finite uniform-test contraction. The bound `M` is the supplied
uniform norm bound on the difference, and no model-dependent constant occurs. -/
theorem abs_finiteProfileValue_sub_le {ι : Type*} (s : Finset ι)
    (p q r : ι → ℝ) (M : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hmass : ∑ i ∈ s, p i = 1)
    (hqr : ∀ i ∈ s, |q i-r i| ≤ M) :
    |finiteProfileValue s p q - finiteProfileValue s p r| ≤ M := by
  calc
    |finiteProfileValue s p q - finiteProfileValue s p r| =
        |∑ i ∈ s, p i * (q i-r i)| := by
      simp only [finiteProfileValue, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ s, |p i * (q i-r i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, p i * |q i-r i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hp i hi)]
    _ ≤ ∑ i ∈ s, p i * M := by
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hqr i hi) (hp i hi))
    _ = M := by rw [← Finset.sum_mul, hmass, one_mul]

end BlockBand.Critical
