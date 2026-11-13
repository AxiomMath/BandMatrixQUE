module
public import BlockBand.QUE.FiniteTestBounds
public import BlockBand.QUE.PhysicalAdapter
public import Mathlib.Tactic
/-!
# Finite QUE reductions

Deterministic reductions of the QUE bound: Young absorption of the mode estimate, summation of
the Fourier modes under diagonalization and Parseval bounds, and the assembly with the Haar
residual `1/(W+1)`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Fourier
open scoped BigOperators

/-- Young absorption retaining both the linear error and squared mixed error. -/
theorem young_mode_bound (d γ a b : ℝ) (hd : 0 < d) (hγ : 0 ≤ γ)
    (h : d / 2 * γ ≤ a + b * Real.sqrt γ) :
    γ ≤ 4 * a / d + 4 * b ^ 2 / d ^ 2 := by
  have hs := Real.sq_sqrt hγ
  have hsq := sq_nonneg (d * Real.sqrt γ - 2 * b)
  have hh := mul_le_mul_of_nonneg_left h hd.le
  have hb : γ ≤ (4 * a * d + 4 * b ^ 2) / d ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hd)).2
    nlinarith
  calc
    γ ≤ (4 * a * d + 4 * b ^ 2) / d ^ 2 := hb
    _ = 4 * a / d + 4 * b ^ 2 / d ^ 2 := by
      field_simp

/-- Finite Fourier summation under diagonalization and Parseval bounds; `Q` is the expectation for
one fixed test. -/
theorem finite_test_bound {ι : Type*} [Fintype ι]
    (weights γ : ι → ℝ) (Q C : ℝ)
    (hw : ∀ m, 0 ≤ weights m) (hs : ∑ m, weights m ≤ 1)
    (hC : 0 ≤ C) (hγ : ∀ m, γ m ≤ C)
    (hQ : Q = ∑ m, weights m * γ m) : Q ≤ C := by
  rw [hQ]
  calc
    (∑ m, weights m * γ m) ≤ ∑ m, weights m * C := by
      exact Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (hγ m) (hw m))
    _ = (∑ m, weights m) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ C := by simpa using mul_le_mul_of_nonneg_right hs hC

/-- Assembly with the residual `1/(W+1)`, given a Haar bridge bound as a hypothesis. -/
theorem site_test_bound (W : ℕ) (Q block residual C : ℝ)
    (hbridge : Q = block + residual) (hblock : block ≤ C)
    (hresidual : residual ≤ 1 / ((W : ℝ) + 1)) :
    Q ≤ C + 1 / ((W : ℝ) + 1) := by
  rw [hbridge]
  exact add_le_add hblock hresidual
end BlockBand.QUE.Fourier
