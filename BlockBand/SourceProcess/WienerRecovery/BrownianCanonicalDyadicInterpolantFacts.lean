module

public import BlockBand.SourceProcess.WienerRecovery.BrownianCanonicalDyadicInterpolant

/-!
# Concrete facts for canonical Brownian dyadic interpolants

This module proves deterministic algebra for the fixed nodal-hat interpolants introduced in
`canonicalRawDyadicInterpolant`.  The results are finite-dimensional and pathwise: no
limit is taken and no probabilistic or continuity statement is used.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped ENNReal NNReal Topology BigOperators
open Filter MeasureTheory ProbabilityTheory

namespace BrownianCanonicalDyadicInterpolantFacts

open BrownianDyadicChainingClosure
open BrownianDyadicInterpolationCorrection
open BrownianCanonicalDyadicInterpolant
open ScalarWienerMeasureConstruction

def dyadicLinearHat (j : ℕ) (x : ℝ) : ℝ := max 0 (1 - |x - j|)

private theorem triHat_eq_zero_of_lt {j k : ℕ} {x : ℝ}
    (hx0 : (k : ℝ) ≤ x) (hjk : j < k) : dyadicLinearHat j x = 0 := by
  rw [dyadicLinearHat, max_eq_left]
  rw [abs_of_nonneg]
  · have h : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hjk)
    norm_num at h hx0 ⊢
    linarith
  · exact sub_nonneg.mpr (le_trans (by exact_mod_cast (Nat.le_of_lt hjk)) hx0)

private theorem triHat_eq_zero_of_succ_lt {j k : ℕ} {x : ℝ}
    (hx1 : x ≤ (k + 1 : ℕ)) (hkj : k + 1 < j) : dyadicLinearHat j x = 0 := by
  rw [dyadicLinearHat, max_eq_left]
  rw [abs_of_nonpos]
  · have h : (((k + 1) + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hkj)
    norm_num at h hx1 ⊢
    linarith
  · exact sub_nonpos.mpr (le_trans hx1 (by exact_mod_cast (Nat.le_of_lt hkj)))

private theorem triHat_eq_left {k : ℕ} {x : ℝ}
    (hx0 : (k : ℝ) ≤ x) (hx1 : x ≤ (k + 1 : ℕ)) :
    dyadicLinearHat k x = (k + 1 : ℕ) - x := by
  rw [dyadicLinearHat, abs_of_nonneg (sub_nonneg.mpr hx0), max_eq_right]
  · push_cast
    ring
  · rw [sub_nonneg]
    norm_num at hx1 ⊢
    linarith

private theorem triHat_eq_right {k : ℕ} {x : ℝ}
    (hx0 : (k : ℝ) ≤ x) (hx1 : x ≤ (k + 1 : ℕ)) :
    dyadicLinearHat (k + 1) x = x - k := by
  rw [dyadicLinearHat, abs_of_nonpos (sub_nonpos.mpr hx1), max_eq_right]
  · push_cast
    ring
  · rw [sub_nonneg]
    norm_num at hx0 ⊢
    linarith

/-- On a closed level-`n` mesh edge, every hat outside the two adjacent nodes
vanishes, and the complete nodal-hat sum is the affine combination of the adjacent
nodal values.  (At an endpoint one of those two remaining hats also vanishes.)  This
is the finite algebraic core of the canonical Brownian interpolant; `n`, the edge,
the point, and all nodal values are fixed, and no limit or probability statement
occurs. -/
theorem sum_dyadicLinearHat_smul_eq_affine
    {V : Type} [AddCommMonoid V] [Module ℝ V]
    (n k : ℕ) (hk : k < 2 ^ n) (x : ℝ)
    (hx0 : (k : ℝ) ≤ x) (hx1 : x ≤ (k + 1 : ℕ)) (v : ℕ → V) :
    (∑ j : Fin (2 ^ n + 1), dyadicLinearHat j.1 x • v j.1) =
      ((k + 1 : ℕ) - x) • v k + (x - k) • v (k + 1) := by
  classical
  let a : Fin (2 ^ n + 1) := ⟨k, by omega⟩
  let b : Fin (2 ^ n + 1) := ⟨k + 1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  rw [← Finset.sum_add_sum_compl (s := ({a, b} : Finset _))]
  have hzero : ∑ j ∈ ({a, b} : Finset (Fin (2 ^ n + 1)))ᶜ,
      dyadicLinearHat j.1 x • v j.1 = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_compl] at hj
    have hjne : j ≠ a ∧ j ≠ b := by simpa [Finset.mem_insert, Finset.mem_singleton] using hj
    have hjka : j.1 ≠ k := by
      intro h
      apply hjne.1
      apply Fin.ext
      simpa [a] using h
    have hjkb : j.1 ≠ k + 1 := by
      intro h
      apply hjne.2
      apply Fin.ext
      simpa [b] using h
    have hjval : j.1 < k ∨ k + 1 < j.1 := by omega
    rcases hjval with hlt | hgt
    · rw [triHat_eq_zero_of_lt hx0 hlt, zero_smul]
    · rw [triHat_eq_zero_of_succ_lt hx1 hgt, zero_smul]
  rw [hzero, add_zero]
  simp [hab, a, b, triHat_eq_left hx0 hx1, triHat_eq_right hx0 hx1]

end BrownianCanonicalDyadicInterpolantFacts
end BlockBand.SourceProcess.WienerRecovery.CEH
