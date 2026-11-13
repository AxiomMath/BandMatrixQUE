module

public import BlockBand.Critical.RelativeVectors.Abel
public import BlockBand.Internal.Contracts.CoareaPalm
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Label-distance sums

Elementary. With `d(i) = labelDist i j`:
* `sum_labelDist_le`: `Σ_{d(i) ≥ ℓ} f(d(i)) ≤ 2 Σ_{k ∈ [ℓ, N]} f(k)` for `f ≥ 0` (each distance has
  at most two labels);
* `sum_inv_sq_le`: `Σ_{k ∈ [ℓ, N]} 1/k² ≤ 2/ℓ` (`ℓ ≥ 1`); `sum_inv_le`: `Σ_{k ∈ [ℓ, N]} 1/k ≤
  1 + log N` (`ℓ ≥ 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Finset
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem card_fiber_labelDist_le (j : Fin N) (k : ℕ) (s : Finset (Fin N)) :
    (s.filter (fun i => labelDist i j = k)).card ≤ 2 := by
  have h : (s.filter (fun i => labelDist i j = k)).card ≤ ({(k : ℤ), -(k : ℤ)} : Finset ℤ).card := by
    refine card_le_card_of_injOn (fun i => (i : ℤ) - (j : ℤ)) ?_ ?_
    · intro i hi
      have hi' := (mem_filter.1 hi).2
      unfold labelDist at hi'
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases Int.natAbs_eq ((i : ℤ) - (j : ℤ)) with h | h
      · left; rw [h, hi']
      · right; rw [h, hi']
    · intro i _ i' _ hii
      simp only at hii
      exact Fin.ext (by omega)
  exact h.trans (card_insert_le _ _)

theorem labelDist_lt (i j : Fin N) : labelDist i j < N := by
  unfold labelDist; have := i.isLt; have := j.isLt; omega

theorem sum_labelDist_le (j : Fin N) (ℓ : ℕ) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ i ∈ univ.filter (fun i : Fin N => ℓ ≤ labelDist i j), f (labelDist i j) ≤
      2 * ∑ k ∈ Icc ℓ N, f k := by
  set s := univ.filter (fun i : Fin N => ℓ ≤ labelDist i j)
  have hmaps : ∀ i ∈ s, labelDist i j ∈ Icc ℓ N := fun i hi =>
    mem_Icc.2 ⟨(mem_filter.1 hi).2, (labelDist_lt i j).le⟩
  rw [← sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine sum_le_sum fun k _ => ?_
  have e : ∑ i ∈ s with labelDist i j = k, f (labelDist i j) =
      ∑ i ∈ s with labelDist i j = k, f k :=
    sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]
  rw [e, sum_const, nsmul_eq_mul]
  have := card_fiber_labelDist_le j k s
  have : ((s.filter (fun i => labelDist i j = k)).card : ℝ) ≤ 2 := by exact_mod_cast this
  nlinarith [hf k]

theorem sum_Ico_inv_sq_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (n : ℕ) :
    ∑ k ∈ Ico ℓ (ℓ + n), (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / ℓ - 2 / (ℓ + n : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ℓ + (n + 1) = (ℓ + n) + 1 by ring, sum_Ico_succ_top (by omega)]
    have hm : (1 : ℝ) ≤ (ℓ + n : ℕ) := by exact_mod_cast (show 1 ≤ ℓ + n by omega)
    set m : ℝ := ((ℓ + n : ℕ) : ℝ)
    have hstep : (1 : ℝ) / m ^ 2 ≤ 2 / m - 2 / ((ℓ + n + 1 : ℕ) : ℝ) := by
      push_cast
      rw [show ((ℓ : ℝ) + n + 1) = m + 1 by simp [m]]
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

theorem sum_inv_sq_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (N : ℕ) :
    ∑ k ∈ Icc ℓ N, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / ℓ := by
  have hsub : Icc ℓ N ⊆ Ico ℓ (ℓ + N) := by
    intro k hk; rw [mem_Icc] at hk; rw [mem_Ico]; omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity).trans ?_
  refine (sum_Ico_inv_sq_le hℓ N).trans ?_
  have : (0 : ℝ) ≤ 2 / ((ℓ + N : ℕ) : ℝ) := by positivity
  linarith

theorem sum_inv_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (N : ℕ) :
    ∑ k ∈ Icc ℓ N, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log N := by
  have hsub : Icc ℓ N ⊆ Icc 1 N := by
    intro k hk; rw [mem_Icc] at hk ⊢; omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity).trans ?_
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

end BlockBand.Critical.RelativeVectors
