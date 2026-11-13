module

public import BlockBand.SourceProcess.ContractingWords.Interface

/-!
# The field `summed` from the per-step bound

At each of the finitely many tag births the geometric term is restarted; its total sum then
remains `O(W⁻¹)`.

* `sum_pow_restart_le`: `Σ_{j∈S} ρ^{j - r_j} ≤ (n_T + 1)/(1 - ρ)` for any set `S` of steps
  `≥ ⌈εW⌉`: the restart `r_j` takes at most `n_T + 1` values and, per value, the sum is geometric.
* `sum_pow_sub_le`: `Σ_{j∈S, j≥r} ρ^{j-r} ≤ 1/(1-ρ)`; `restartIndex_mem_le`: for `j ≥ ⌈εW⌉` the
  restart index lies in `{⌈εW⌉} ∪ {k_a + 1}` and is `≤ j`.
* `summed_of` (proved in the sibling module): the field `summed` of `ContractingWordsEnergyUniformContract` from the hypothesis
  `SummedStep`, with constant `C(n_T + 1)/(1 - ρ) + CT`: the per-step errors
  `C W⁻¹(ρ^{j-r_j} + W^{-1/2})` over at most `TW` steps sum to
  `≤ C(n_T+1)/((1-ρ)W) + CT/√W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

theorem restartIndex_mem_le (ε : ℝ) (W : ℕ) {nT : ℕ} (k : Fin nT → ℕ) {j : ℕ}
    (hj : ⌈ε * W⌉₊ ≤ j) :
    restartIndex ε W k j ∈ insert ⌈ε * W⌉₊ (Finset.univ.image fun a => k a + 1) ∧
      restartIndex ε W k j ≤ j := by
  set F := Finset.univ.filter fun a => k a < j
  refine ⟨?_, max_le hj (Finset.sup_le fun a ha => (Finset.mem_filter.mp ha).2)⟩
  rcases le_total (F.sup fun a => k a + 1) ⌈ε * W⌉₊ with h | h
  · rw [restartIndex, max_eq_left h]; exact Finset.mem_insert_self _ _
  · rw [restartIndex, max_eq_right h]
    rcases F.eq_empty_or_nonempty with hF | hF
    · have : (F.sup fun a => k a + 1) = 0 := by rw [hF, Finset.sup_empty]; rfl
      rw [this] at h ⊢
      have h0 : ⌈ε * W⌉₊ = 0 := Nat.le_zero.mp h
      rw [← h0]; exact Finset.mem_insert_self _ _
    · obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup F hF fun a => k a + 1
      rw [ha]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a))

theorem sum_pow_sub_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (S : Finset ℕ) (r : ℕ) :
    ∑ j ∈ S.filter (r ≤ ·), ρ ^ (j - r) ≤ 1 / (1 - ρ) := by
  set S' := S.filter (r ≤ ·)
  have hinj : Set.InjOn (fun j => j - r) S' := by
    intro x hx y hy hxy
    have := (Finset.mem_filter.mp hx).2
    have := (Finset.mem_filter.mp hy).2
    simp only at hxy; omega
  rw [← Finset.sum_image (f := fun i => ρ ^ i) hinj]
  have hsub : S'.image (fun j => j - r) ⊆ Finset.range (S.sup id + 1) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have : j ≤ S.sup id := Finset.le_sup (f := id) (Finset.mem_filter.mp hj).1
    exact Finset.mem_range.mpr (by omega)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => pow_nonneg hρ0 i).trans ?_
  rw [Finset.range_eq_Ico]
  simpa using geom_sum_Ico_le_of_lt_one hρ0 hρ1 (m := 0) (n := S.sup id + 1)

/-- **Geometric terms restarted at the tag births sum to `O(1)`.** -/
theorem sum_pow_restart_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ε : ℝ) (W : ℕ) {nT : ℕ}
    (k : Fin nT → ℕ) (S : Finset ℕ) (hS : ∀ j ∈ S, ⌈ε * W⌉₊ ≤ j) :
    ∑ j ∈ S, ρ ^ (j - restartIndex ε W k j) ≤ (nT + 1) / (1 - ρ) := by
  set R := insert ⌈ε * W⌉₊ (Finset.univ.image fun a => k a + 1)
  have hR : (R.card : ℝ) ≤ nT + 1 := by
    have h1 := Finset.card_insert_le ⌈ε * W⌉₊ (Finset.univ.image fun a => k a + 1)
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin nT))) (f := fun a => k a + 1)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    exact_mod_cast (h1.trans (by omega))
  have hpt : ∀ j ∈ S, ρ ^ (j - restartIndex ε W k j) ≤
      ∑ r ∈ R, if r ≤ j then ρ ^ (j - r) else 0 := by
    intro j hj
    obtain ⟨hmem, hle⟩ := restartIndex_mem_le ε W k (hS j hj)
    have := Finset.single_le_sum (f := fun r => if r ≤ j then ρ ^ (j - r) else 0)
      (fun r _ => by split_ifs <;> positivity) hmem
    simpa [hle] using this
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_comm]
  have hinner : ∀ r ∈ R, (∑ j ∈ S, if r ≤ j then ρ ^ (j - r) else 0) ≤ 1 / (1 - ρ) := by
    intro r _
    rw [← Finset.sum_filter]; exact sum_pow_sub_le hρ0 hρ1 S r
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  exact div_le_div_of_nonneg_right hR (by linarith)

end BlockBand.SourceProcess.ContractingWords
