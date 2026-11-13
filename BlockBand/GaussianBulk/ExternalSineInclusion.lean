module

public import Mathlib

/-!
# Finite inclusion–exclusion over ordered injective tuples

The Laplace functional of a finite point
configuration is the alternating series of its factorial correlation measures, with the
`N!/(N-k)!` (ordered injective tuple) normalization of `deformedFactorialCorrelation`.

Deterministic finite identities for an arbitrary finite index type `ι` and arbitrary real
weights `g : ι → ℝ`; no probability, measure or spectral hypothesis. `embeddingSum g k` is
`Σ_{e : Fin k ↪ ι} ∏_j g (e j)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sum over ordered injective `k`-tuples of the product of the weights. -/
def embeddingSum (g : ι → ℝ) (k : ℕ) : ℝ := ∑ e : Fin k ↪ ι, ∏ j, g (e j)

/-- Injective `k`-tuples with image `T` are the bijections `Fin k ≃ T`. -/
def embeddingImageEquiv (k : ℕ) (T : Finset ι) :
    {e : Fin k ↪ ι // univ.map e = T} ≃ (Fin k ≃ T) where
  toFun e := Equiv.ofBijective (fun j => ⟨e.1 j, by
      have h := mem_map_of_mem e.1 (mem_univ j)
      rwa [e.2] at h⟩)
    ⟨fun a b hab => e.1.injective (congrArg Subtype.val hab), fun x => by
      have hx : x.1 ∈ univ.map e.1 := by rw [e.2]; exact x.2
      obtain ⟨j, -, hj⟩ := mem_map.mp hx
      exact ⟨j, Subtype.ext hj⟩⟩
  invFun σ := ⟨σ.toEmbedding.trans (Function.Embedding.subtype _), by
    ext x
    simp only [mem_map, mem_univ, true_and, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨j, rfl⟩
      exact (σ j).2
    · intro hx
      exact ⟨σ.symm ⟨x, hx⟩, by simp⟩⟩
  left_inv e := by
    apply Subtype.ext
    ext j
    rfl
  right_inv σ := Equiv.ext fun _ => rfl

/-- The number of injective `k`-tuples with image a given `k`-set is `k!`. -/
theorem card_filter_map_eq (k : ℕ) (T : Finset ι) (hT : T.card = k) :
    (univ.filter (fun e : Fin k ↪ ι => univ.map e = T)).card = k.factorial := by
  rw [← Fintype.card_subtype, Fintype.card_congr (embeddingImageEquiv k T)]
  have e : Fin k ≃ T := Fintype.equivOfCardEq (by simp [hT])
  rw [Fintype.card_equiv e, Fintype.card_fin]

/-- The ordered injective tuple sum is `k!` times the elementary symmetric sum. -/
theorem embeddingSum_eq (g : ι → ℝ) (k : ℕ) :
    embeddingSum g k = (k.factorial : ℝ) * ∑ T ∈ powersetCard k univ, ∏ i ∈ T, g i := by
  unfold embeddingSum
  have hmap : ∀ e : Fin k ↪ ι, ∏ j, g (e j) = ∏ i ∈ univ.map e, g i := by
    intro e
    rw [prod_map]
  simp_rw [hmap]
  have hto : ∀ e ∈ (univ : Finset (Fin k ↪ ι)), univ.map e ∈ powersetCard k univ := by
    intro e _
    simp [mem_powersetCard]
  rw [← sum_fiberwise_of_maps_to hto, mul_sum]
  refine sum_congr rfl fun T hT => ?_
  have hTk : T.card = k := (mem_powersetCard.mp hT).2
  rw [sum_congr rfl (g := fun _ => ∏ i ∈ T, g i) (fun e he => by rw [(mem_filter.mp he).2]),
    sum_const, card_filter_map_eq k T hTk, nsmul_eq_mul]

/-- Inclusion–exclusion: `∏ (1 - g i)` is the alternating factorial-normalized sum of the
ordered injective tuple sums, `k = 0, …, |ι|`. -/
theorem prod_one_sub_eq_sum_embeddingSum (g : ι → ℝ) :
    ∏ i, (1 - g i) = ∑ k ∈ range (Fintype.card ι + 1),
      (-1 : ℝ) ^ k / (k.factorial : ℝ) * embeddingSum g k := by
  have h1 : ∏ i, (1 - g i) = ∏ i, (-g i + 1) := by
    refine prod_congr rfl fun i _ => ?_
    ring
  have hto : ∀ T ∈ (univ : Finset ι).powerset, T.card ∈ range (Fintype.card ι + 1) := by
    intro T _
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_univ T))
  rw [h1, prod_add, ← sum_fiberwise_of_maps_to hto]
  refine sum_congr rfl fun k _ => ?_
  have hfib : (univ : Finset ι).powerset.filter (fun T => T.card = k) = powersetCard k univ := by
    ext T
    simp [mem_powersetCard]
  rw [hfib]
  rw [embeddingSum_eq, ← mul_assoc, div_mul_cancel₀ _ (by positivity), mul_sum]
  refine sum_congr rfl fun T hT => ?_
  have hTk : T.card = k := (mem_powersetCard.mp hT).2
  rw [prod_const_one, mul_one, prod_neg, hTk]

/-- Weights in `[0,1]` vanishing off `S`: the ordered tuple sum is in
`[0, |S|.descFactorial k]` (the factorial count of `S`). -/
theorem embeddingSum_nonneg_le (g : ι → ℝ) (S : Finset ι) (h0 : ∀ i, 0 ≤ g i)
    (h1 : ∀ i, g i ≤ if i ∈ S then 1 else 0) (k : ℕ) :
    0 ≤ embeddingSum g k ∧ embeddingSum g k ≤ (S.card.descFactorial k : ℝ) := by
  constructor
  · exact sum_nonneg fun e _ => prod_nonneg fun j _ => h0 _
  · have hle : embeddingSum g k ≤ embeddingSum (fun i => if i ∈ S then (1 : ℝ) else 0) k := by
      rw [embeddingSum_eq, embeddingSum_eq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro T _
      exact Finset.prod_le_prod₀ (fun i _ => h0 i) (fun i _ => h1 i)
    refine hle.trans (le_of_eq ?_)
    have key : ∀ T : Finset ι,
        ∏ i ∈ T, (if i ∈ S then (1 : ℝ) else 0) = if T ⊆ S then 1 else 0 := by
      intro T
      split_ifs with h
      · exact prod_eq_one fun i hi => ite_eq_left (h hi)
      · obtain ⟨i, hi, hiS⟩ := not_subset.mp h
        exact prod_eq_zero hi (ite_eq_right hiS)
    rw [embeddingSum_eq]
    simp_rw [key]
    rw [sum_boole, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
      ← card_powersetCard k S]
    congr 3
    ext T
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    exact and_comm

end BlockBand.GaussianBulk
