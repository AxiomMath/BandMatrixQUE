module

public import BlockBand.Palm.MomentFlow.MultiPerm
public import BlockBand.Palm.MomentFlow.StepsMultiSpec

/-!
# ordered matching distance versus labelled displacements

`occDist_le_of_labs` (bottleneck property of the sorted matching): if `x` labels `ξ`, `y` labels
`ζ` and every labelled displacement satisfies `|x_m - y_m| ≤ R`, then
`occDist ξ ζ ≤ r R`. Consequently (`exists_far_of_occDist`) `occDist ξ ζ > r R` forces, for
**every** labelling `y` of `ζ`, a position `m` with `|x_m - y_m| > R`.

Proof: the cumulative counts `#{particles ≤ t}` of `ξ` and `ζ` are `R`-interlaced; for sorted
lists this gives `|L_ξ[k] - L_ζ[k]| ≤ R` for every index `k`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.CoareaPalm

variable {N r : ℕ}

/-!
### Sorted lists
-/

theorem sorted_succ_le_countP {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : k < L.length) : k + 1 ≤ L.countP (fun e => decide (e ≤ L[k])) := by
  have hsub : (L.take (k + 1)).Sublist L := List.take_sublist _ _
  have h1 := hsub.countP_le (p := fun e => decide (e ≤ L[k]))
  have hlen : (L.take (k + 1)).length = k + 1 := by simp; omega
  have h2 : (L.take (k + 1)).countP (fun e => decide (e ≤ L[k])) = k + 1 := by
    rw [List.countP_eq_length.2, hlen]
    intro e he
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    simp only [List.getElem_take, decide_eq_true_eq]
    have hjk : j ≤ k := by rw [hlen] at hj; omega
    exact hL.rel_get_of_le (a := ⟨j, by omega⟩) (b := ⟨k, hk⟩) (by simpa using hjk)
  omega

theorem sorted_le_of_countP {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : k < L.length) {t : ℕ} (h : k + 1 ≤ L.countP (fun e => decide (e ≤ t))) :
    L[k] ≤ t := by
  by_contra hlt
  push Not at hlt
  have hsplit := List.countP_append (p := fun e => decide (e ≤ t)) (l₁ := L.take k)
    (l₂ := L.drop k)
  rw [List.take_append_drop] at hsplit
  have hdrop : (L.drop k).countP (fun e => decide (e ≤ t)) = 0 := by
    rw [List.countP_eq_zero]
    intro e he
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    simp only [List.getElem_drop, decide_eq_true_eq, not_le]
    have := hL.rel_get_of_le (a := ⟨k, hk⟩) (b := ⟨k + j, by simp at hj; omega⟩)
      (by simp)
    simp at this
    omega
  have htake : (L.take k).countP (fun e => decide (e ≤ t)) ≤ k :=
    (List.countP_le_length).trans (by simp)
  omega

/-!
### Cumulative counts of configurations
-/

/-- The multiset of particle labels. -/
def occBag (ξ : Occ N) : Multiset ℕ :=
  (Finset.univ : Finset (Fin N)).val.bind (fun i => Multiset.replicate (ξ i) (i : ℕ))

theorem occLabels_eq (ξ : Occ N) : occLabels ξ = (occBag ξ).sort (· ≤ ·) := rfl

/-- `#{particles of ξ at labels ≤ t}`. -/
def cumOcc (ξ : Occ N) (t : ℕ) : ℕ := ∑ i : Fin N, if (i : ℕ) ≤ t then ξ i else 0

theorem countP_occLabels (ξ : Occ N) (t : ℕ) :
    (occLabels ξ).countP (fun e => decide (e ≤ t)) = cumOcc ξ t := by
  classical
  have h1 : (occLabels ξ).countP (fun e => decide (e ≤ t)) =
      Multiset.countP (fun e => e ≤ t) (occBag ξ) := by
    rw [occLabels_eq, ← Multiset.coe_countP, Multiset.sort_eq]
  have hb : ∀ s : Multiset (Fin N), Multiset.countP (fun e => e ≤ t)
      (s.bind fun i => Multiset.replicate (ξ i) (i : ℕ)) =
      (s.map fun i : Fin N => if (i : ℕ) ≤ t then ξ i else 0).sum := by
    intro s
    induction s using Multiset.induction with
    | empty => simp
    | cons i s ih =>
      rw [Multiset.cons_bind, Multiset.countP_add, ih, Multiset.map_cons, Multiset.sum_cons]
      congr 1
      rw [← Multiset.coe_replicate, Multiset.coe_countP, List.countP_replicate]
      by_cases h : (i : ℕ) ≤ t <;> simp [h]
  rw [h1, occBag, hb]
  unfold cumOcc
  rw [Finset.sum_eq_multiset_sum]

theorem length_occLabels {ξ : Occ N} (hξ : ξ ∈ sector N r) : (occLabels ξ).length = r := by
  rw [occLabels_eq, Multiset.length_sort, occBag, Multiset.card_bind]
  rw [← mem_sector.1 hξ, Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp

theorem cumOcc_eq_card {ξ : Occ N} {x : Fin r → Fin N} (hx : x ∈ labs r ξ) (t : ℕ) :
    cumOcc ξ t = (univ.filter fun m => (x m : ℕ) ≤ t).card := by
  classical
  rw [← mem_labs.1 hx]
  unfold cumOcc
  simp only [occOf_eq_sum, Finset.card_filter]
  have : ∀ i : Fin N, (if (i : ℕ) ≤ t then ∑ m : Fin r, (if x m = i then 1 else 0) else 0) =
      ∑ m : Fin r, (if x m = i then (if (x m : ℕ) ≤ t then 1 else 0) else 0) := by
    intro i
    by_cases hi : (i : ℕ) ≤ t
    · rw [ite_eq_left hi]
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases h1 : x m = i
      · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left (by rw [h1]; exact hi)]
      · rw [ite_eq_right h1, ite_eq_right h1]
    · rw [ite_eq_right hi]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      by_cases h1 : x m = i
      · rw [ite_eq_left h1, ite_eq_right (by rw [h1]; exact hi)]
      · rw [ite_eq_right h1]
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem cumOcc_le_of_disp {ξ ζ : Occ N} {x y : Fin r → Fin N} (hx : x ∈ labs r ξ)
    (hy : y ∈ labs r ζ) {R : ℕ} (hR : ∀ m, (y m : ℕ) ≤ x m + R) (t : ℕ) :
    cumOcc ξ t ≤ cumOcc ζ (t + R) := by
  rw [cumOcc_eq_card hx, cumOcc_eq_card hy]
  refine Finset.card_le_card fun m hm => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  have := hR m; omega

/-!
### The bottleneck property
-/

theorem foldr_le_length_mul (l : List (ℕ × ℕ)) {R : ℕ}
    (h : ∀ p ∈ l, Int.natAbs ((p.1 : ℤ) - p.2) ≤ R) :
    l.foldr (fun p acc => Int.natAbs ((p.1 : ℤ) - p.2) + acc) 0 ≤ l.length * R := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldr_cons, List.length_cons]
    have h1 := h p (List.mem_cons_self)
    have h2 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    nlinarith

/-- **Bottleneck property of the sorted matching.** -/
theorem occDist_le_of_labs {ξ ζ : Occ N} {x y : Fin r → Fin N} (hx : x ∈ labs r ξ)
    (hy : y ∈ labs r ζ) {R : ℕ} (hR : ∀ m, labelDist (x m) (y m) ≤ R) :
    occDist ξ ζ ≤ r * R := by
  classical
  have hξ : ξ ∈ sector N r := mem_labs.1 hx ▸ occOf_mem_sector x
  have hζ : ζ ∈ sector N r := mem_labs.1 hy ▸ occOf_mem_sector y
  have hd : ∀ m, (y m : ℕ) ≤ x m + R ∧ (x m : ℕ) ≤ y m + R := by
    intro m; have := hR m; unfold labelDist at this; omega
  set L1 := occLabels ξ
  set L2 := occLabels ζ
  have h1 : L1.length = r := length_occLabels hξ
  have h2 : L2.length = r := length_occLabels hζ
  have hs1 : L1.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hs2 : L2.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hk : ∀ k (hk1 : k < L1.length) (hk2 : k < L2.length), L1[k] ≤ L2[k] + R ∧
      L2[k] ≤ L1[k] + R := by
    intro k hk1 hk2
    constructor
    · refine sorted_le_of_countP hs1 hk1 ?_
      rw [countP_occLabels]
      calc k + 1 ≤ L2.countP (fun e => decide (e ≤ L2[k])) := sorted_succ_le_countP hs2 hk2
        _ = cumOcc ζ L2[k] := countP_occLabels ζ _
        _ ≤ cumOcc ξ (L2[k] + R) := cumOcc_le_of_disp hy hx (fun m => (hd m).2) _
    · refine sorted_le_of_countP hs2 hk2 ?_
      rw [countP_occLabels]
      calc k + 1 ≤ L1.countP (fun e => decide (e ≤ L1[k])) := sorted_succ_le_countP hs1 hk1
        _ = cumOcc ξ L1[k] := countP_occLabels ξ _
        _ ≤ cumOcc ζ (L1[k] + R) := cumOcc_le_of_disp hx hy (fun m => (hd m).1) _
  have hz : ∀ p ∈ L1.zip L2, Int.natAbs ((p.1 : ℤ) - p.2) ≤ R := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    simp only [List.length_zip] at hj
    rw [List.getElem_zip]
    have := hk j (by omega) (by omega)
    omega
  have := foldr_le_length_mul (L1.zip L2) hz
  rw [List.length_zip, h1, h2, min_self] at this
  exact this

/-- `occDist ξ ζ > r R` forces a displacement `> R` in every labelling of `ζ`. -/
theorem exists_far_of_occDist {ξ ζ : Occ N} {x y : Fin r → Fin N} (hx : x ∈ labs r ξ)
    (hy : y ∈ labs r ζ) {R : ℝ} (hR0 : 0 ≤ R) (h : (r : ℝ) * R < (occDist ξ ζ : ℝ)) :
    ∃ m, R < (labelDist (x m) (y m) : ℝ) := by
  by_contra hno
  push Not at hno
  have hle : ∀ m, labelDist (x m) (y m) ≤ ⌊R⌋₊ := fun m => Nat.le_floor (hno m)
  have h1 := occDist_le_of_labs hx hy hle
  have h2 : ((occDist ξ ζ : ℕ) : ℝ) ≤ (r : ℝ) * (⌊R⌋₊ : ℝ) := by exact_mod_cast h1
  have h3 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0
  have h4 : (r : ℝ) * (⌊R⌋₊ : ℝ) ≤ (r : ℝ) * R :=
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg r)
  linarith

end BlockBand.Palm.MomentFlow
