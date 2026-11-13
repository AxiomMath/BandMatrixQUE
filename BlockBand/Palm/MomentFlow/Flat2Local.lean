module

public import BlockBand.Palm.MomentFlow.Flat2Ramp

/-!
# Local and global flattening commutator, and the ramp under one jump

* `le_rampDist`, `rampDist_le`, `mem_occLabels`: `rampDist k₀ ξ` is the maximum of `|k - k₀|`
  over the occupied labels `k` of `ξ`.
* **`abs_rampDist_move_sub_le`**: `|rampDist(ξ^{i,j}) - rampDist(ξ)| ≤ |i - j|` (`ξ_i > 0`).
* `flat_commutator_eq`: `Σ w (a f + 1 - a) - (a(ξ) Σ w f + 1 - a(ξ)) = Σ w (a - a(ξ))(f - 1)` for a
  probability row.
* **`flat2_commutator_local`**: the bound `(M_loc + 1)·2rR/wd + (M + 1)·tail`, with the local
  bound `|f| ≤ M_loc` required only on `{ζ ∈ occBall r R ξ : a(ζ) ≠ a(ξ)}` and the global `M` only
  multiplying the finite-speed tail.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem le_listMaxDist (k₀ : ℕ) :
    ∀ L : List ℕ, ∀ x ∈ L, Int.natAbs ((x : ℤ) - k₀) ≤ listMaxDist k₀ L
  | [], x, hx => by simp at hx
  | y :: L, x, hx => by
    simp only [listMaxDist, List.foldr_cons] at *
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (le_listMaxDist k₀ L x hx).trans (le_max_right _ _)

theorem listMaxDist_le (k₀ M : ℕ) :
    ∀ L : List ℕ, (∀ x ∈ L, Int.natAbs ((x : ℤ) - k₀) ≤ M) → listMaxDist k₀ L ≤ M
  | [], _ => by simp [listMaxDist]
  | y :: L, h => by
    simp only [listMaxDist, List.foldr_cons]
    exact max_le (h y (by simp)) (listMaxDist_le k₀ M L fun x hx => h x (by simp [hx]))

theorem mem_occLabels {ξ : Occ N} {x : ℕ} : x ∈ occLabels ξ ↔ ∃ k : Fin N, 0 < ξ k ∧ (k : ℕ) = x := by
  unfold occLabels
  rw [Multiset.mem_sort, Multiset.mem_bind]
  constructor
  · rintro ⟨k, -, hk⟩
    obtain ⟨h1, h2⟩ := Multiset.mem_replicate.1 hk
    exact ⟨k, Nat.pos_of_ne_zero h1, h2.symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_univ_val _, Multiset.mem_replicate.2 ⟨hk.ne', rfl⟩⟩

theorem le_rampDist (k₀ : ℕ) {ξ : Occ N} {k : Fin N} (hk : 0 < ξ k) :
    Int.natAbs ((k : ℤ) - k₀) ≤ rampDist k₀ ξ :=
  le_listMaxDist k₀ _ _ (mem_occLabels.2 ⟨k, hk, rfl⟩)

theorem rampDist_le (k₀ M : ℕ) {ξ : Occ N}
    (h : ∀ k : Fin N, 0 < ξ k → Int.natAbs ((k : ℤ) - k₀) ≤ M) : rampDist k₀ ξ ≤ M :=
  listMaxDist_le k₀ M _ fun x hx => by
    obtain ⟨k, hk, rfl⟩ := mem_occLabels.1 hx
    exact h k hk

theorem rampDist_move_le (k₀ : ℕ) {ξ : Occ N} {i j : Fin N} (hi : 0 < ξ i) (hij : i ≠ j) :
    rampDist k₀ (move ξ i j) ≤ rampDist k₀ ξ + labelDist i j := by
  refine rampDist_le k₀ _ fun k hk => ?_
  by_cases hkj : k = j
  · subst hkj
    have := le_rampDist k₀ (ξ := ξ) hi
    unfold labelDist; omega
  · by_cases hki : k = i
    · subst hki
      have := le_rampDist k₀ (ξ := ξ) hi
      omega
    · rw [move_apply_of_ne ξ hki hkj] at hk
      exact (le_rampDist k₀ hk).trans (Nat.le_add_right _ _)

/-- One jump `ξ ↦ ξ^{i,j}` moves the ramp distance by at most `|i - j|`. -/
theorem abs_rampDist_move_sub_le (k₀ : ℕ) {ξ : Occ N} {i j : Fin N} (hi : 0 < ξ i) (hij : i ≠ j) :
    |(rampDist k₀ (move ξ i j) : ℝ) - rampDist k₀ ξ| ≤ labelDist i j := by
  have h1 := rampDist_move_le k₀ hi hij
  have h2 : rampDist k₀ ξ ≤ rampDist k₀ (move ξ i j) + labelDist i j := by
    have hj : 0 < move ξ i j j := by rw [move_apply_target]; omega
    refine rampDist_le k₀ _ fun k hk => ?_
    by_cases hki : k = i
    · subst hki
      have := le_rampDist k₀ hj
      unfold labelDist; omega
    · by_cases hkj : k = j
      · subst hkj; exact (le_rampDist k₀ hj).trans (Nat.le_add_right _ _)
      · have hk' : 0 < move ξ i j k := by rw [move_apply_of_ne ξ hki hkj]; exact hk
        exact (le_rampDist k₀ hk').trans (Nat.le_add_right _ _)
  rw [abs_le]
  constructor
  · have : (rampDist k₀ ξ : ℝ) ≤ rampDist k₀ (move ξ i j) + labelDist i j := by exact_mod_cast h2
    linarith
  · have : (rampDist k₀ (move ξ i j) : ℝ) ≤ rampDist k₀ ξ + labelDist i j := by exact_mod_cast h1
    linarith

/-- The commutator sum as a single weighted sum. -/
theorem flat_commutator_eq {S : Finset (Occ N)} {w a f : Occ N → ℝ} {ξ : Occ N}
    (hw1 : ∑ ζ ∈ S, w ζ = 1) :
    ∑ ζ ∈ S, w ζ * (a ζ * f ζ + (1 - a ζ)) - (a ξ * ∑ ζ ∈ S, w ζ * f ζ + (1 - a ξ)) =
      ∑ ζ ∈ S, w ζ * ((a ζ - a ξ) * (f ζ - 1)) := by
  have e : ∑ ζ ∈ S, w ζ * ((a ζ - a ξ) * (f ζ - 1)) =
      ∑ ζ ∈ S, w ζ * (a ζ * f ζ + (1 - a ζ)) - a ξ * ∑ ζ ∈ S, w ζ * f ζ -
        (1 - a ξ) * ∑ ζ ∈ S, w ζ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ζ _ => by ring
  rw [e, hw1]; ring

/-- **S-1: flattening commutator with a local and a global bound.** Same setting as
`flat2_commutator`; `|f| ≤ M_loc` is needed only on the ball where the ramp differs from its value
at `ξ`, and the global `|f| ≤ M` multiplies only the tail:
`|U(Av f)(ξ) - Av(U f)(ξ)| ≤ (M_loc + 1)·2rR/wd + (M + 1)·tail`. -/
theorem flat2_commutator_local {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ} (hsu : s ≤ u)
    (hc : ∀ v ∈ Ioo s u, ∀ i j, i ≠ j → 0 ≤ c v i j)
    (hsym : ∀ v ∈ Ioo s u, ∀ i j, c v i j = c v j i) {w : ℝ → Occ N → ℝ}
    (hw : IsBackwardMomentFlow c r s u w) {ξ : Occ N} (hξ : ξ ∈ sector N r)
    (hwu : ∀ ζ ∈ sector N r, w u ζ = deltaCfg ξ ζ) {f : Occ N → ℝ} {wd : ℝ} (hwd : 0 < wd)
    (k₀ : ℕ) {R : ℝ} (hR : 0 ≤ R) {M Mloc : ℝ} (hMloc : 0 ≤ Mloc)
    (hf : ∀ ζ ∈ sector N r, |f ζ| ≤ M)
    (hfloc : ∀ ζ ∈ sector N r, ζ ∈ occBall r R ξ → ramp wd k₀ ζ ≠ ramp wd k₀ ξ → |f ζ| ≤ Mloc) :
    |∑ ζ ∈ sector N r, w s ζ * (ramp wd k₀ ζ * f ζ + (1 - ramp wd k₀ ζ)) -
        (ramp wd k₀ ξ * ∑ ζ ∈ sector N r, w s ζ * f ζ + (1 - ramp wd k₀ ξ))| ≤
      (Mloc + 1) * (2 / wd * ((r : ℝ) * R)) +
        (M + 1) * ∑ ζ ∈ sector N r \ occBall r R ξ, w s ζ := by
  classical
  have hs : s ∈ Icc s u := ⟨le_rfl, hsu⟩
  have hw0 : ∀ ζ ∈ sector N r, 0 ≤ w s ζ := fun ζ hζ =>
    hw.nonneg hc (fun ζ hζ => by rw [hwu ζ hζ]; unfold deltaCfg; split_ifs <;> norm_num) s hs ζ hζ
  have hw1 : ∑ ζ ∈ sector N r, w s ζ = 1 := by
    rw [hw.mass_eq hsym s hs, Finset.sum_congr rfl fun ζ hζ => hwu ζ hζ]
    simpa using sum_deltaCfg_mul hξ (fun _ => (1 : ℝ))
  rw [flat_commutator_eq hw1]
  set W := occBall r R ξ
  set a := ramp wd k₀
  set L := 2 / wd * ((r : ℝ) * R)
  have hL0 : 0 ≤ L := by positivity
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not (sector N r) (fun ζ => ζ ∈ W)]
  have hsd : (sector N r).filter (fun ζ => ζ ∉ W) = sector N r \ W := by
    ext ζ; simp [Finset.mem_sdiff]
  rw [hsd]
  have hA : ∑ ζ ∈ (sector N r).filter (fun ζ => ζ ∈ W), |w s ζ * ((a ζ - a ξ) * (f ζ - 1))| ≤
      (Mloc + 1) * L := by
    calc ∑ ζ ∈ (sector N r).filter (fun ζ => ζ ∈ W), |w s ζ * ((a ζ - a ξ) * (f ζ - 1))|
        ≤ ∑ ζ ∈ (sector N r).filter (fun ζ => ζ ∈ W), w s ζ * ((Mloc + 1) * L) := by
          refine Finset.sum_le_sum fun ζ hζ => ?_
          obtain ⟨hζS, hζW⟩ := Finset.mem_filter.1 hζ
          rw [abs_mul, abs_of_nonneg (hw0 ζ hζS)]
          refine mul_le_mul_of_nonneg_left ?_ (hw0 ζ hζS)
          by_cases heq : a ζ = a ξ
          · rw [heq, sub_self, zero_mul, abs_zero]; positivity
          · have hd : ¬ ((r : ℝ) * R < (occDist ξ ζ : ℝ)) := (Finset.mem_filter.1 hζW).2
            have ha : |a ζ - a ξ| ≤ L := by
              rw [abs_sub_comm]
              refine (abs_ramp_sub_le hwd k₀ ξ ζ).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
              exact (rampDist_sub_le_occDist hξ hζS k₀).trans (not_lt.1 hd)
            have hfz : |f ζ - 1| ≤ Mloc + 1 :=
              (abs_sub _ _).trans (by rw [abs_one]; linarith [hfloc ζ hζS hζW heq])
            rw [abs_mul, mul_comm (Mloc + 1)]
            exact mul_le_mul ha hfz (abs_nonneg _) hL0
      _ = (Mloc + 1) * L * ∑ ζ ∈ (sector N r).filter (fun ζ => ζ ∈ W), w s ζ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ (Mloc + 1) * L * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← hw1]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun ζ hζ _ => hw0 ζ hζ
      _ = (Mloc + 1) * L := mul_one _
  have hB : ∑ ζ ∈ sector N r \ W, |w s ζ * ((a ζ - a ξ) * (f ζ - 1))| ≤
      (M + 1) * ∑ ζ ∈ sector N r \ W, w s ζ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ζ hζ => ?_
    have hζS := (Finset.mem_sdiff.1 hζ).1
    rw [abs_mul, abs_of_nonneg (hw0 ζ hζS), mul_comm (M + 1)]
    refine mul_le_mul_of_nonneg_left ?_ (hw0 ζ hζS)
    have ha : |a ζ - a ξ| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith [ramp_le_one wd k₀ ζ, ramp_nonneg wd k₀ ξ],
        by linarith [ramp_le_one wd k₀ ξ, ramp_nonneg wd k₀ ζ]⟩
    have hfz : |f ζ - 1| ≤ M + 1 := (abs_sub _ _).trans (by rw [abs_one]; linarith [hf ζ hζS])
    rw [abs_mul]
    calc |a ζ - a ξ| * |f ζ - 1| ≤ 1 * (M + 1) :=
          mul_le_mul ha hfz (abs_nonneg _) zero_le_one
      _ = M + 1 := one_mul _
  linarith

end BlockBand.Palm.MomentFlow
