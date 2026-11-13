module

public import BlockBand.Endpoints.Poisson.SequentialCollarsPaths

/-!
# Sequential collar removal: the incident old components in both pairings

Identification of the old components incident to the selected collar `k` at stage `S`
(Step 2 and Step 3 of the proof in the paper):

* box pairing (`isOldRun_box`, `runRight_box`): the component is the complementary path `k`
  (`unitPos k 3`, length `L k`), both of whose ends attach to collar `k` (case 1 of Step 3);
* cyclic pairing (`isOldRun_cyclic_right`, `isOldRun_cyclic_left`): the right component runs from
  `unitPos k 3` to the nearest collar start `c_j`, `j ∈ S ∪ {k}` (`rightLen`, by `Nat.find`), the
  left one from the nearest right outer block `r_j`, `j ∈ S ∪ {k}`, to `c_k - 1` (`leftLen`); if
  `S = ∅` both are the single path of `n - 3` blocks closing on collar `k` (case 1), otherwise
  each ends at a previously matched port (case 2).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix

section Components

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

theorem layout_le (hL : IsCollarLayout n L) (k : Fin m) : L k + 3 ≤ n := by
  have := unitOffset_add_le_total (L := L) k
  rw [hL.1] at this; omega

theorem unitPos_eq_add (s : ZMod n) (k : Fin m) (o : ℕ) :
    unitPos n L s k o = unitPos n L s k 0 + (o : ZMod n) := by
  rw [unitPos_add, zero_add]

theorem unitPos_add_self (s : ZMod n) (k : Fin m) (o : ℕ) :
    unitPos n L s k (o + n) = unitPos n L s k o := by
  rw [unitPos_eq_add, unitPos_eq_add (o := o)]; push_cast; rw [ZMod.natCast_self, add_zero]

/-!
### The box pairing: the incident component is the complementary path `k`
-/

theorem isOldRun_box (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    IsOldRun L s .box S k (unitPos n L s k 3) (L k) := by
  have hLk := hL.2 k
  have hn := layout_le hL k
  have hpos : ∀ j : ℕ, unitPos n L s k 3 + (j : ZMod n) = unitPos n L s k (3 + j) :=
    fun j => unitPos_add s k 3 j
  refine ⟨hLk, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rintro j hj ⟨i, -, hc | hc | hc⟩ <;> rw [hpos] at hc <;>
    · have := hL.2 i
      have := ((unitPos_inj hL s (by omega) (by omega)).mp hc).2
      omega
  · intro j hj
    rw [hpos, hpos, bondTarget_of_ne]
    · rw [unitPos_succ]; congr 1
    · intro i he
      have := hL.2 i
      have := (unitPos_inj hL s (by omega) (by omega)).mp he
      obtain ⟨rfl, h2⟩ := this
      omega
  · intro q j hj hq
    rw [hpos] at hq ⊢
    have := eq_of_bondTarget_eq hL .box k (by omega) (by omega) hq
    rw [this, unitPos_succ]
    congr 1; omega
  · have h23 : unitPos n L s k 3 - 1 = unitPos n L s k 2 := by
      rw [← unitPos_succ]; ring
    rw [h23, bondTarget_collar hL .box k (by norm_num)]
  · have h23 : unitPos n L s k 3 - 1 = unitPos n L s k 2 := by
      rw [← unitPos_succ]; ring
    rw [h23, hpos, show 3 + (L k - 1) = L k + 2 by omega]
    change bondTarget L s .box (pathEnd L s k) ≠ _
    rw [bondTarget_box_pathEnd hL]
    exact unitPos_ne hL (by omega) (by omega) (by norm_num)

theorem runRight_box (hL : IsCollarLayout n L) (k : Fin m) :
    runRight L s .box (unitPos n L s k 3) (L k) = unitPos n L s k 0 := by
  have hLk := hL.2 k
  unfold runRight
  rw [unitPos_add, show 3 + (L k - 1) = L k + 2 by omega]
  exact bondTarget_box_pathEnd hL k

/-!
### The cyclic pairing: the old paths up to the nearest removed (or selected) collar
-/

theorem exists_right_stop (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    ∃ r : ℕ, ∃ j ∈ insert k S, unitPos n L s k 3 + (r : ZMod n) = unitPos n L s j 0 := by
  have hn := layout_le hL k
  refine ⟨n - 3, k, Finset.mem_insert_self _ _, ?_⟩
  rw [unitPos_add, show 3 + (n - 3) = 0 + n by omega, unitPos_add_self]

theorem exists_left_stop (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    ∃ r : ℕ, ∃ j ∈ insert k S, unitPos n L s k 0 - 1 - (r : ZMod n) = unitPos n L s j 2 := by
  have hn := layout_le hL k
  refine ⟨n - 3, k, Finset.mem_insert_self _ _, ?_⟩
  rw [unitPos_eq_add (o := 2), Nat.cast_sub (by omega), ZMod.natCast_self]
  push_cast; ring

variable (L s) in
open Classical in
/-- Length of the old path to the right of collar `k` (cyclic pairing). -/
def rightLen (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) : ℕ :=
  Nat.find (exists_right_stop (s := s) hL S k)

variable (L s) in
open Classical in
/-- Length of the old path to the left of collar `k` (cyclic pairing). -/
def leftLen (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) : ℕ :=
  Nat.find (exists_left_stop (s := s) hL S k)

theorem rightLen_spec (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    ∃ j ∈ insert k S,
      unitPos n L s k 3 + (rightLen L s hL S k : ZMod n) = unitPos n L s j 0 := by
  classical
  exact Nat.find_spec (exists_right_stop (s := s) hL S k)

theorem rightLen_min (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) {r : ℕ}
    (hr : r < rightLen L s hL S k) :
    ¬ ∃ j ∈ insert k S, unitPos n L s k 3 + (r : ZMod n) = unitPos n L s j 0 := by
  classical
  exact Nat.find_min (exists_right_stop (s := s) hL S k) hr

theorem rightLen_le (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    rightLen L s hL S k ≤ n - 3 := by
  classical
  have hn := layout_le hL k
  exact Nat.find_min' (exists_right_stop (s := s) hL S k) ⟨k, Finset.mem_insert_self _ _, by
    rw [unitPos_add, show 3 + (n - 3) = 0 + n by omega, unitPos_add_self]⟩

theorem leftLen_spec (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    ∃ j ∈ insert k S,
      unitPos n L s k 0 - 1 - (leftLen L s hL S k : ZMod n) = unitPos n L s j 2 := by
  classical
  exact Nat.find_spec (exists_left_stop (s := s) hL S k)

theorem leftLen_min (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) {r : ℕ}
    (hr : r < leftLen L s hL S k) :
    ¬ ∃ j ∈ insert k S, unitPos n L s k 0 - 1 - (r : ZMod n) = unitPos n L s j 2 := by
  classical
  exact Nat.find_min (exists_left_stop (s := s) hL S k) hr

theorem leftLen_le (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    leftLen L s hL S k ≤ n - 3 := by
  classical
  have hn := layout_le hL k
  exact Nat.find_min' (exists_left_stop (s := s) hL S k) ⟨k, Finset.mem_insert_self _ _, by
    rw [unitPos_eq_add (o := 2), Nat.cast_sub (by omega), ZMod.natCast_self]
    push_cast; ring⟩

/-- In the cyclic pairing the right old component of collar `k` is a run. -/
theorem isOldRun_cyclic_right (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    IsOldRun L s .cyclic S k (unitPos n L s k 3) (rightLen L s hL S k) := by
  have hLk := hL.2 k
  have hn := layout_le hL k
  have hle := rightLen_le (s := s) hL S k
  obtain ⟨j₀, hj₀, hstop⟩ := rightLen_spec (s := s) hL S k
  set r := rightLen L s hL S k with hr
  have hr1 : 1 ≤ r := by
    by_contra h0
    have h0 : r = 0 := by omega
    rw [h0, Nat.cast_zero, add_zero] at hstop
    have := hL.2 j₀
    have := ((unitPos_inj hL s (by omega) (by omega)).mp hstop).2
    omega
  refine ⟨hr1, by omega, ?_, fun j _ => by simp [bondTarget]; ring,
    fun q j _ hq => hq, by simp [bondTarget], ?_⟩
  · rintro i hi ⟨j, hj, hc⟩
    have hj' := hL.2 j
    have hmin := fun r' (h : r' < r) => rightLen_min (s := s) hL S k h
    rcases hc with hc | hc | hc
    · exact hmin i hi ⟨j, hj, hc⟩
    · by_cases hio : 1 ≤ i
      · apply hmin (i - 1) (by omega)
        refine ⟨j, hj, ?_⟩
        rw [unitPos_eq_add (o := 1)] at hc
        rw [Nat.cast_sub hio]
        linear_combination hc
      · have hi0 : i = 0 := by omega
        subst hi0
        rw [Nat.cast_zero, add_zero, unitPos_eq_add (o := 1), unitPos_eq_add (o := 3)] at hc
        have : unitPos n L s k 2 = unitPos n L s j 0 := by
          rw [unitPos_eq_add (o := 2)]; push_cast; linear_combination hc
        have := ((unitPos_inj hL s (by omega) (by omega)).mp this).2
        omega
    · by_cases hio : 2 ≤ i
      · apply hmin (i - 2) (by omega)
        refine ⟨j, hj, ?_⟩
        rw [unitPos_eq_add (o := 2)] at hc
        rw [Nat.cast_sub hio]
        push_cast
        linear_combination hc
      · have hc' : unitPos n L s k (3 + i) = unitPos n L s j 2 := by
          rw [← unitPos_add]; exact hc
        have : unitPos n L s k (1 + i) = unitPos n L s j 0 := by
          rw [unitPos_eq_add (o := 1 + i)]
          rw [unitPos_eq_add (o := 3 + i), unitPos_eq_add (o := 2)] at hc'
          push_cast at hc' ⊢
          linear_combination hc'
        have := ((unitPos_inj hL s (by omega) (by omega)).mp this).2
        omega
  · simp only [bondTarget]
    have h23 : unitPos n L s k 3 - 1 = unitPos n L s k 2 := by
      rw [← unitPos_succ]; ring
    rw [h23, add_assoc, show ((r - 1 : ℕ) : ZMod n) + 1 = (r : ZMod n) by
      rw [Nat.cast_sub hr1]; ring, hstop]
    have := hL.2 j₀
    exact unitPos_ne hL (by omega) (by omega) (by norm_num)

theorem runRight_cyclic_right (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    ∃ j ∈ insert k S,
      runRight L s .cyclic (unitPos n L s k 3) (rightLen L s hL S k) = unitPos n L s j 0 := by
  obtain ⟨j₀, hj₀, hstop⟩ := rightLen_spec (s := s) hL S k
  refine ⟨j₀, hj₀, ?_⟩
  have hr1 := (isOldRun_cyclic_right (s := s) hL S k).one_le
  simp only [runRight, bondTarget]
  rw [add_assoc, show ((rightLen L s hL S k - 1 : ℕ) : ZMod n) + 1 =
    (rightLen L s hL S k : ZMod n) by rw [Nat.cast_sub hr1]; ring, hstop]

/-- In the cyclic pairing the left old component of collar `k` is a run ending at `c_k - 1`. -/
theorem isOldRun_cyclic_left (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    IsOldRun L s .cyclic S k (unitPos n L s k 0 - (leftLen L s hL S k : ZMod n))
      (leftLen L s hL S k) := by
  have hLk := hL.2 k
  have hn := layout_le hL k
  have hle := leftLen_le (s := s) hL S k
  obtain ⟨j₀, hj₀, hstop⟩ := leftLen_spec (s := s) hL S k
  set r := leftLen L s hL S k with hr
  have hr1 : 1 ≤ r := by
    by_contra h0
    have h0 : r = 0 := by omega
    rw [h0, Nat.cast_zero, sub_zero] at hstop
    have := hL.2 j₀
    have h3 : unitPos n L s k 0 = unitPos n L s j₀ 3 := by
      rw [unitPos_eq_add (o := 3), unitPos_eq_add (o := 2)] at *
      push_cast at hstop ⊢
      linear_combination hstop
    have := ((unitPos_inj hL s (by omega) (by omega)).mp h3).2
    omega
  refine ⟨hr1, by omega, ?_, fun j _ => by simp [bondTarget]; ring,
    fun q j _ hq => hq, by simp [bondTarget], ?_⟩
  · rintro i hi ⟨j, hj, hc⟩
    have hj' := hL.2 j
    have hmin := fun r' (h : r' < r) => leftLen_min (s := s) hL S k h
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hi
    -- the position is `c_k - 1 - d`
    have hposn : unitPos n L s k 0 - (r : ZMod n) + (i : ZMod n) =
        unitPos n L s k 0 - 1 - (d : ZMod n) := by
      rw [hd]; push_cast; ring
    rw [hposn] at hc
    rcases hc with hc | hc | hc
    · by_cases hd2 : 2 ≤ d
      · apply hmin (d - 2) (by omega)
        refine ⟨j, hj, ?_⟩
        rw [unitPos_eq_add (o := 2), ← hc, Nat.cast_sub hd2]
        push_cast; ring
      · have : unitPos n L s j 2 = unitPos n L s k (1 - d) := by
          rw [unitPos_eq_add (o := 2), unitPos_eq_add (o := 1 - d), ← hc, Nat.cast_sub (by omega)]
          push_cast; ring
        have := ((unitPos_inj hL s (by omega) (by omega)).mp this).2
        omega
    · by_cases hd1 : 1 ≤ d
      · apply hmin (d - 1) (by omega)
        refine ⟨j, hj, ?_⟩
        rw [unitPos_eq_add (o := 2)]
        rw [unitPos_eq_add (o := 1)] at hc
        rw [Nat.cast_sub hd1]
        push_cast at hc ⊢
        linear_combination hc
      · have hd0 : d = 0 := by omega
        subst hd0
        have : unitPos n L s j 2 = unitPos n L s k 0 := by
          rw [unitPos_eq_add (o := 2)]
          rw [unitPos_eq_add (o := 1)] at hc
          push_cast at hc ⊢
          linear_combination (-1 : ZMod n) * hc
        have := ((unitPos_inj hL s (by omega) (by omega)).mp this).2
        omega
    · exact hmin d (by omega) ⟨j, hj, hc⟩
  · simp only [bondTarget]
    have hend : unitPos n L s k 0 - (r : ZMod n) + ((r - 1 : ℕ) : ZMod n) + 1 =
        unitPos n L s k 0 := by
      rw [Nat.cast_sub hr1]; ring
    have hl : unitPos n L s k 0 - (r : ZMod n) - 1 = unitPos n L s j₀ 2 := by
      rw [← hstop]; ring
    rw [hend, hl]
    have := hL.2 j₀
    exact unitPos_ne hL (by omega) (by omega) (by norm_num)

theorem runRight_cyclic_left (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    runRight L s .cyclic (unitPos n L s k 0 - (leftLen L s hL S k : ZMod n))
      (leftLen L s hL S k) = unitPos n L s k 0 := by
  have hr1 := (isOldRun_cyclic_left (s := s) hL S k).one_le
  simp only [runRight, bondTarget]
  rw [Nat.cast_sub hr1]; ring

theorem left_port_cyclic_left (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    ∃ j ∈ insert k S,
      unitPos n L s k 0 - (leftLen L s hL S k : ZMod n) - 1 = unitPos n L s j 2 := by
  obtain ⟨j₀, hj₀, hstop⟩ := leftLen_spec (s := s) hL S k
  exact ⟨j₀, hj₀, by rw [← hstop]; ring⟩

end Components

end BlockBand.Endpoints
