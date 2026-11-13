module
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Finite time grids and their common refinements

Finite time grids with strictly increasing endpoints, the common grid of two grids obtained by
sorting the union of their endpoints, and contiguous refinements, in which every coarse interval is
a contiguous block of fine intervals. Step lengths and path increments telescope over these
blocks.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open scoped NNReal BigOperators
open MeasureTheory ProbabilityTheory
namespace FiniteIto
/-- A deterministic finite time grid with strictly increasing endpoints. -/
structure TimeGrid (m : ℕ) where
  time : Fin (m + 1) → ℝ≥0
  strictMono_time : StrictMono time

/-- Length of grid interval `k`. -/
def TimeGrid.step {m : ℕ} (π : TimeGrid m) (k : Fin m) : ℝ≥0 :=
  π.time k.succ - π.time k.castSucc

/-- Grid interval lengths are nonnegative (and in fact positive). -/
theorem TimeGrid.step_pos {m : ℕ} (π : TimeGrid m) (k : Fin m) :
    0 < π.step k := by
  exact tsub_pos_iff_lt.mpr (π.strictMono_time k.castSucc_lt_succ)

end FiniteIto
namespace AdaptedStepIto
open FiniteIto
/-- A refinement records the parent coarse interval of every fine interval and the
exact decomposition of each coarse time length into its fine children. -/
structure GridRefinement {m n : ℕ} (coarse : TimeGrid m) (fine : TimeGrid n) where
  parent : Fin n → Fin m
  step_sum : ∀ i, ∑ k : {k : Fin n // parent k = i}, (fine.step k : ℝ) = coarse.step i

end AdaptedStepIto
namespace ContinuousItoCommonRefinement
open FiniteIto AdaptedStepIto
/-- The finite union of the endpoint values of two grids. -/
def commonEndpointSet {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n) : Finset ℝ≥0 :=
  Finset.univ.image π.time ∪ Finset.univ.image ρ.time

/-- The number of intervals in the increasing union of two endpoint sets. -/
def commonStepCount {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n) : ℕ :=
  (commonEndpointSet π ρ).card - 1

theorem commonEndpointSet_card_pos {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n) :
    0 < (commonEndpointSet π ρ).card := by
  apply Finset.card_pos.mpr
  refine ⟨π.time 0, ?_⟩
  simp [commonEndpointSet]

theorem commonEndpointSet_card_eq {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n) :
    (commonEndpointSet π ρ).card = commonStepCount π ρ + 1 := by
  have hcard := commonEndpointSet_card_pos π ρ
  unfold commonStepCount
  omega

/-- Increasing enumeration of all endpoints occurring in either grid. -/
def commonEndpointOrderIso {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n) :
    Fin (commonStepCount π ρ + 1) ≃o (commonEndpointSet π ρ : Set ℝ≥0) :=
  (commonEndpointSet π ρ).orderIsoOfFin (commonEndpointSet_card_eq π ρ)

/-- The common grid obtained by sorting the union of the two endpoint sets. -/
def commonTimeGrid {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n) :
    TimeGrid (commonStepCount π ρ) where
  time i := (commonEndpointOrderIso π ρ i : ℝ≥0)
  strictMono_time := by
    intro i j hij
    exact (commonEndpointOrderIso π ρ).strictMono hij

/-- Each endpoint of the first grid has its unique index in the common grid. -/
def leftEndpointIndex {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n) :
    Fin (m + 1) → Fin (commonStepCount π ρ + 1) :=
  fun i => (commonEndpointOrderIso π ρ).symm
    ⟨π.time i, by simp [commonEndpointSet]⟩

/-- Each endpoint of the second grid has its unique index in the common grid. -/
def rightEndpointIndex {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n) :
    Fin (n + 1) → Fin (commonStepCount π ρ + 1) :=
  fun i => (commonEndpointOrderIso π ρ).symm
    ⟨ρ.time i, by simp [commonEndpointSet]⟩

@[simp] theorem commonTimeGrid_leftEndpointIndex {m n : ℕ}
    (π : TimeGrid m) (ρ : TimeGrid n) (i : Fin (m + 1)) :
    (commonTimeGrid π ρ).time (leftEndpointIndex π ρ i) = π.time i := by
  simp [commonTimeGrid, leftEndpointIndex]

@[simp] theorem commonTimeGrid_rightEndpointIndex {m n : ℕ}
    (π : TimeGrid m) (ρ : TimeGrid n) (i : Fin (n + 1)) :
    (commonTimeGrid π ρ).time (rightEndpointIndex π ρ i) = ρ.time i := by
  simp [commonTimeGrid, rightEndpointIndex]

/-- The first grid embeds strictly monotonically into the common endpoint grid. -/
theorem leftEndpointIndex_strictMono {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n) :
    StrictMono (leftEndpointIndex π ρ) := by
  intro i j hij
  apply (commonEndpointOrderIso π ρ).symm.strictMono
  exact π.strictMono_time hij

/-- The second grid embeds strictly monotonically into the common endpoint grid. -/
theorem rightEndpointIndex_strictMono {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n) :
    StrictMono (rightEndpointIndex π ρ) := by
  intro i j hij
  apply (commonEndpointOrderIso π ρ).symm.strictMono
  exact ρ.strictMono_time hij

/-- Under a common initial time, both endpoint embeddings start at index zero. -/
theorem leftEndpointIndex_zero {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n)
    (h0 : π.time 0 = ρ.time 0) :
    leftEndpointIndex π ρ 0 = 0 := by
  apply Fin.ext
  simp only [Fin.val_zero]
  by_contra hne
  have hpos : 0 < (leftEndpointIndex π ρ 0).val := Nat.pos_of_ne_zero hne
  let j : Fin (commonStepCount π ρ + 1) :=
    ⟨(leftEndpointIndex π ρ 0).val - 1, by omega⟩
  have hj : j < leftEndpointIndex π ρ 0 := by
    change (leftEndpointIndex π ρ 0).val - 1 <
      (leftEndpointIndex π ρ 0).val
    omega
  have hlt := (commonTimeGrid π ρ).strictMono_time hj
  have hjmem : (commonTimeGrid π ρ).time j ∈ commonEndpointSet π ρ :=
    (commonEndpointOrderIso π ρ j).property
  simp only [commonEndpointSet, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hjmem
  rcases hjmem with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hle : π.time 0 ≤ π.time i := π.strictMono_time.monotone (Fin.zero_le i)
    rw [commonTimeGrid_leftEndpointIndex] at hlt
    rw [hi] at hle
    exact (not_lt_of_ge hle) hlt
  · have hle : ρ.time 0 ≤ ρ.time i := ρ.strictMono_time.monotone (Fin.zero_le i)
    rw [commonTimeGrid_leftEndpointIndex] at hlt
    rw [← h0, hi] at hle
    exact (not_lt_of_ge hle) hlt

theorem rightEndpointIndex_zero {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n)
    (h0 : π.time 0 = ρ.time 0) :
    rightEndpointIndex π ρ 0 = 0 := by
  have hEq : leftEndpointIndex π ρ 0 = rightEndpointIndex π ρ 0 := by
    unfold leftEndpointIndex rightEndpointIndex
    exact congrArg (commonEndpointOrderIso π ρ).symm (Subtype.ext h0)
  rw [← hEq, leftEndpointIndex_zero π ρ h0]

/-- Under a common terminal time, both endpoint embeddings finish at the last
common-grid endpoint. -/
theorem leftEndpointIndex_last {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n)
    (hT : π.time (Fin.last m) = ρ.time (Fin.last n)) :
    leftEndpointIndex π ρ (Fin.last m) = Fin.last (commonStepCount π ρ) := by
  apply Fin.ext
  simp only [Fin.val_last]
  by_contra hne
  have hltVal : (leftEndpointIndex π ρ (Fin.last m)).val <
      commonStepCount π ρ := by
    have hle := (leftEndpointIndex π ρ (Fin.last m)).isLt
    omega
  let j : Fin (commonStepCount π ρ + 1) :=
    ⟨(leftEndpointIndex π ρ (Fin.last m)).val + 1, by omega⟩
  have hj : leftEndpointIndex π ρ (Fin.last m) < j := by
    change (leftEndpointIndex π ρ (Fin.last m)).val <
      (leftEndpointIndex π ρ (Fin.last m)).val + 1
    omega
  have hlt := (commonTimeGrid π ρ).strictMono_time hj
  rw [commonTimeGrid_leftEndpointIndex] at hlt
  have hjmem : (commonTimeGrid π ρ).time j ∈ commonEndpointSet π ρ :=
    (commonEndpointOrderIso π ρ j).property
  simp only [commonEndpointSet, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hjmem
  rcases hjmem with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hle : π.time i ≤ π.time (Fin.last m) :=
      π.strictMono_time.monotone (Fin.le_last i)
    rw [hi] at hle
    exact (not_lt_of_ge hle) hlt
  · have hle : ρ.time i ≤ ρ.time (Fin.last n) :=
      ρ.strictMono_time.monotone (Fin.le_last i)
    rw [← hT, hi] at hle
    exact (not_lt_of_ge hle) hlt

theorem rightEndpointIndex_last {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n)
    (hT : π.time (Fin.last m) = ρ.time (Fin.last n)) :
    rightEndpointIndex π ρ (Fin.last n) = Fin.last (commonStepCount π ρ) := by
  have hEq :
      leftEndpointIndex π ρ (Fin.last m) =
        rightEndpointIndex π ρ (Fin.last n) := by
    unfold leftEndpointIndex rightEndpointIndex
    exact congrArg (commonEndpointOrderIso π ρ).symm (Subtype.ext hT)
  rw [← hEq, leftEndpointIndex_last π ρ hT]

/-!
## Contiguous refinements
-/

theorem existsUnique_parent_interval {m n : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (he : StrictMono e)
    (he0 : e 0 = 0) (heT : e (Fin.last m) = Fin.last n)
    (k : Fin n) :
    ∃! i : Fin m,
      e i.castSucc ≤ k.castSucc ∧ k.succ ≤ e i.succ := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 0 := by
      have hlast0 : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
      have hfin : (0 : Fin (n + 1)) = Fin.last n := by
        calc
          0 = e 0 := he0.symm
          _ = e (Fin.last 0) := congrArg e hlast0
          _ = Fin.last n := heT
      have h := congrArg Fin.val hfin
      simp only [Fin.val_zero, Fin.val_last] at h
      omega
    subst n
    exact Fin.elim0 k
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let lastInterval : Fin m := ⟨m - 1, by omega⟩
    have hlastSucc : lastInterval.succ = Fin.last m := by
      apply Fin.ext
      simp [lastInterval]
      omega
    let S : Finset (Fin m) :=
      Finset.univ.filter (fun i => k.succ ≤ e i.succ)
    have hlastMem : lastInterval ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hlastSucc, heT]
      exact Fin.le_last _
    have hS : S.Nonempty := ⟨lastInterval, hlastMem⟩
    let i : Fin m := S.min' hS
    have hiMem : i ∈ S := S.min'_mem hS
    have hupper : k.succ ≤ e i.succ := by
      simpa [S] using hiMem
    have hlower : e i.castSucc ≤ k.castSucc := by
      by_contra hnot
      have hstrict : k.castSucc < e i.castSucc := lt_of_not_ge hnot
      let z : Fin m := ⟨0, hmpos⟩
      have hi0 : i ≠ z := by
        intro hi
        rw [hi] at hstrict
        have hz : z.castSucc = (0 : Fin (m + 1)) := rfl
        rw [hz, he0] at hstrict
        exact Fin.not_lt_zero _ hstrict
      have hipos : 0 < i.val := by
        by_contra h
        have hiz : i = z := by
          apply Fin.ext
          simp only [z]
          omega
        exact hi0 hiz
      let p : Fin m := ⟨i.val - 1, by omega⟩
      have hpSucc : p.succ = i.castSucc := by
        apply Fin.ext
        simp [p]
        omega
      have hp_lt : p < i := by
        change p.val < i.val
        dsimp [p]
        omega
      have hpMem : p ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hpSucc]
        rw [Fin.le_iff_val_le_val]
        change k.val < (e i.castSucc).val at hstrict
        simp only [Fin.val_succ]
        omega
      exact (not_lt_of_ge (S.min'_le p hpMem)) hp_lt
    refine ⟨i, ⟨hlower, hupper⟩, ?_⟩
    intro i' hi'
    have hi_le : i ≤ i' := S.min'_le i' (by simpa [S] using hi'.2)
    apply le_antisymm
    · by_contra hnot
      have hi_lt : i < i' := lt_of_not_ge hnot
      have hindex : i.succ ≤ i'.castSucc := by
        exact Fin.succ_le_castSucc_iff.mpr hi_lt
      have he_le : e i.succ ≤ e i'.castSucc := he.monotone hindex
      exact (not_le_of_gt k.castSucc_lt_succ)
        (le_trans hupper (le_trans he_le hi'.1))
    · exact hi_le

/-- A grid refinement together with the exact contiguous block occupied by every
coarse interval. -/
structure ContiguousGridRefinement {m n : ℕ}
    (coarse : TimeGrid m) (fine : TimeGrid n) where
  toGridRefinement : GridRefinement coarse fine
  endpointIndex : Fin (m + 1) → Fin (n + 1)
  endpointIndex_strictMono : StrictMono endpointIndex
  endpoint_time : ∀ j, fine.time (endpointIndex j) = coarse.time j
  endpoint_zero : endpointIndex 0 = 0
  endpoint_last : endpointIndex (Fin.last m) = Fin.last n
  parent_interval : ∀ k,
    endpointIndex (toGridRefinement.parent k).castSucc ≤ k.castSucc ∧
      k.succ ≤ endpointIndex (toGridRefinement.parent k).succ
  parent_unique : ∀ k i,
    endpointIndex i.castSucc ≤ k.castSucc →
    k.succ ≤ endpointIndex i.succ →
    toGridRefinement.parent k = i

/-- Fine interval indices between two ordered endpoint indices are exactly the
corresponding half-open interval of natural numbers. -/
def fineIntervalEquiv {n : ℕ} (a b : Fin (n + 1)) (_hab : a ≤ b) :
    {k : Fin n // a ≤ k.castSucc ∧ k.succ ≤ b} ≃
      {j : ℕ // j ∈ Finset.Ico a.val b.val} where
  toFun k := ⟨k.val, by
    simp only [Finset.mem_Ico]
    constructor
    · exact k.property.1
    · have h := k.property.2
      change k.val + 1 ≤ b.val at h
      omega⟩
  invFun j := by
    have hjmem := j.property
    have hj : j.val < n := by
      have hb := b.isLt
      simp only [Finset.mem_Ico] at hjmem
      omega
    refine ⟨⟨j.val, hj⟩, ?_⟩
    simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ,
      Finset.mem_Ico] at hjmem ⊢
    omega
  left_inv k := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    rfl

/-- Step lengths telescope over any contiguous block of a fine grid. -/
theorem sum_steps_between {n : ℕ} (fine : TimeGrid n)
    (a b : Fin (n + 1)) (hab : a ≤ b) :
    (∑ k : {k : Fin n // a ≤ k.castSucc ∧ k.succ ≤ b},
        (fine.step k : ℝ)) =
      (fine.time b : ℝ) - (fine.time a : ℝ) := by
  let F : ℕ → ℝ := fun j =>
    if hj : j < n + 1 then (fine.time ⟨j, hj⟩ : ℝ) else 0
  have htel := Finset.sum_Ico_sub F (show a.val ≤ b.val from hab)
  have heq :
      (∑ k : {k : Fin n // a ≤ k.castSucc ∧ k.succ ≤ b},
          (fine.step k : ℝ)) =
        ∑ j : {j : ℕ // j ∈ Finset.Ico a.val b.val},
          (F (j.val + 1) - F j.val) := by
    apply Fintype.sum_equiv (fineIntervalEquiv a b hab)
    intro k
    have hk := k.property
    simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ] at hk
    have hklt : k.val < n := k.val.isLt
    have hklt1 : k.val < n + 1 := by omega
    have hkslt : k.val + 1 < n + 1 := by omega
    change ((fine.time k.val.succ - fine.time k.val.castSucc : ℝ≥0) : ℝ) =
      F (k.val + 1) - F k.val
    rw [NNReal.coe_sub]
    · simp only [F, dite_eq_left hkslt, dite_eq_left hklt1]
      congr 1
    · exact (fine.strictMono_time k.val.castSucc_lt_succ).le
  rw [heq]
  have hsubtype :
      (∑ j : {j : ℕ // j ∈ Finset.Ico a.val b.val},
          (F (j.val + 1) - F j.val)) =
        ∑ j ∈ Finset.Ico a.val b.val, (F (j + 1) - F j) := by
    change ∑ j ∈ (Finset.Ico a.val b.val).attach,
        (F (j.val + 1) - F j.val) =
      ∑ j ∈ Finset.Ico a.val b.val, (F (j + 1) - F j)
    simpa using Finset.sum_attach (Finset.Ico a.val b.val)
      (fun j => F (j + 1) - F j)
  rw [hsubtype, htel]
  have ha : a.val ≤ n := Nat.lt_succ_iff.mp a.isLt
  have hb : b.val ≤ n := Nat.lt_succ_iff.mp b.isLt
  simp [F, ha, hb]

/-- Parent coarse interval selected by the unique contiguous block containing a
fine interval. -/
def endpointParent {m n : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (he : StrictMono e)
    (he0 : e 0 = 0) (heT : e (Fin.last m) = Fin.last n) :
    Fin n → Fin m :=
  fun k => Classical.choose (existsUnique_parent_interval e he he0 heT k)

theorem endpointParent_interval {m n : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (he : StrictMono e)
    (he0 : e 0 = 0) (heT : e (Fin.last m) = Fin.last n) (k : Fin n) :
    e (endpointParent e he he0 heT k).castSucc ≤ k.castSucc ∧
      k.succ ≤ e (endpointParent e he he0 heT k).succ :=
  by
    unfold endpointParent
    exact (Classical.choose_spec
      (existsUnique_parent_interval e he he0 heT k)).1

theorem endpointParent_unique {m n : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (he : StrictMono e)
    (he0 : e 0 = 0) (heT : e (Fin.last m) = Fin.last n)
    (k : Fin n) (i : Fin m)
    (hleft : e i.castSucc ≤ k.castSucc) (hright : k.succ ≤ e i.succ) :
    endpointParent e he he0 heT k = i :=
  by
    unfold endpointParent
    exact ((Classical.choose_spec
      (existsUnique_parent_interval e he he0 heT k)).2 i
        ⟨hleft, hright⟩).symm

theorem endpointParent_eq_iff {m n : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (he : StrictMono e)
    (he0 : e 0 = 0) (heT : e (Fin.last m) = Fin.last n)
    (k : Fin n) (i : Fin m) :
    endpointParent e he he0 heT k = i ↔
      e i.castSucc ≤ k.castSucc ∧ k.succ ≤ e i.succ := by
  constructor
  · intro h
    subst i
    exact endpointParent_interval e he he0 heT k
  · exact fun h => endpointParent_unique e he he0 heT k i h.1 h.2

/-- A parent fiber is precisely its contiguous block of fine intervals. -/
def parentFiberEquiv {m n : ℕ}
    (e : Fin (m + 1) → Fin (n + 1)) (he : StrictMono e)
    (he0 : e 0 = 0) (heT : e (Fin.last m) = Fin.last n) (i : Fin m) :
    {k : Fin n // endpointParent e he he0 heT k = i} ≃
      {k : Fin n // e i.castSucc ≤ k.castSucc ∧ k.succ ≤ e i.succ} where
  toFun k := ⟨k, (endpointParent_eq_iff e he he0 heT k i).mp k.property⟩
  invFun k := ⟨k, (endpointParent_eq_iff e he he0 heT k i).mpr k.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Contiguous endpoint subdivision implies the exact parent step-sum law. -/
theorem endpointParent_step_sum {m n : ℕ}
    (coarse : TimeGrid m) (fine : TimeGrid n)
    (e : Fin (m + 1) → Fin (n + 1)) (he : StrictMono e)
    (htime : ∀ j, fine.time (e j) = coarse.time j)
    (he0 : e 0 = 0) (heT : e (Fin.last m) = Fin.last n) (i : Fin m) :
    (∑ k : {k : Fin n // endpointParent e he he0 heT k = i},
      (fine.step k : ℝ)) = coarse.step i := by
  rw [Fintype.sum_equiv (parentFiberEquiv e he he0 heT i)
    (fun k => (fine.step k : ℝ))
    (fun k => (fine.step k : ℝ)) (fun _ => rfl)]
  rw [sum_steps_between fine (e i.castSucc) (e i.succ)
    (he.monotone i.castSucc_le_succ)]
  rw [htime i.succ, htime i.castSucc]
  change (coarse.time i.succ : ℝ) - (coarse.time i.castSucc : ℝ) =
    ((coarse.time i.succ - coarse.time i.castSucc : ℝ≥0) : ℝ)
  rw [NNReal.coe_sub (coarse.strictMono_time i.castSucc_lt_succ).le]

/-- Every endpoint embedding preserving the times and both outer endpoints induces a contiguous
grid refinement. -/
def contiguousRefinementOfEndpointEmbedding {m n : ℕ}
    (coarse : TimeGrid m) (fine : TimeGrid n)
    (e : Fin (m + 1) → Fin (n + 1)) (he : StrictMono e)
    (htime : ∀ j, fine.time (e j) = coarse.time j)
    (he0 : e 0 = 0) (heT : e (Fin.last m) = Fin.last n) :
    ContiguousGridRefinement coarse fine where
  toGridRefinement :=
    { parent := endpointParent e he he0 heT
      step_sum := endpointParent_step_sum coarse fine e he htime he0 heT }
  endpointIndex := e
  endpointIndex_strictMono := he
  endpoint_time := htime
  endpoint_zero := he0
  endpoint_last := heT
  parent_interval := endpointParent_interval e he he0 heT
  parent_unique := endpointParent_unique e he he0 heT

/-- The sorted endpoint union contiguously refines the first grid. -/
def leftCommonRefinement {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n)
    (h0 : π.time 0 = ρ.time 0)
    (hT : π.time (Fin.last m) = ρ.time (Fin.last n)) :
    ContiguousGridRefinement π (commonTimeGrid π ρ) :=
  contiguousRefinementOfEndpointEmbedding π (commonTimeGrid π ρ)
    (leftEndpointIndex π ρ) (leftEndpointIndex_strictMono π ρ)
    (commonTimeGrid_leftEndpointIndex π ρ)
    (leftEndpointIndex_zero π ρ h0) (leftEndpointIndex_last π ρ hT)

/-- The same sorted endpoint union contiguously refines the second grid. -/
def rightCommonRefinement {m n : ℕ} (π : TimeGrid m) (ρ : TimeGrid n)
    (h0 : π.time 0 = ρ.time 0)
    (hT : π.time (Fin.last m) = ρ.time (Fin.last n)) :
    ContiguousGridRefinement ρ (commonTimeGrid π ρ) :=
  contiguousRefinementOfEndpointEmbedding ρ (commonTimeGrid π ρ)
    (rightEndpointIndex π ρ) (rightEndpointIndex_strictMono π ρ)
    (commonTimeGrid_rightEndpointIndex π ρ)
    (rightEndpointIndex_zero π ρ h0) (rightEndpointIndex_last π ρ hT)

theorem leftCommonRefinement_step_sum {m n : ℕ}
    (π : TimeGrid m) (ρ : TimeGrid n)
    (h0 : π.time 0 = ρ.time 0)
    (hT : π.time (Fin.last m) = ρ.time (Fin.last n)) (i : Fin m) :
    (∑ k : {k : Fin (commonStepCount π ρ) //
        (leftCommonRefinement π ρ h0 hT).toGridRefinement.parent k = i},
      ((commonTimeGrid π ρ).step k : ℝ)) = π.step i :=
  (leftCommonRefinement π ρ h0 hT).toGridRefinement.step_sum i

theorem rightCommonRefinement_step_sum {m n : ℕ}
    (π : TimeGrid m) (ρ : TimeGrid n)
    (h0 : π.time 0 = ρ.time 0)
    (hT : π.time (Fin.last m) = ρ.time (Fin.last n)) (i : Fin n) :
    (∑ k : {k : Fin (commonStepCount π ρ) //
        (rightCommonRefinement π ρ h0 hT).toGridRefinement.parent k = i},
      ((commonTimeGrid π ρ).step k : ℝ)) = ρ.step i :=
  (rightCommonRefinement π ρ h0 hT).toGridRefinement.step_sum i

/-!
## Telescoping and stochastic-sum compatibility
-/

/-- Consecutive differences telescope over a contiguous block of a finite path. -/
theorem sum_differences_between {n : ℕ} {A : Type*} [AddCommGroup A]
    (x : Fin (n + 1) → A) (a b : Fin (n + 1)) (hab : a ≤ b) :
    (∑ k : {k : Fin n // a ≤ k.castSucc ∧ k.succ ≤ b},
      (x k.val.succ - x k.val.castSucc)) = x b - x a := by
  let F : ℕ → A := fun j => if hj : j < n + 1 then x ⟨j, hj⟩ else 0
  have htel := Finset.sum_Ico_sub F (show a.val ≤ b.val from hab)
  have heq :
      (∑ k : {k : Fin n // a ≤ k.castSucc ∧ k.succ ≤ b},
          (x k.val.succ - x k.val.castSucc)) =
        ∑ j : {j : ℕ // j ∈ Finset.Ico a.val b.val},
          (F (j.val + 1) - F j.val) := by
    apply Fintype.sum_equiv (fineIntervalEquiv a b hab)
    intro k
    have hklt : k.val < n := k.val.isLt
    have hklt1 : k.val < n + 1 := by omega
    have hkslt : k.val + 1 < n + 1 := by omega
    change x k.val.succ - x k.val.castSucc =
      F (k.val + 1) - F k.val
    simp only [F, dite_eq_left hkslt, dite_eq_left hklt1]
    congr 1
  rw [heq]
  have hsubtype :
      (∑ j : {j : ℕ // j ∈ Finset.Ico a.val b.val},
          (F (j.val + 1) - F j.val)) =
        ∑ j ∈ Finset.Ico a.val b.val, (F (j + 1) - F j) := by
    change ∑ j ∈ (Finset.Ico a.val b.val).attach,
        (F (j.val + 1) - F j.val) =
      ∑ j ∈ Finset.Ico a.val b.val, (F (j + 1) - F j)
    simpa using Finset.sum_attach (Finset.Ico a.val b.val)
      (fun j => F (j + 1) - F j)
  rw [hsubtype, htel]
  have ha : a.val ≤ n := Nat.lt_succ_iff.mp a.isLt
  have hb : b.val ≤ n := Nat.lt_succ_iff.mp b.isLt
  simp [F, ha, hb]

theorem ContiguousGridRefinement.parent_eq_iff {m n : ℕ}
    {coarse : TimeGrid m} {fine : TimeGrid n}
    (r : ContiguousGridRefinement coarse fine) (k : Fin n) (i : Fin m) :
    r.toGridRefinement.parent k = i ↔
      r.endpointIndex i.castSucc ≤ k.castSucc ∧
        k.succ ≤ r.endpointIndex i.succ := by
  constructor
  · intro h
    subst i
    exact r.parent_interval k
  · exact fun h => r.parent_unique k i h.1 h.2

/-- The parent fiber supplied by a contiguous refinement is its endpoint block. -/
def ContiguousGridRefinement.parentFiberEquiv {m n : ℕ}
    {coarse : TimeGrid m} {fine : TimeGrid n}
    (r : ContiguousGridRefinement coarse fine) (i : Fin m) :
    {k : Fin n // r.toGridRefinement.parent k = i} ≃
      {k : Fin n // r.endpointIndex i.castSucc ≤ k.castSucc ∧
        k.succ ≤ r.endpointIndex i.succ} where
  toFun k := ⟨k, (r.parent_eq_iff k i).mp k.property⟩
  invFun k := ⟨k, (r.parent_eq_iff k i).mpr k.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Path increments over all fine children of one coarse interval telescope to
the difference at its embedded coarse endpoints. -/
theorem ContiguousGridRefinement.sum_path_increments {m n : ℕ}
    {coarse : TimeGrid m} {fine : TimeGrid n}
    (r : ContiguousGridRefinement coarse fine)
    {A : Type*} [AddCommGroup A] (x : Fin (n + 1) → A) (i : Fin m) :
    (∑ k : {k : Fin n // r.toGridRefinement.parent k = i},
      (x k.val.succ - x k.val.castSucc)) =
      x (r.endpointIndex i.succ) - x (r.endpointIndex i.castSucc) := by
  rw [Fintype.sum_equiv (r.parentFiberEquiv i)
    (fun k => x k.val.succ - x k.val.castSucc)
    (fun k => x k.val.succ - x k.val.castSucc) (fun _ => rfl)]
  exact sum_differences_between x _ _
    (r.endpointIndex_strictMono.monotone i.castSucc_le_succ)

end ContinuousItoCommonRefinement
end BlockBand.SourceProcess.FiniteDriverCompletion
