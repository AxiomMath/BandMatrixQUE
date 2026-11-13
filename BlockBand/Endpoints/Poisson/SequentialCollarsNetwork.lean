module

public import BlockBand.Endpoints.Poisson.SequentialCollarsAlgebra

/-!
# Sequential collar removal: the ring network, the two pairings and the stage matrices

We set up the ring network used in the sequential-collars lemma and prove its item (iii), the
exact stage factorization.

* **Layout.** Block positions are `ZMod n` (the ring), sites `RingSite n W = ZMod n × Fin W`.
  `IsCollarLayout n L`: the ring is `m` consecutive units, unit `k` = collar `k` (offsets
  `0,1,2` from `unitPos n L s k 0`: outer `A`, middle `G`, outer `A`) followed by the
  complementary path `k` of `L k ≥ 1` blocks; `n = Σ (L k + 3)`; `s` is an arbitrary offset.
* **Coordinates.** `RingCoords n W = (blocks, bonds)`, `ω.1 p` the diagonal block at `p`,
  `ω.2 p` the forward bond `H_{p,p+1}`.
* **Pairings** (the rewiring of the collars). `bondTarget π p` is the block that bond `ω.2 p` attaches `p`
  to: `p + 1` in the cyclic pairing; in the box pairing the bond leaving the end of path `k` is
  attached to the left outer block of collar `k` instead of collar `k+1` (each complementary
  path closes through one collar). All other bonds and all diagonals are shared: one coupling on
  one probability space, no duplicated variable.
* **Stages.** `S` = removed collars. `stageFull π S e z buf κ ω` is the full matrix on all
  sites: diagonal blocks `A_p - e`, except `zI_W` (`z = ξ + iη`) at the two outer blocks of every
  removed collar; bonds by `bondTarget`; the source `iκ/W²` on the blocks of `C`
  (`InSource buf`: path blocks at offsets `buf ≤ j < L k - buf`, i.e. all path blocks except a
  buffer of `buf` blocks at each path end; `buf` = rounded `RW`).
  `stageMatrix` deletes the middle blocks of removed collars (`StageSite`).
* **Item (iii).** `stageMatrix_factorization` (the stage factorization) and
  `stageMatrix_factorization_of_hermitian` (only `M_κ⁻¹`, `(G-e)⁻¹` assumed), the prefactor
  `collarPrefactor e z (freshCollar L s k ω)` depending only on the fresh collar; and
  `final_models_agree`: the fully matched models of the two pairings coincide after the
  deterministic site permutation `finalSitePerm` (left outer coordinate of collar `k` ↦ that of
  collar `k+1`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix

section Layout

variable {m : ℕ} (n : ℕ) (L : Fin m → ℕ)

/-- The collar layout: `n = Σₖ (L k + 3)` and every complementary path is nonempty. -/
def IsCollarLayout : Prop := (∑ k, (L k + 3) = n) ∧ ∀ k, 1 ≤ L k

/-- Offset of unit `k` (collar `k` followed by path `k`) from the base position. -/
def unitOffset (k : Fin m) : ℕ := ∑ i ∈ Finset.univ.filter (· < k), (L i + 3)

/-- Block position at offset `o` in unit `k` (offsets `0,1,2`: collar; `3 + j`: path). -/
def unitPos (s : ZMod n) (k : Fin m) (o : ℕ) : ZMod n := s + ((unitOffset L k + o : ℕ) : ZMod n)

variable {n L}

theorem unitOffset_add_le_of_lt {k k' : Fin m} (h : k < k') :
    unitOffset L k + (L k + 3) ≤ unitOffset L k' := by
  unfold unitOffset
  have hsub : insert k (Finset.univ.filter (· < k)) ⊆ Finset.univ.filter (· < k') := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hi with rfl | hi
    · exact h
    · exact lt_trans hi h
  have hk : k ∉ Finset.univ.filter (· < k) := by simp
  calc (∑ i ∈ Finset.univ.filter (· < k), (L i + 3)) + (L k + 3)
      = ∑ i ∈ insert k (Finset.univ.filter (· < k)), (L i + 3) := by
        rw [Finset.sum_insert hk, add_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

theorem unitOffset_add_le_total (k : Fin m) :
    unitOffset L k + (L k + 3) ≤ ∑ i, (L i + 3) := by
  unfold unitOffset
  have hk : k ∉ Finset.univ.filter (· < k) := by simp
  calc (∑ i ∈ Finset.univ.filter (· < k), (L i + 3)) + (L k + 3)
      = ∑ i ∈ insert k (Finset.univ.filter (· < k)), (L i + 3) := by
        rw [Finset.sum_insert hk, add_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem unitPos_add (s : ZMod n) (k : Fin m) (o d : ℕ) :
    unitPos n L s k o + (d : ZMod n) = unitPos n L s k (o + d) := by
  unfold unitPos; push_cast; ring

theorem unitPos_inj (hL : IsCollarLayout n L) (s : ZMod n) {k k' : Fin m} {o o' : ℕ}
    (ho : o < L k + 3) (ho' : o' < L k' + 3) :
    unitPos n L s k o = unitPos n L s k' o' ↔ k = k' ∧ o = o' := by
  constructor
  · intro h
    unfold unitPos at h
    have h1 : ((unitOffset L k + o : ℕ) : ZMod n) = ((unitOffset L k' + o' : ℕ) : ZMod n) :=
      add_left_cancel h
    rw [ZMod.natCast_eq_natCast_iff' _ _ n] at h1
    have hk := unitOffset_add_le_total (L := L) k
    have hk' := unitOffset_add_le_total (L := L) k'
    rw [hL.1] at hk hk'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    rcases lt_trichotomy k k' with hlt | rfl | hgt
    · have := unitOffset_add_le_of_lt (L := L) hlt; omega
    · exact ⟨rfl, by omega⟩
    · have := unitOffset_add_le_of_lt (L := L) hgt; omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem unitPos_end (hL : IsCollarLayout n L) (s : ZMod n) (k : Fin m) :
    unitPos n L s k (L k + 3) = unitPos n L s (finRotate m k) 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := k.isLt; omega⟩
  unfold unitPos
  congr 1
  by_cases hk : k = Fin.last m'
  · subst hk
    have hr : finRotate (m' + 1) (Fin.last m') = 0 := finRotate_last
    rw [hr]
    have h0 : unitOffset L (0 : Fin (m' + 1)) = 0 := by
      unfold unitOffset
      apply Finset.sum_eq_zero
      intro i hi
      simp at hi
    have hlast : unitOffset L (Fin.last m') + (L (Fin.last m') + 3) = n := by
      rw [← hL.1]
      unfold unitOffset
      have hk : Fin.last m' ∉ Finset.univ.filter (· < Fin.last m') := by simp
      have huniv : insert (Fin.last m') (Finset.univ.filter (· < Fin.last m')) = Finset.univ := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        rcases (Fin.le_last i).lt_or_eq with h | h
        · exact Or.inr h
        · exact Or.inl h
      calc (∑ i ∈ Finset.univ.filter (· < Fin.last m'), (L i + 3)) + (L (Fin.last m') + 3)
          = ∑ i ∈ insert (Fin.last m') (Finset.univ.filter (· < Fin.last m')), (L i + 3) := by
            rw [Finset.sum_insert hk, add_comm]
        _ = _ := by rw [huniv]
    rw [h0, hlast, ZMod.natCast_self]
    simp
  · have hval : ((finRotate (m' + 1) k : Fin (m' + 1)) : ℕ) = k + 1 := coe_finRotate_of_ne_last hk
    have hsucc : unitOffset L (finRotate (m' + 1) k) = unitOffset L k + (L k + 3) := by
      unfold unitOffset
      have hset : Finset.univ.filter (· < finRotate (m' + 1) k) =
          insert k (Finset.univ.filter (· < k)) := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Fin.lt_def, hval, Fin.lt_def]
        constructor
        · intro h
          rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext h)
        · rintro (rfl | h) <;> omega
      have hk : k ∉ Finset.univ.filter (· < k) := by simp
      rw [hset, Finset.sum_insert hk, add_comm]
    rw [hsucc, add_zero]

end Layout

/-!
## The two pairings and the stage matrices
-/

/-- The two pairings of the bonds at the collars (cyclic and box). -/
inductive Pairing
  | cyclic
  | box
  deriving DecidableEq

section Network

variable {m n : ℕ} (L : Fin m → ℕ) (s : ZMod n)

/-- The last block of complementary path `k`. -/
def pathEnd (k : Fin m) : ZMod n := unitPos n L s k (L k + 2)

open Classical in
/-- The block that the bond `ω.2 p` attaches `p` to, in pairing `π`. -/
def bondTarget : Pairing → ZMod n → ZMod n
  | .cyclic, p => p + 1
  | .box, p => if h : ∃ k, p = pathEnd L s k then unitPos n L s h.choose 0 else p + 1

/-- `p` is an outer block of a removed collar: its diagonal is the matched `zI_W`. -/
def IsMatched (S : Finset (Fin m)) (p : ZMod n) : Prop :=
  ∃ j ∈ S, p = unitPos n L s j 0 ∨ p = unitPos n L s j 2

/-- `p` is the middle block of a removed collar (deleted). -/
def IsDeleted (S : Finset (Fin m)) (p : ZMod n) : Prop := ∃ j ∈ S, p = unitPos n L s j 1

/-- `p ∈ C`: a block of path `k` at offset `j` with `buf ≤ j < L k - buf`, i.e. every path block
except a buffer of exactly `buf` blocks at each end of the path. -/
def InSource (buf : ℕ) (p : ZMod n) : Prop :=
  ∃ k : Fin m, ∃ j : ℕ, buf ≤ j ∧ j + buf < L k ∧ p = unitPos n L s k (3 + j)

/-- `p` is one of the three blocks of collar `k`. -/
def InCollar (k : Fin m) (p : ZMod n) : Prop :=
  p = unitPos n L s k 0 ∨ p = unitPos n L s k 1 ∨ p = unitPos n L s k 2

/-- Sites `(block, internal coordinate)`. -/
abbrev RingSite (n W : ℕ) := ZMod n × Fin W

/-- Gaussian coordinates of the ring: diagonal blocks and forward bonds. -/
abbrev RingCoords (n W : ℕ) :=
  (ZMod n → Matrix (Fin W) (Fin W) ℂ) × (ZMod n → Matrix (Fin W) (Fin W) ℂ)

variable {W : ℕ}

open Classical in
/-- Hermitian-type part of the stage matrix: `A_p - e` (or `ξ I` at matched blocks) and
the bonds of pairing `π`. -/
def stageHerm (π : Pairing) (S : Finset (Fin m)) (e ξ : ℝ) (ω : RingCoords n W) :
    Matrix (RingSite n W) (RingSite n W) ℂ :=
  fun x y =>
    (if x.1 = y.1 then
      (if IsMatched L s S x.1 then (if x.2 = y.2 then (ξ : ℂ) else 0)
        else ω.1 x.1 x.2 y.2 - (if x.2 = y.2 then (e : ℂ) else 0)) else 0) +
    (if bondTarget L s π x.1 = y.1 then ω.2 x.1 x.2 y.2 else 0) +
    (if bondTarget L s π y.1 = x.1 then star (ω.2 y.1 y.2 x.2) else 0)

open Classical in
/-- Absorption on block `p`: `η` at matched blocks, `κ/W²` on `C`, else `0`. -/
def stageAbsorption (S : Finset (Fin m)) (buf : ℕ) (κ η : ℝ) (W : ℕ) (p : ZMod n) : ℝ :=
  if IsMatched L s S p then η else if InSource L s buf p then κ / (W : ℝ) ^ 2 else 0

/-- The stage matrix on all sites (before deleting the removed middle blocks). -/
def stageFull (π : Pairing) (S : Finset (Fin m)) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) : Matrix (RingSite n W) (RingSite n W) ℂ :=
  stageHerm L s π S e z.re ω +
    diagonal fun x => ((stageAbsorption L s S buf κ z.im W x.1 : ℝ) : ℂ) * Complex.I

/-- Surviving sites at stage `S`: all sites except removed middle blocks. -/
abbrev StageSite (S : Finset (Fin m)) (W : ℕ) := {x : RingSite n W // ¬ IsDeleted L s S x.1}

/-- The stage matrix `H_κ` of stage `S`: `H^before` at `S`, `H^after` at `insert k S`. -/
def stageMatrix (π : Pairing) (S : Finset (Fin m)) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) : Matrix (StageSite L s S W) (StageSite L s S W) ℂ :=
  (stageFull L s π S e z buf κ ω).submatrix Subtype.val Subtype.val

/-!
### Position lemmas
-/

variable {L s}

theorem unitPos_ne (hL : IsCollarLayout n L) {k k' : Fin m} {o o' : ℕ}
    (ho : o < L k + 3) (ho' : o' < L k' + 3) (h : o ≠ o') :
    unitPos n L s k o ≠ unitPos n L s k' o' := fun he =>
  h ((unitPos_inj hL s ho ho').mp he).2

theorem unitPos_succ (s : ZMod n) (k : Fin m) (o : ℕ) :
    unitPos n L s k o + 1 = unitPos n L s k (o + 1) := by
  have := unitPos_add (L := L) s k o 1
  simpa using this

theorem collar_ne_pathEnd (hL : IsCollarLayout n L) {k j : Fin m} {o : ℕ} (ho : o ≤ 2) :
    unitPos n L s k o ≠ pathEnd L s j := by
  have := hL.2 j; have := hL.2 k
  exact unitPos_ne hL (by omega) (by omega) (by omega)

theorem pathEnd_succ (hL : IsCollarLayout n L) (k : Fin m) :
    pathEnd L s k + 1 = unitPos n L s (finRotate m k) 0 := by
  unfold pathEnd
  rw [unitPos_succ, unitPos_end hL]

theorem bondTarget_of_ne (π : Pairing) {p : ZMod n} (hp : ∀ k, p ≠ pathEnd L s k) :
    bondTarget L s π p = p + 1 := by
  cases π
  · rfl
  · have hn : ¬ ∃ k, p = pathEnd L s k := fun ⟨k, hk⟩ => hp k hk
    simp only [bondTarget, hn, dite_false]

theorem bondTarget_box_pathEnd (hL : IsCollarLayout n L) (k : Fin m) :
    bondTarget L s .box (pathEnd L s k) = unitPos n L s k 0 := by
  simp only [bondTarget]
  have h : ∃ j, pathEnd L s k = pathEnd L s j := ⟨k, rfl⟩
  simp only [h, dite_true]
  have hspec := h.choose_spec
  unfold pathEnd at hspec
  have := (unitPos_inj hL s (by omega) (by omega)).mp hspec
  exact congrArg (fun j => unitPos n L s j 0) this.1.symm

theorem bondTarget_cyclic_pathEnd (hL : IsCollarLayout n L) (k : Fin m) :
    bondTarget L s .cyclic (pathEnd L s k) = unitPos n L s (finRotate m k) 0 :=
  pathEnd_succ hL k

theorem bondTarget_collar (hL : IsCollarLayout n L) (π : Pairing) (k : Fin m) {o : ℕ}
    (ho : o ≤ 2) : bondTarget L s π (unitPos n L s k o) = unitPos n L s k (o + 1) := by
  rw [bondTarget_of_ne π (fun j => collar_ne_pathEnd hL ho), unitPos_succ]

/-- Only the left neighbour bonds into an inner collar position. -/
theorem eq_of_bondTarget_eq (hL : IsCollarLayout n L) (π : Pairing) (k : Fin m) {o : ℕ}
    (ho1 : 1 ≤ o) (ho : o < L k + 3) {q : ZMod n}
    (hq : bondTarget L s π q = unitPos n L s k o) : q = unitPos n L s k (o - 1) := by
  by_cases hpe : ∃ j, q = pathEnd L s j
  · obtain ⟨j, rfl⟩ := hpe
    exfalso
    cases π
    · rw [bondTarget_cyclic_pathEnd hL] at hq
      have := ((unitPos_inj hL s (by omega) ho).mp hq).2; omega
    · rw [bondTarget_box_pathEnd hL] at hq
      have := ((unitPos_inj hL s (by omega) ho).mp hq).2; omega
  · simp only [not_exists] at hpe
    rw [bondTarget_of_ne π hpe] at hq
    have h2 : unitPos n L s k (o - 1) + 1 = unitPos n L s k o := by
      rw [unitPos_succ]; congr 1; omega
    rw [← h2] at hq
    exact add_right_cancel hq

theorem not_deleted_collar (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) {o : ℕ} (ho : o ≤ 2) : ¬ IsDeleted L s S (unitPos n L s k o) := by
  rintro ⟨j, hj, he⟩
  have := hL.2 k; have := hL.2 j
  have h := (unitPos_inj hL s (by omega) (by omega)).mp he
  exact hk (h.1 ▸ hj)

theorem not_matched_collar (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) {o : ℕ} (ho : o ≤ 2) : ¬ IsMatched L s S (unitPos n L s k o) := by
  rintro ⟨j, hj, he | he⟩ <;>
  · have := hL.2 k; have := hL.2 j
    have h := (unitPos_inj hL s (by omega) (by omega)).mp he
    exact hk (h.1 ▸ hj)

theorem not_inSource_collar (hL : IsCollarLayout n L) (buf : ℕ) {k : Fin m} {o : ℕ}
    (ho : o ≤ 2) : ¬ InSource L s buf (unitPos n L s k o) := by
  rintro ⟨j, i, -, hi, he⟩
  have := hL.2 k
  have h := (unitPos_inj hL s (by omega) (by omega)).mp he
  omega

theorem isMatched_insert {S : Finset (Fin m)} {k : Fin m} {p : ZMod n} :
    IsMatched L s (insert k S) p ↔
      (p = unitPos n L s k 0 ∨ p = unitPos n L s k 2) ∨ IsMatched L s S p := by
  simp [IsMatched, Finset.mem_insert, or_and_right, exists_or]

theorem isDeleted_insert {S : Finset (Fin m)} {k : Fin m} {p : ZMod n} :
    IsDeleted L s (insert k S) p ↔ p = unitPos n L s k 1 ∨ IsDeleted L s S p := by
  simp [IsDeleted, Finset.mem_insert, or_and_right, exists_or]

/-!
### Entry lemmas of the stage matrix
-/

theorem stageFull_swap (π : Pairing) (S : Finset (Fin m)) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) {x y : RingSite n W} (h : x.1 ≠ y.1) :
    stageFull L s π S e z buf κ ω y x = star (stageFull L s π S e z buf κ ω x y) := by
  have hxy : x ≠ y := fun he => h (he ▸ rfl)
  simp only [stageFull, stageHerm, Matrix.add_apply, diagonal_apply, h, Ne.symm h,
    hxy, Ne.symm hxy, ite_false, zero_add, add_zero, star_add]
  rw [add_comm]
  congr 1 <;> split_ifs <;> simp

theorem stageFull_insert_eq (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (z : ℂ)
    (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) {x y : RingSite n W}
    (h : x.1 ≠ y.1 ∨ (x.1 ≠ unitPos n L s k 0 ∧ x.1 ≠ unitPos n L s k 2)) :
    stageFull L s π (insert k S) e z buf κ ω x y = stageFull L s π S e z buf κ ω x y := by
  rcases h with h | h
  · have hxy : x ≠ y := fun he => h (he ▸ rfl)
    simp [stageFull, stageHerm, h, hxy]
  · have hm : IsMatched L s (insert k S) x.1 ↔ IsMatched L s S x.1 := by
      rw [isMatched_insert]; tauto
    by_cases hS : IsMatched L s S x.1
    · have hI := hm.mpr hS
      simp [stageFull, stageHerm, stageAbsorption, hS, hI, diagonal_apply]
    · have hI : ¬ IsMatched L s (insert k S) x.1 := fun h' => hS (hm.mp h')
      simp [stageFull, stageHerm, stageAbsorption, hS, hI, diagonal_apply]

/-- The middle block of an unremoved collar couples only to its two outer blocks. -/
theorem stageFull_mid_eq_zero (hL : IsCollarLayout n L) (π : Pairing) (S : Finset (Fin m))
    (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) {x y : RingSite n W}
    (hx : ¬ InCollar L s k x.1) (hy : y.1 = unitPos n L s k 1) :
    stageFull L s π S e z buf κ ω x y = 0 ∧ stageFull L s π S e z buf κ ω y x = 0 := by
  have hne : x.1 ≠ y.1 := fun he => hx (Or.inr (Or.inl (he.trans hy)))
  have hxy : x ≠ y := fun he => hne (he ▸ rfl)
  have h1 : bondTarget L s π x.1 ≠ y.1 := by
    intro he
    rw [hy] at he
    have := eq_of_bondTarget_eq hL π k (le_refl 1) (by have := hL.2 k; omega) he
    exact hx (Or.inl this)
  have h2 : bondTarget L s π y.1 ≠ x.1 := by
    rw [hy, bondTarget_collar hL π k (by norm_num)]
    intro he
    exact hx (Or.inr (Or.inr he.symm))
  constructor
  · simp [stageFull, stageHerm, hne, hxy, h1, h2]
  · simp [stageFull, stageHerm, Ne.symm hne, Ne.symm hxy, h1, h2]

/-!
### The decomposition of one stage
-/

instance (S : Finset (Fin m)) : DecidablePred (IsDeleted L s S) := fun p => by
  unfold IsDeleted; infer_instance

instance (k : Fin m) : DecidablePred (InCollar L s k) := fun p => by
  unfold InCollar; infer_instance

variable (L s)

/-- Position of outer coordinate `i` of collar `k`. -/
abbrev outerPos (k : Fin m) (i : Fin 2) : ZMod n := unitPos n L s k (2 * i.val)

/-- Old interior sites at stage `S` with selected collar `k`. -/
abbrev OldSite (S : Finset (Fin m)) (k : Fin m) (W : ℕ) :=
  {x : RingSite n W // ¬ IsDeleted L s S x.1 ∧ ¬ InCollar L s k x.1}

/-- The two outer coordinates of collar `k` (`i = 0`: left, `i = 1`: right). -/
abbrev outerSite (k : Fin m) (i : Fin 2 × Fin W) : RingSite n W := (outerPos L s k i.1, i.2)

/-- The middle block of collar `k`. -/
abbrev midSite (k : Fin m) (a : Fin W) : RingSite n W := (unitPos n L s k 1, a)

/-- `M_κ`: the old interior matrix (all previously matched diagonals, the source). -/
def oldInterior (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ)
    (κ : ℝ) (ω : RingCoords n W) : Matrix (OldSite L s S k W) (OldSite L s S k W) ℂ :=
  (stageFull L s π S e z buf κ ω).submatrix Subtype.val Subtype.val

/-- `C_o`: the bonds of the old interior to the two selected outer coordinates. -/
def oldCoupling (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ)
    (κ : ℝ) (ω : RingCoords n W) : Matrix (OldSite L s S k W) (Fin 2 × Fin W) ℂ :=
  (stageFull L s π S e z buf κ ω).submatrix Subtype.val (outerSite L s k)

/-- The outer-outer block of the stage matrix (`A - e` for an unremoved collar). -/
def collarOuterOf (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ)
    (κ : ℝ) (ω : RingCoords n W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (stageFull L s π S e z buf κ ω).submatrix (outerSite L s k) (outerSite L s k)

/-- The outer-middle block of the stage matrix (`B`). -/
def collarBondOf (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ)
    (κ : ℝ) (ω : RingCoords n W) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  (stageFull L s π S e z buf κ ω).submatrix (outerSite L s k) (midSite L s k)

/-- The middle-middle block of the stage matrix (`G - e`). -/
def collarMidOf (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ)
    (κ : ℝ) (ω : RingCoords n W) : Matrix (Fin W) (Fin W) ℂ :=
  (stageFull L s π S e z buf κ ω).submatrix (midSite L s k) (midSite L s k)

variable {L s}

theorem outerPos_zero (k : Fin m) : outerPos L s k 0 = unitPos n L s k 0 := rfl
theorem outerPos_one (k : Fin m) : outerPos L s k 1 = unitPos n L s k 2 := rfl

theorem outerPos_inCollar (k : Fin m) (i : Fin 2) : InCollar L s k (outerPos L s k i) := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

theorem outerPos_le (i : Fin 2) : 2 * i.val ≤ 2 := by have := i.isLt; omega

open Classical in
/-- Sites before the stage: old interior, the two outer coordinates, the middle block. -/
def beforeEquiv (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S) :
    StageSite L s S W ≃ OldSite L s S k W ⊕ ((Fin 2 × Fin W) ⊕ Fin W) where
  toFun x :=
    if h : InCollar L s k x.1.1 then
      Sum.inr (if x.1.1 = unitPos n L s k 0 then Sum.inl (0, x.1.2)
        else if x.1.1 = unitPos n L s k 2 then Sum.inl (1, x.1.2) else Sum.inr x.1.2)
    else Sum.inl ⟨x.1, x.2, h⟩
  invFun
    | Sum.inl o => ⟨o.1, o.2.1⟩
    | Sum.inr (Sum.inl i) => ⟨outerSite L s k i, not_deleted_collar hL hk (outerPos_le i.1)⟩
    | Sum.inr (Sum.inr a) => ⟨midSite L s k a, not_deleted_collar hL hk (by norm_num)⟩
  left_inv x := by
    have h02 : unitPos n L s k 0 ≠ unitPos n L s k 2 :=
      unitPos_ne hL (by omega) (by omega) (by norm_num)
    dsimp only
    by_cases h : InCollar L s k x.1.1
    · simp only [h, dite_true]
      rcases h with h | h | h
      · simp only [h, ite_true]
        exact Subtype.ext (Prod.ext h.symm rfl)
      · have h0 : x.1.1 ≠ unitPos n L s k 0 := by
          rw [h]; exact unitPos_ne hL (by omega) (by omega) (by norm_num)
        have h2 : x.1.1 ≠ unitPos n L s k 2 := by
          rw [h]; exact unitPos_ne hL (by omega) (by omega) (by norm_num)
        simp only [h0, h2, ite_false]
        exact Subtype.ext (Prod.ext h.symm rfl)
      · have h0 : x.1.1 ≠ unitPos n L s k 0 := by rw [h]; exact h02.symm
        simp only [h0, ite_false]
        have h2 : x.1.1 = unitPos n L s k 2 := h
        simp only [h2, ite_true]
        exact Subtype.ext (Prod.ext h.symm rfl)
    · simp only [h, dite_false]
  right_inv y := by
    have h02 : unitPos n L s k 0 ≠ unitPos n L s k 2 :=
      unitPos_ne hL (by omega) (by omega) (by norm_num)
    have h01 : unitPos n L s k 1 ≠ unitPos n L s k 0 :=
      unitPos_ne hL (by omega) (by omega) (by norm_num)
    have h21 : unitPos n L s k 1 ≠ unitPos n L s k 2 :=
      unitPos_ne hL (by omega) (by omega) (by norm_num)
    rcases y with o | (⟨i, a⟩ | a)
    · simp only [o.2.2, dite_false]
    · have hc := outerPos_inCollar (L := L) (s := s) k i
      simp only [outerSite, hc, dite_true]
      fin_cases i
      · simp [outerPos]
      · simp [outerPos, h02.symm]
    · have hc : InCollar L s k (unitPos n L s k 1) := Or.inr (Or.inl rfl)
      simp only [midSite, hc, dite_true, h01, h21, ite_false]

open Classical in
/-- Sites after the stage: old interior and the two (now matched) outer coordinates. -/
def afterEquiv (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S) :
    StageSite L s (insert k S) W ≃ OldSite L s S k W ⊕ (Fin 2 × Fin W) where
  toFun x :=
    if h0 : x.1.1 = unitPos n L s k 0 then Sum.inr (0, x.1.2)
    else if h2 : x.1.1 = unitPos n L s k 2 then Sum.inr (1, x.1.2)
    else Sum.inl ⟨x.1, fun h => x.2 (isDeleted_insert.mpr (Or.inr h)), by
      rintro (h | h | h)
      · exact h0 h
      · exact x.2 (isDeleted_insert.mpr (Or.inl h))
      · exact h2 h⟩
  invFun
    | Sum.inl o => ⟨o.1, by
        rw [isDeleted_insert]
        rintro (h | h)
        · exact o.2.2 (Or.inr (Or.inl h))
        · exact o.2.1 h⟩
    | Sum.inr i => ⟨outerSite L s k i, by
        rw [isDeleted_insert]
        rintro (h | h)
        · exact unitPos_ne hL (by have := i.1.isLt; omega) (by omega)
            (by have := i.1.isLt; omega) h
        · exact not_deleted_collar hL hk (outerPos_le i.1) h⟩
  left_inv x := by
    have h02 : unitPos n L s k 0 ≠ unitPos n L s k 2 :=
      unitPos_ne hL (by omega) (by omega) (by norm_num)
    dsimp only
    by_cases h0 : x.1.1 = unitPos n L s k 0
    · simp only [h0, dite_true]
      exact Subtype.ext (Prod.ext h0.symm rfl)
    · by_cases h2 : x.1.1 = unitPos n L s k 2
      · simp only [h0, dite_false]
        simp only [h2, dite_true]
        exact Subtype.ext (Prod.ext h2.symm rfl)
      · simp only [h0, h2, dite_false]
  right_inv y := by
    have h02 : unitPos n L s k 0 ≠ unitPos n L s k 2 :=
      unitPos_ne hL (by omega) (by omega) (by norm_num)
    rcases y with o | ⟨i, a⟩
    · have h0 : o.1.1 ≠ unitPos n L s k 0 := fun h => o.2.2 (Or.inl h)
      have h2 : o.1.1 ≠ unitPos n L s k 2 := fun h => o.2.2 (Or.inr (Or.inr h))
      simp only [h0, h2, dite_false]
    · fin_cases i
      · simp [outerPos]
      · simp [outerPos, h02.symm]

/-- `H^before_κ` in the block form `collarBefore` (old interior, outer, middle). -/
theorem stageMatrix_before_reindex (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) (π : Pairing) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) :
    (stageMatrix L s π S e z buf κ ω).submatrix (beforeEquiv hL hk).symm (beforeEquiv hL hk).symm =
      collarBefore (oldInterior L s π S k e z buf κ ω) (oldCoupling L s π S k e z buf κ ω)
        (oldCoupling L s π S k e z buf κ ω)ᴴ (collarOuterOf L s π S k e z buf κ ω)
        (collarBondOf L s π S k e z buf κ ω) (collarBondOf L s π S k e z buf κ ω)ᴴ
        (collarMidOf L s π S k e z buf κ ω) := by
  have hmidOuter : ∀ (a : Fin W) (i : Fin 2 × Fin W),
      (midSite L s k a).1 ≠ (outerSite L s k i).1 := by
    intro a i
    exact unitPos_ne hL (by omega) (by have := i.1.isLt; omega) (by have := i.1.isLt; omega)
  ext (x | x | x) (y | y | y)
  · rfl
  · rfl
  · exact (stageFull_mid_eq_zero hL π S k e z buf κ ω x.2.2 (y := midSite L s k y) rfl).1
  · simp only [stageMatrix, collarBefore, beforeEquiv, Equiv.coe_fn_symm_mk, submatrix_apply,
      fromBlocks_apply₂₁, fromRows_apply_inl, conjTranspose_apply, oldCoupling]
    exact stageFull_swap π S e z buf κ ω (fun h => y.2.2 (h ▸ outerPos_inCollar k x.1))
  · rfl
  · rfl
  · exact (stageFull_mid_eq_zero hL π S k e z buf κ ω y.2.2 (y := midSite L s k x) rfl).2
  · simp only [stageMatrix, collarBefore, beforeEquiv, Equiv.coe_fn_symm_mk, submatrix_apply,
      fromBlocks_apply₂₂, fromBlocks_apply₂₁, conjTranspose_apply, collarBondOf]
    exact stageFull_swap π S e z buf κ ω (hmidOuter x y).symm
  · rfl

theorem bondTarget_outer_ne (hL : IsCollarLayout n L) (π : Pairing) (k : Fin m) (i j : Fin 2) :
    bondTarget L s π (outerPos L s k i) ≠ outerPos L s k j := by
  simp only [outerPos]
  rw [bondTarget_collar hL π k (outerPos_le i)]
  have := hL.2 k
  exact unitPos_ne hL (by have := i.isLt; omega) (by have := j.isLt; omega) (by omega)

theorem outerPos_inj (hL : IsCollarLayout n L) (k : Fin m) {i j : Fin 2} :
    outerPos L s k i = outerPos L s k j ↔ i = j := by
  constructor
  · intro h
    have := ((unitPos_inj hL s (by have := i.isLt; omega) (by have := j.isLt; omega)).mp h).2
    exact Fin.ext (by omega)
  · rintro rfl; rfl

/-- After the stage the two outer coordinates carry the matched scalar diagonal `z I`. -/
theorem stageFull_outer_after (hL : IsCollarLayout n L) (π : Pairing) (S : Finset (Fin m))
    (k : Fin m) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) (i j : Fin 2 × Fin W) :
    stageFull L s π (insert k S) e z buf κ ω (outerSite L s k i) (outerSite L s k j) =
      (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) i j := by
  have hb1 := bondTarget_outer_ne (s := s) hL π k i.1 j.1
  have hb2 := bondTarget_outer_ne (s := s) hL π k j.1 i.1
  have hm' : ∀ i : Fin 2, IsMatched L s (insert k S) (outerPos L s k i) := by
    intro i
    rw [isMatched_insert]
    left
    fin_cases i <;> simp [outerPos]
  have hm := hm' i.1
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  by_cases hij : i = j
  · subst hij
    simp only [stageFull, stageHerm, stageAbsorption, outerSite, Matrix.add_apply,
      diagonal_apply, hm, hb1, ite_true, ite_false, add_zero, Matrix.smul_apply, one_apply,
      Prod.mk.injEq, true_and, smul_eq_mul]
    split_ifs
    · conv_rhs => rw [← Complex.re_add_im z]
      ring
    · simp
  · have hpos : outerPos L s k i ≠ outerPos L s k j := fun h => hij ((outerPos_inj hL k).mp h)
    simp only [stageFull, stageHerm, outerSite, Matrix.add_apply, diagonal_apply, hpos, hb1, hb2,
      ite_false, add_zero, Matrix.smul_apply, one_apply, Prod.mk.injEq, hij, false_and,
      smul_eq_mul, mul_zero]

/-- `H^after_κ` in the block form `collarAfter`, with the same `M_κ`, `C_o` as before. -/
theorem stageMatrix_after_reindex (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) (π : Pairing) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) :
    (stageMatrix L s π (insert k S) e z buf κ ω).submatrix (afterEquiv hL hk).symm
        (afterEquiv hL hk).symm =
      collarAfter (oldInterior L s π S k e z buf κ ω) (oldCoupling L s π S k e z buf κ ω)
        (oldCoupling L s π S k e z buf κ ω)ᴴ z := by
  have hold : ∀ (x : OldSite L s S k W) (i : Fin 2 × Fin W),
      x.1.1 ≠ (outerSite L s k i).1 := fun x i h => x.2.2 (h ▸ outerPos_inCollar k i.1)
  ext (x | x) (y | y)
  · simp only [stageMatrix, collarAfter, afterEquiv, Equiv.coe_fn_symm_mk, submatrix_apply,
      fromBlocks_apply₁₁, oldInterior]
    exact stageFull_insert_eq π S k e z buf κ ω
      (Or.inr ⟨fun h => x.2.2 (Or.inl h), fun h => x.2.2 (Or.inr (Or.inr h))⟩)
  · simp only [stageMatrix, collarAfter, afterEquiv, Equiv.coe_fn_symm_mk, submatrix_apply,
      fromBlocks_apply₁₂, oldCoupling]
    exact stageFull_insert_eq π S k e z buf κ ω (Or.inl (hold x y))
  · simp only [stageMatrix, collarAfter, afterEquiv, Equiv.coe_fn_symm_mk, submatrix_apply,
      fromBlocks_apply₂₁, conjTranspose_apply, oldCoupling]
    rw [stageFull_insert_eq π S k e z buf κ ω (Or.inl (hold y x).symm)]
    exact stageFull_swap π S e z buf κ ω (hold y x)
  · simp only [stageMatrix, collarAfter, afterEquiv, Equiv.coe_fn_symm_mk, submatrix_apply,
      fromBlocks_apply₂₂]
    exact stageFull_outer_after hL π S k e z buf κ ω x y

/-!
### The fresh collar and the source-independent prefactor
-/

/-- Gaussian coordinates of one collar: the three diagonals `A, G, A` (offsets `0, 1, 2`) and the
two internal bonds (offset `0`: left outer–middle, offset `1`: middle–right outer). -/
abbrev CollarSample (W : ℕ) :=
  (Fin 3 → Matrix (Fin W) (Fin W) ℂ) × (Fin 2 → Matrix (Fin W) (Fin W) ℂ)

variable (L s) in
/-- The fresh variables of collar `k`. -/
def freshCollar (k : Fin m) (ω : RingCoords n W) : CollarSample W :=
  (fun o => ω.1 (unitPos n L s k o.val), fun o => ω.2 (unitPos n L s k o.val))

/-- `A - e` on the two outer coordinates: `diag(A_left - e, A_right - e)`. -/
def collarOuterBlock (e : ℝ) (C : CollarSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  fun x y => if x.1 = y.1 then
    C.1 ⟨2 * x.1.val, by have := x.1.isLt; omega⟩ x.2 y.2 - (if x.2 = y.2 then (e : ℂ) else 0)
    else 0

/-- `B`: the two internal bonds from the outer coordinates to the middle block. -/
def collarBondBlock (C : CollarSample W) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  fun x b => if x.1 = 0 then C.2 0 x.2 b else star (C.2 1 b x.2)

/-- `G - e`. -/
def collarMidBlock (e : ℝ) (C : CollarSample W) : Matrix (Fin W) (Fin W) ℂ :=
  C.1 1 - (e : ℂ) • 1

/-- `K_c = A - e - ξ - B(G-e)⁻¹B*`. -/
def collarKc (e ξ : ℝ) (C : CollarSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  collarK ξ (collarOuterBlock e C) (collarBondBlock C) (collarBondBlock C)ᴴ (collarMidBlock e C)

/-- The source-independent prefactor `det(G-e) det(K_c+iη)/(2iη)^{2W}` of
the stage factorization; a function of the fresh collar and `(e, z)` only. -/
def collarPrefactor (e : ℝ) (z : ℂ) (C : CollarSample W) : ℂ :=
  (collarMidBlock e C).det * ((collarKc e z.re C + ((z.im : ℂ) * Complex.I) • 1).det /
    (((2 * z.im : ℝ) : ℂ) * Complex.I) ^ (2 * W))

/-- For an unremoved collar the outer block is `diag(A_left - e, A_right - e)`. -/
theorem collarOuterOf_eq (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) (π : Pairing) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) :
    collarOuterOf L s π S k e z buf κ ω = collarOuterBlock e (freshCollar L s k ω) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have hb1 := bondTarget_outer_ne (s := s) hL π k i j
  have hb2 := bondTarget_outer_ne (s := s) hL π k j i
  have hnm := not_matched_collar (s := s) hL hk (outerPos_le i)
  have hns := not_inSource_collar (L := L) (s := s) hL buf (k := k) (outerPos_le i)
  by_cases hij : i = j
  · subst hij
    simp only [collarOuterOf, collarOuterBlock, freshCollar, stageFull, stageHerm,
      stageAbsorption, submatrix_apply, outerSite, outerPos, Matrix.add_apply, diagonal_apply,
      hb1, ite_true, ite_false, add_zero, Prod.mk.injEq, true_and]
    simp only [hnm, hns, ite_false, Complex.ofReal_zero, zero_mul, ite_self, add_zero]
  · have hpos : outerPos L s k i ≠ outerPos L s k j := fun h => hij ((outerPos_inj hL k).mp h)
    simp only [collarOuterOf, collarOuterBlock, stageFull, stageHerm, submatrix_apply, outerSite,
      Matrix.add_apply, diagonal_apply, hpos, hb1, hb2, hij, ite_false, add_zero,
      Prod.mk.injEq, false_and]

/-- The outer-middle block is the pair of internal bonds `B`. -/
theorem collarBondOf_eq (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m)
    (π : Pairing) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) :
    collarBondOf L s π S k e z buf κ ω = collarBondBlock (freshCollar L s k ω) := by
  have hLk := hL.2 k
  ext ⟨i, a⟩ b
  have hmid : bondTarget L s π (unitPos n L s k 1) = unitPos n L s k 2 :=
    bondTarget_collar hL π k (by norm_num)
  fin_cases i
  · have hne : unitPos n L s k 0 ≠ unitPos n L s k 1 :=
      unitPos_ne hL (by omega) (by omega) (by norm_num)
    have h1 : bondTarget L s π (unitPos n L s k 0) = unitPos n L s k 1 :=
      bondTarget_collar hL π k (by norm_num)
    have h2 : unitPos n L s k 2 ≠ unitPos n L s k 0 :=
      unitPos_ne hL (by omega) (by omega) (by norm_num)
    simp [collarBondOf, collarBondBlock, freshCollar, stageFull, stageHerm, outerPos, hne,
      h1, hmid, h2]
  · have hne : unitPos n L s k 2 ≠ unitPos n L s k 1 :=
      unitPos_ne hL (by omega) (by omega) (by norm_num)
    have h1 : bondTarget L s π (unitPos n L s k 2) = unitPos n L s k 3 :=
      bondTarget_collar hL π k (by norm_num)
    have h3 : unitPos n L s k 3 ≠ unitPos n L s k 1 :=
      unitPos_ne hL (by omega) (by omega) (by norm_num)
    simp [collarBondOf, collarBondBlock, freshCollar, stageFull, stageHerm, outerPos, hne,
      h1, hmid, h3]

/-- The middle block is `G - e`. -/
theorem collarMidOf_eq (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m)
    (π : Pairing) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) :
    collarMidOf L s π S k e z buf κ ω = collarMidBlock e (freshCollar L s k ω) := by
  have hLk := hL.2 k
  have hnm : ¬ IsMatched L s S (unitPos n L s k 1) := by
    rintro ⟨j, -, he | he⟩ <;>
    · have := hL.2 j
      have := ((unitPos_inj hL s (by omega) (by omega)).mp he).2
      omega
  have hns := not_inSource_collar (L := L) (s := s) hL buf (k := k) (o := 1) (by norm_num)
  have hmid : bondTarget L s π (unitPos n L s k 1) = unitPos n L s k 2 :=
    bondTarget_collar hL π k (by norm_num)
  have h21 : unitPos n L s k 2 ≠ unitPos n L s k 1 :=
    unitPos_ne hL (by omega) (by omega) (by norm_num)
  ext a b
  simp [collarMidOf, collarMidBlock, freshCollar, stageFull, stageHerm, stageAbsorption,
    diagonal_apply, hnm, hns, hmid, h21, Matrix.one_apply]

/-!
### Item (iii): the exact stage factorization
-/

/-- The stage factorization at every stage of either pairing, on the event that the
displayed inverses exist. -/
theorem stageMatrix_factorization [NeZero n] (hL : IsCollarLayout n L) {S : Finset (Fin m)}
    {k : Fin m} (hk : k ∉ S) (π : Pairing) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W)
    (hM : IsUnit (oldInterior L s π S k e z buf κ ω).det)
    (hG : IsUnit (collarMidBlock e (freshCollar L s k ω)).det)
    (hK : IsUnit (collarKc e z.re (freshCollar L s k ω) + ((z.im : ℂ) * Complex.I) • 1).det)
    (hX : IsUnit (z • 1 - oldSchur (oldInterior L s π S k e z buf κ ω)
        (oldCoupling L s π S k e z buf κ ω) (oldCoupling L s π S k e z buf κ ω)ᴴ).det)
    (hη : z.im ≠ 0) :
    (stageMatrix L s π S e z buf κ ω).det / (stageMatrix L s π (insert k S) e z buf κ ω).det =
      collarPrefactor e z (freshCollar L s k ω) *
        (1 - collarU z.im (collarKc e z.re (freshCollar L s k ω)) *
          oldResponse z (oldSchur (oldInterior L s π S k e z buf κ ω)
            (oldCoupling L s π S k e z buf κ ω) (oldCoupling L s π S k e z buf κ ω)ᴴ)).det := by
  rw [← det_submatrix_equiv_self (beforeEquiv hL hk).symm,
    ← det_submatrix_equiv_self (afterEquiv hL hk).symm,
    stageMatrix_before_reindex hL hk, stageMatrix_after_reindex hL hk,
    collarOuterOf_eq hL hk, collarBondOf_eq hL, collarMidOf_eq hL]
  rw [collar_stage_factorization _ _ _ _ _ _ _ z hM hG hK hX hη]
  simp only [collarPrefactor, collarKc, Fintype.card_prod, Fintype.card_fin]

/-!
### The Hermitian structure: only the real inverses need to exist
-/

/-- The Hermitian-type part is Hermitian when all diagonal samples are. -/
theorem stageHerm_isHermitian (π : Pairing) (S : Finset (Fin m)) (e ξ : ℝ) (ω : RingCoords n W)
    (hA : ∀ p, (ω.1 p).IsHermitian) : (stageHerm L s π S e ξ ω).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨p, a⟩ ⟨q, b⟩
  simp only [stageHerm, star_add]
  rw [add_assoc, add_assoc]
  congr 1
  · by_cases h : q = p
    · subst h
      simp only [ite_true]
      by_cases hm : IsMatched L s S q
      · simp only [hm, ite_true]
        split_ifs <;> simp_all
      · simp only [hm, ite_false, star_sub]
        rw [(hA q).apply]
        congr 1
        split_ifs <;> simp_all
    · have h' : ¬ p = q := fun e => h e.symm
      simp [h, h']
  · rw [add_comm]
    congr 1 <;> split_ifs <;> simp

theorem stageAbsorption_nonneg (S : Finset (Fin m)) (buf : ℕ) {κ η : ℝ} (hκ : 0 ≤ κ)
    (hη : 0 ≤ η) (p : ZMod n) : 0 ≤ stageAbsorption L s S buf κ η W p := by
  unfold stageAbsorption
  split_ifs
  · exact hη
  · positivity
  · exact le_refl 0

/-- `M_κ` has numerical range in the closed upper half-plane (Hermitian samples, `κ ≥ 0`,
`Im z ≥ 0`). -/
theorem oldInterior_numRange [NeZero n] (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (e : ℝ)
    (z : ℂ) (buf : ℕ) {κ : ℝ} (ω : RingCoords n W) (hA : ∀ p, (ω.1 p).IsHermitian)
    (hκ : 0 ≤ κ) (hz : 0 ≤ z.im) (u : OldSite L s S k W → ℂ) :
    0 ≤ (star u ⬝ᵥ oldInterior L s π S k e z buf κ ω *ᵥ u).im := by
  have hdec : oldInterior L s π S k e z buf κ ω =
      (stageHerm L s π S e z.re ω).submatrix Subtype.val Subtype.val +
        diagonal fun x : OldSite L s S k W =>
          ((stageAbsorption L s S buf κ z.im W x.1.1 : ℝ) : ℂ) * Complex.I := by
    ext x y
    simp only [oldInterior, stageFull, submatrix_apply, Matrix.add_apply, diagonal_apply,
      Subtype.ext_iff]
  rw [hdec]
  exact im_star_dotProduct_herm_add_diag_nonneg _
    ((stageHerm_isHermitian π S e z.re ω hA).submatrix _) _
    (fun x => stageAbsorption_nonneg S buf hκ hz _) u

theorem collarOuterBlock_isHermitian (e : ℝ) (C : CollarSample W) (hA : ∀ o, (C.1 o).IsHermitian) :
    (collarOuterBlock e C).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  simp only [collarOuterBlock]
  by_cases hij : j = i
  · subst hij
    simp only [ite_true, star_sub]
    rw [(hA _).apply]
    congr 1
    split_ifs <;> simp_all
  · have hij' : ¬ i = j := fun h => hij h.symm
    simp [hij, hij']

theorem collarMidBlock_isHermitian (e : ℝ) (C : CollarSample W) (hA : ∀ o, (C.1 o).IsHermitian) :
    (collarMidBlock e C).IsHermitian := by
  unfold collarMidBlock
  refine (hA 1).sub ?_
  simp [IsHermitian, conjTranspose_smul]

/-- The stage factorization for Hermitian diagonal samples, a nonnegative source and
`Im z > 0`: it holds whenever the two real inverses `M_κ⁻¹` and `(G-e)⁻¹` exist. -/
theorem stageMatrix_factorization_of_hermitian [NeZero n] (hL : IsCollarLayout n L)
    {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S) (π : Pairing) (e : ℝ) (z : ℂ) (buf : ℕ)
    {κ : ℝ} (ω : RingCoords n W) (hA : ∀ p, (ω.1 p).IsHermitian) (hκ : 0 ≤ κ) (hz : 0 < z.im)
    (hM : IsUnit (oldInterior L s π S k e z buf κ ω).det)
    (hG : IsUnit (collarMidBlock e (freshCollar L s k ω)).det) :
    (stageMatrix L s π S e z buf κ ω).det / (stageMatrix L s π (insert k S) e z buf κ ω).det =
      collarPrefactor e z (freshCollar L s k ω) *
        (1 - collarU z.im (collarKc e z.re (freshCollar L s k ω)) *
          oldResponse z (oldSchur (oldInterior L s π S k e z buf κ ω)
            (oldCoupling L s π S k e z buf κ ω) (oldCoupling L s π S k e z buf κ ω)ᴴ)).det := by
  have hC : ∀ o, ((freshCollar L s k ω).1 o).IsHermitian := fun o => hA _
  refine stageMatrix_factorization hL hk π e z buf κ ω hM hG ?_ ?_ hz.ne'
  · exact isUnit_det_hermitian_add _ (collarK_isHermitian _ _
      (collarOuterBlock_isHermitian e _ hC) (collarMidBlock_isHermitian e _ hC)) hz
  · exact isUnit_det_sub_oldSchur _ _ hM
      (oldInterior_numRange π S k e z buf ω hA hκ hz.le) hz

/-!
### Item (iii), second clause: the two pairings end at the same fully matched model
-/

variable (L s) in
open Classical in
/-- Move the left outer coordinate of every collar `k` to that of collar `f k`; identity on
every other block position. -/
def leftOuterShift (f : Equiv.Perm (Fin m)) (p : ZMod n) : ZMod n :=
  if h : ∃ k, p = unitPos n L s k 0 then unitPos n L s (f h.choose) 0 else p

theorem collarShift_start (hL : IsCollarLayout n L) (f : Equiv.Perm (Fin m)) (k : Fin m) :
    leftOuterShift L s f (unitPos n L s k 0) = unitPos n L s (f k) 0 := by
  have h : ∃ j, unitPos n L s k 0 = unitPos n L s j 0 := ⟨k, rfl⟩
  simp only [leftOuterShift, h, dite_true]
  have := ((unitPos_inj hL s (by omega) (by omega)).mp h.choose_spec).1
  exact congrArg (fun j => unitPos n L s (f j) 0) this.symm

theorem collarShift_of_ne (f : Equiv.Perm (Fin m)) {p : ZMod n}
    (hp : ∀ k, p ≠ unitPos n L s k 0) : leftOuterShift L s f p = p := by
  have h : ¬ ∃ k, p = unitPos n L s k 0 := fun ⟨k, hk⟩ => hp k hk
  simp only [leftOuterShift, h, dite_false]

theorem collarShift_symm (hL : IsCollarLayout n L) (f : Equiv.Perm (Fin m)) (p : ZMod n) :
    leftOuterShift L s f.symm (leftOuterShift L s f p) = p := by
  by_cases h : ∃ k, p = unitPos n L s k 0
  · obtain ⟨k, rfl⟩ := h
    rw [collarShift_start hL, collarShift_start hL, Equiv.symm_apply_apply]
  · simp only [not_exists] at h
    rw [collarShift_of_ne f h, collarShift_of_ne f.symm h]

variable (L s) in
/-- The deterministic permutation of block positions identifying the two final models. -/
def finalPerm (hL : IsCollarLayout n L) : Equiv.Perm (ZMod n) where
  toFun := leftOuterShift L s (finRotate m)
  invFun := leftOuterShift L s (finRotate m).symm
  left_inv p := collarShift_symm hL _ p
  right_inv p := by
    have := collarShift_symm (s := s) hL (finRotate m).symm p
    rwa [Equiv.symm_symm] at this

theorem isDeleted_collarShift (hL : IsCollarLayout n L) (S : Finset (Fin m))
    (f : Equiv.Perm (Fin m)) (p : ZMod n) :
    IsDeleted L s S (leftOuterShift L s f p) ↔ IsDeleted L s S p := by
  by_cases h : ∃ k, p = unitPos n L s k 0
  · obtain ⟨k, rfl⟩ := h
    rw [collarShift_start hL]
    have hnd : ∀ j : Fin m, ¬ IsDeleted L s S (unitPos n L s j 0) := by
      rintro j ⟨i, -, he⟩
      have := hL.2 j; have := hL.2 i
      have := ((unitPos_inj hL s (by omega) (by omega)).mp he).2
      omega
    exact iff_of_false (hnd _) (hnd _)
  · simp only [not_exists] at h
    rw [collarShift_of_ne f h]

variable (L s) in
/-- The site permutation of the fully matched models (`Equiv` on the surviving sites). -/
def finalSitePerm (hL : IsCollarLayout n L) :
    StageSite L s (Finset.univ : Finset (Fin m)) W ≃ StageSite L s Finset.univ W :=
  Equiv.subtypeEquiv ((finalPerm L s hL).prodCongr (Equiv.refl _))
    (fun x => not_congr (isDeleted_collarShift hL _ _ x.1).symm)

theorem pred_of_succ_eq_start (hL : IsCollarLayout n L) {p : ZMod n} {i : Fin m}
    (h : p + 1 = unitPos n L s i 0) : p = pathEnd L s ((finRotate m).symm i) := by
  have := pathEnd_succ (s := s) hL ((finRotate m).symm i)
  rw [Equiv.apply_symm_apply, ← h] at this
  exact (add_right_cancel this).symm

theorem start_ne_mid (hL : IsCollarLayout n L) (i j : Fin m) :
    unitPos n L s i 0 ≠ unitPos n L s j 1 := by
  have := hL.2 i; have := hL.2 j
  exact unitPos_ne hL (by omega) (by omega) (by norm_num)

theorem isMatched_univ_iff (p : ZMod n) :
    IsMatched L s Finset.univ p ↔ ∃ j, p = unitPos n L s j 0 ∨ p = unitPos n L s j 2 := by
  simp [IsMatched]

theorem isMatched_collarShift (hL : IsCollarLayout n L) (f : Equiv.Perm (Fin m)) (p : ZMod n) :
    IsMatched L s Finset.univ (leftOuterShift L s f p) ↔ IsMatched L s Finset.univ p := by
  by_cases h : ∃ k, p = unitPos n L s k 0
  · obtain ⟨k, rfl⟩ := h
    rw [collarShift_start hL, isMatched_univ_iff, isMatched_univ_iff]
    exact iff_of_true ⟨_, Or.inl rfl⟩ ⟨_, Or.inl rfl⟩
  · simp only [not_exists] at h
    rw [collarShift_of_ne f h]

theorem inSource_collarShift (hL : IsCollarLayout n L) (buf : ℕ) (f : Equiv.Perm (Fin m))
    (p : ZMod n) : InSource L s buf (leftOuterShift L s f p) ↔ InSource L s buf p := by
  by_cases h : ∃ k, p = unitPos n L s k 0
  · obtain ⟨k, rfl⟩ := h
    rw [collarShift_start hL]
    exact iff_of_false (not_inSource_collar hL buf (by norm_num))
      (not_inSource_collar hL buf (by norm_num))
  · simp only [not_exists] at h
    rw [collarShift_of_ne f h]

/-- The bonds of the two fully matched models correspond under `finalPerm`. -/
theorem bondTarget_final (hL : IsCollarLayout n L) {p q : ZMod n}
    (hp : ¬ IsDeleted L s Finset.univ p) (hq : ¬ IsDeleted L s Finset.univ q) :
    (bondTarget L s .box p = q ↔
      bondTarget L s .cyclic (finalPerm L s hL p) = finalPerm L s hL q) ∧
    (bondTarget L s .box p = q → finalPerm L s hL p = p) := by
  have hq' : ¬ IsDeleted L s Finset.univ (finalPerm L s hL q) :=
    (not_congr (isDeleted_collarShift hL _ _ q)).mpr hq
  have hmid : ∀ r : ZMod n, ¬ IsDeleted L s Finset.univ r → ∀ j : Fin m, r ≠ unitPos n L s j 1 :=
    fun r hr j he => hr ⟨j, Finset.mem_univ _, he⟩
  by_cases hpc : ∃ k, p = unitPos n L s k 0
  · obtain ⟨k, rfl⟩ := hpc
    have h1 : bondTarget L s .box (unitPos n L s k 0) ≠ q := by
      rw [bondTarget_collar hL _ k (by norm_num)]
      exact fun he => hmid q hq k he.symm
    have h2 : bondTarget L s .cyclic (finalPerm L s hL (unitPos n L s k 0)) ≠
        finalPerm L s hL q := by
      change bondTarget L s .cyclic (leftOuterShift L s _ _) ≠ _
      rw [collarShift_start hL, bondTarget_collar hL _ _ (by norm_num)]
      exact fun he => hmid _ hq' _ he.symm
    exact ⟨iff_of_false h1 h2, fun h => absurd h h1⟩
  · simp only [not_exists] at hpc
    have hσp : finalPerm L s hL p = p := collarShift_of_ne _ hpc
    refine ⟨?_, fun _ => hσp⟩
    rw [hσp]
    by_cases hpe : ∃ j, p = pathEnd L s j
    · obtain ⟨j, rfl⟩ := hpe
      rw [bondTarget_box_pathEnd hL, bondTarget_cyclic_pathEnd hL]
      constructor
      · rintro rfl
        exact (collarShift_start hL _ j).symm
      · intro h
        by_cases hqc : ∃ i, q = unitPos n L s i 0
        · obtain ⟨i, rfl⟩ := hqc
          change _ = leftOuterShift L s _ _ at h
          rw [collarShift_start hL] at h
          have := ((unitPos_inj hL s (by omega) (by omega)).mp h).1
          rw [(finRotate m).injective this]
        · simp only [not_exists] at hqc
          change _ = leftOuterShift L s _ _ at h
          rw [collarShift_of_ne _ hqc] at h
          exact absurd h.symm (hqc _)
    · simp only [not_exists] at hpe
      rw [bondTarget_of_ne _ hpe, bondTarget_of_ne _ hpe]
      by_cases hqc : ∃ i, q = unitPos n L s i 0
      · obtain ⟨i, rfl⟩ := hqc
        change _ ↔ _ = leftOuterShift L s _ _
        rw [collarShift_start hL]
        refine iff_of_false (fun h => hpe _ (pred_of_succ_eq_start hL h)) (fun h => ?_)
        have := pred_of_succ_eq_start hL h
        rw [Equiv.symm_apply_apply] at this
        exact hpe _ this
      · simp only [not_exists] at hqc
        change _ ↔ _ = leftOuterShift L s _ _
        rw [collarShift_of_ne _ hqc]

/-- Item (iii), last clause: the fully matched final models of the two pairings agree up to the
deterministic permutation `finalSitePerm` of the auxiliary (left outer) coordinates. -/
theorem final_models_agree (hL : IsCollarLayout n L) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) :
    stageMatrix L s .box Finset.univ e z buf κ ω =
      (stageMatrix L s .cyclic Finset.univ e z buf κ ω).submatrix (finalSitePerm L s hL)
        (finalSitePerm L s hL) := by
  ext ⟨⟨p, a⟩, hp⟩ ⟨⟨q, b⟩, hq⟩
  simp only [stageMatrix, submatrix_apply, finalSitePerm, Equiv.subtypeEquiv_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq]
  obtain ⟨hb1, hb1'⟩ := bondTarget_final (s := s) (p := p) (q := q) hL hp hq
  obtain ⟨hb2, hb2'⟩ := bondTarget_final (s := s) (p := q) (q := p) hL hq hp
  set σ := finalPerm L s hL
  have hσinj : σ p = σ q ↔ p = q := σ.injective.eq_iff
  have hσm : IsMatched L s Finset.univ (σ p) ↔ IsMatched L s Finset.univ p :=
    isMatched_collarShift hL _ p
  have hσs : InSource L s buf (σ p) ↔ InSource L s buf p := inSource_collarShift hL buf _ p
  have hfix : ¬ IsMatched L s Finset.univ p → σ p = p := by
    intro hm
    apply collarShift_of_ne
    intro k hk
    exact hm ((isMatched_univ_iff p).mpr ⟨k, Or.inl hk⟩)
  simp only [stageFull, stageHerm, stageAbsorption, Matrix.add_apply, diagonal_apply,
    Prod.mk.injEq]
  congr 1
  · congr 1
    · congr 1
      · by_cases hpq : p = q
        · subst hpq
          simp only [ite_true]
          by_cases hm : IsMatched L s Finset.univ p
          · simp [hm, hσm.mpr hm]
          · simp [hm, hfix hm]
        · simp [hpq, (not_congr hσinj).mpr hpq]
      · by_cases h : bondTarget L s .box p = q
        · have h1 := hb1.mp h
          simp only [h, h1, ite_true]
          rw [hb1' h]
        · simp [h, (not_congr hb1).mp h]
    · by_cases h : bondTarget L s .box q = p
      · have h1 := hb2.mp h
        simp only [h, h1, ite_true]
        rw [hb2' h]
      · simp [h, (not_congr hb2).mp h]
  · by_cases hpq : p = q
    · subst hpq
      by_cases hm : IsMatched L s Finset.univ p
      · simp [hm, hσm.mpr hm]
      · by_cases hs : InSource L s buf p
        · simp [hm, (not_congr hσm).mpr hm, hs, hσs.mpr hs]
        · simp [hm, (not_congr hσm).mpr hm, hs, (not_congr hσs).mpr hs]
    · simp [hpq, (not_congr hσinj).mpr hpq]

end Network

end BlockBand.Endpoints
