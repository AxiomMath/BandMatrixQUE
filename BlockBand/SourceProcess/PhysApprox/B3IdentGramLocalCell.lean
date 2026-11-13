module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalAlg
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramPassStop
public import BlockBand.SourceProcess.PhysApprox.B3Ident2KGrid

/-!
# The grid and the discrete jumps

The grid `t_j = cellT s W a t j` of `[a, t]`, `p = ⌊W(s+a)⌋`, `q = ⌊W(s+t)⌋`:
* `cellT_eq_of_lt`: `t_j = j/W − s` for `p < j ≤ q`; `limLenAll_cellT`: the length at `t_j` is
  `j` for `p ≤ j ≤ q`; **`limLenAll_of_cell`**: it is `j` on `[t_j, t_{j+1})`;
* `cellT_succ_sub_le`: `t_{j+1} − t_j ≤ 1/W`; `cellT_succ_sub_eq`: `= 1/W` for `p < j < q`;
* **`gramJ_eq_b3JumpAt`**: off a birth length, the limit jumps `gramJ u` are the discrete jumps
  `b3JumpAt` at the length `limLenAll s W u` (the grid point `t_j = τ_i − s` with
  `W τ_i = j ∈ ℕ` is exactly where they differ);
* `b3JumpAt_succ`, `b3BirthAt_eq_zero`: the discrete jumps step by the births.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal

variable {K np : ℕ}

/-!
## The grid
-/

section Grid

variable {s : ℝ} {W : ℕ} {a t : ℝ≥0}

theorem coe_cellT (s : ℝ) (W : ℕ) (a t : ℝ≥0) (j : ℕ) :
    (cellT s W a t j : ℝ) = max (a : ℝ) (min (t : ℝ) (max ((j : ℝ) / W - s) 0)) := by
  simp [cellT, NNReal.coe_max, NNReal.coe_min, Real.coe_toNNReal']

theorem le_limLenAll {u : ℝ≥0} {j : ℕ} (h : (j : ℝ) ≤ W * (s + u)) :
    j ≤ limLenAll s W u :=
  Nat.le_floor h

theorem limLenAll_le_mul (hs : 0 ≤ s) (u : ℝ≥0) : (limLenAll s W u : ℝ) ≤ W * (s + u) :=
  Nat.floor_le (mul_nonneg (Nat.cast_nonneg W) (by positivity))

theorem lt_limLenAll_add_one (u : ℝ≥0) : (W : ℝ) * (s + u) < limLenAll s W u + 1 :=
  Nat.lt_floor_add_one _

/-- `t_j = j/W − s` for `p < j ≤ q`. -/
theorem cellT_eq_of_lt (hs : 0 ≤ s) (hW : 1 ≤ W) {j : ℕ} (hpj : limLenAll s W a < j)
    (hjq : j ≤ limLenAll s W t) : (cellT s W a t j : ℝ) = (j : ℝ) / W - s := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : (W : ℝ) * (s + a) < j := by
    have := lt_limLenAll_add_one (s := s) (W := W) a
    have h2 : ((limLenAll s W a : ℕ) : ℝ) + 1 ≤ j := by exact_mod_cast hpj
    linarith
  have h2 : (j : ℝ) ≤ W * (s + t) := (Nat.cast_le.2 hjq).trans (limLenAll_le_mul hs t)
  have h3 : (a : ℝ) < (j : ℝ) / W - s := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hW0]; linarith
  have h4 : (j : ℝ) / W - s ≤ t := by
    rw [sub_le_iff_le_add, div_le_iff₀ hW0]; linarith
  rw [coe_cellT, max_eq_left (by linarith [a.2] : (0 : ℝ) ≤ (j : ℝ) / W - s),
    min_eq_right h4, max_eq_right h3.le]

theorem limLenAll_cellT (hs : 0 ≤ s) (hW : 1 ≤ W) {j : ℕ} (hpj : limLenAll s W a ≤ j)
    (hjq : j ≤ limLenAll s W t) : limLenAll s W (cellT s W a t j) = j := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rcases eq_or_lt_of_le hpj with h | h
  · subst h; rw [cellT_first hs hW]
  · have e := cellT_eq_of_lt hs hW h hjq
    unfold limLenAll
    rw [e]
    have : (W : ℝ) * (s + ((j : ℝ) / W - s)) = j := by field_simp; ring
    rw [this, Nat.floor_natCast]

/-- **The length is `j` on the cell `[t_j, t_{j+1})`.** -/
theorem limLenAll_of_cell (hs : 0 ≤ s) (hW : 1 ≤ W) {j : ℕ} (hpj : limLenAll s W a ≤ j)
    (hjq : j ≤ limLenAll s W t) {u : ℝ≥0} (h1 : cellT s W a t j ≤ u)
    (h2 : u < cellT s W a t (j + 1)) : limLenAll s W u = j := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hlo : j ≤ limLenAll s W u := by
    rw [← limLenAll_cellT hs hW hpj hjq]
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left (by
      have : (cellT s W a t j : ℝ) ≤ u := h1
      linarith) (Nat.cast_nonneg W))
  have hau : (a : ℝ) ≤ u := (le_max_left (a : ℝ≥0) _).trans h1
  have h2' : (u : ℝ) < cellT s W a t (j + 1) := h2
  rw [coe_cellT] at h2'
  have hu : (u : ℝ) < ((j + 1 : ℕ) : ℝ) / W - s := by
    rcases le_total (a : ℝ) (min (t : ℝ) (max (((j + 1 : ℕ) : ℝ) / W - s) 0)) with hm | hm
    · rw [max_eq_right hm] at h2'
      have h3 := h2'.trans_le (min_le_right _ _)
      rcases le_total (((j + 1 : ℕ) : ℝ) / W - s) 0 with h4 | h4
      · rw [max_eq_right h4] at h3; exact absurd h3 (not_lt.2 u.2)
      · rwa [max_eq_left h4] at h3
    · rw [max_eq_left hm] at h2'; linarith
  have hup : limLenAll s W u < j + 1 := by
    unfold limLenAll
    refine (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg W) (by positivity))).2 ?_
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hW0] at hu
    push_cast at hu ⊢
    linarith
  omega

theorem cellT_mono (s : ℝ) (W : ℕ) (a t : ℝ≥0) {j j' : ℕ} (hjj : j ≤ j') :
    cellT s W a t j ≤ cellT s W a t j' := by
  unfold cellT
  refine max_le_max le_rfl (min_le_min le_rfl (Real.toNNReal_le_toNNReal ?_))
  have : (j : ℝ) ≤ j' := by exact_mod_cast hjj
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  linarith [div_le_div_of_nonneg_right this hW]

/-- **A cell has length at most `1/W`.** -/
theorem cellT_succ_sub_le (s : ℝ) (W : ℕ) (a t : ℝ≥0) (j : ℕ) :
    (cellT s W a t (j + 1) : ℝ) - cellT s W a t j ≤ 1 / W := by
  rw [coe_cellT, coe_cellT]
  set x : ℝ := (j : ℝ) / W - s
  have hx : ((j + 1 : ℕ) : ℝ) / W - s = x + 1 / W := by simp only [x]; push_cast; ring
  rw [hx]
  have hW : (0 : ℝ) ≤ 1 / W := by positivity
  have e1 : max (x + 1 / W) 0 ≤ max x 0 + 1 / W := max_le (by linarith [le_max_left x 0])
    (by linarith [le_max_right x 0])
  have e2 : min (t : ℝ) (max (x + 1 / W) 0) ≤ min (t : ℝ) (max x 0) + 1 / W := by
    rcases le_total (t : ℝ) (max x 0) with h | h
    · rw [min_eq_left h]; linarith [min_le_left (t : ℝ) (max (x + 1 / W) 0)]
    · rw [min_eq_right h]; linarith [min_le_right (t : ℝ) (max (x + 1 / W) 0)]
  have e3 : max (a : ℝ) (min (t : ℝ) (max (x + 1 / W) 0)) ≤
      max (a : ℝ) (min (t : ℝ) (max x 0)) + 1 / W :=
    max_le (by linarith [le_max_left (a : ℝ) (min (t : ℝ) (max x 0))])
      (by linarith [le_max_right (a : ℝ) (min (t : ℝ) (max x 0))])
  linarith

theorem cellT_succ_sub_eq (hs : 0 ≤ s) (hW : 1 ≤ W) {j : ℕ} (hpj : limLenAll s W a < j)
    (hjq : j + 1 ≤ limLenAll s W t) :
    (cellT s W a t (j + 1) : ℝ) - cellT s W a t j = 1 / W := by
  rw [cellT_eq_of_lt hs hW (hpj.trans (Nat.lt_succ_self j)) hjq,
    cellT_eq_of_lt hs hW hpj (by omega)]
  push_cast; ring

end Grid

/-!
## Limit jumps and discrete jumps
-/

/-- The births of `b3JumpAt` as a sum over the probes. -/
theorem b3JumpAt_eq_sum (b s : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) :
    b3JumpAt (K := K) b s τ m W n = ∑ i, if ⌊(W : ℝ) * τ i⌋₊ ∈ Finset.Ico (closeLen s W) n then
      ((((dStar b * m i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1,
        ((dStar b * m i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1) :
          GramState (SrcCol K (Fin np))) else 0 := by
  simp only [b3JumpAt, b3BirthAt]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_ite_eq _ _ _

/-- **Off a birth length, the limit jumps are the discrete jumps at that length.** -/
theorem gramJ_eq_b3JumpAt {b s : ℝ} {τ m : Fin np → ℝ} (hτ : ∀ i, s < τ i)
    {W : ℕ} (hW : 1 ≤ W) {u : ℝ≥0} (hnb : ¬ IsBirthStep τ W (limLenAll s W u)) :
    gramJ (K := K) b s τ m u = b3JumpAt b s τ m W (limLenAll s W u) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [gramJ_eq_sel, b3JumpAt_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : closeLen s W ≤ ⌊(W : ℝ) * τ i⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (hτ i).le hW0.le)
  have hne : ⌊(W : ℝ) * τ i⌋₊ ≠ limLenAll s W u := fun h => hnb ⟨i, h⟩
  have hiff : (τ i - s ≤ (u : ℝ)) ↔ ⌊(W : ℝ) * τ i⌋₊ ∈ Finset.Ico (closeLen s W)
      (limLenAll s W u) := by
    rw [Finset.mem_Ico]
    constructor
    · intro h
      refine ⟨hc, lt_of_le_of_ne (Nat.floor_mono (mul_le_mul_of_nonneg_left (by linarith)
        hW0.le)) hne⟩
    · rintro ⟨-, h⟩
      by_contra h'
      have : (W : ℝ) * (s + u) ≤ W * τ i :=
        mul_le_mul_of_nonneg_left (by linarith) hW0.le
      exact absurd (Nat.floor_mono this) (not_le.2 h)
  by_cases h : τ i - s ≤ (u : ℝ)
  · have h' := hiff.1 h
    simp only [h, h', decide_true, ↓reduceIte]
  · have h' : ⌊(W : ℝ) * τ i⌋₊ ∉ Finset.Ico (closeLen s W) (limLenAll s W u) :=
      fun h' => h (hiff.2 h')
    simp only [h, h', decide_false, Bool.false_eq_true, ↓reduceIte]

theorem b3JumpAt_succ (b s : ℝ) (τ m : Fin np → ℝ) {W n : ℕ} (hn : closeLen s W ≤ n) :
    b3JumpAt (K := K) b s τ m W (n + 1) = b3JumpAt b s τ m W n + b3BirthAt b τ m W n := by
  simp only [b3JumpAt]
  rw [Finset.sum_Ico_succ_top hn]

theorem b3BirthAt_eq_zero (b : ℝ) {τ m : Fin np → ℝ} {W n : ℕ} (hn : ¬ IsBirthStep τ W n) :
    b3BirthAt (K := K) b τ m W n = 0 := by
  unfold b3BirthAt
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h
  · exact absurd ⟨i, h⟩ hn
  · rfl

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
