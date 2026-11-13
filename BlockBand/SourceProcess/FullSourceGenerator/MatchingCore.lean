module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# Matching with the contraction rule: matrix words and the rotations of `pairTerm`/`crossTerm`

A trace word is evaluated at arbitrary letter matrices `A` and separator matrices `B`
(`segProd A B w = A₁B₁⋯A_rB_r`, `wval = Tr segProd`); along the path `wordValue` is `wval` at
`letterMatrix`, `separatorMatrix` (`wordValue_eq_wval`, by definition). A word with two marked
letters is written in the *shape* `L ++ x :: (Mid ++ y :: R)` (marked positions `|L|` and
`|L| + 1 + |Mid|`); every pair `i < j < |w|` has this shape (`exists_pair_shape`), and every
position has the shape `L ++ x :: R` (`exists_single_shape`). On shapes the rotations and
truncations used by `pairTerm` and `crossTerm` are explicit (`single_rotate`, `pair_S₁`,
`pair_S₂`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {nT nI : ℕ}

/-- The matrix `A₁B₁⋯A_rB_r` of a word at letters `A` and separators `B`. -/
def segProd (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (w : TraceWord nT nI) : Matrix ι ι ℂ :=
  (w.map fun x => A x.1 * B x.2).prod

/-- The value `Tr(A₁B₁⋯A_rB_r)` of a word. -/
def wval (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (w : TraceWord nT nI) : ℂ :=
  (segProd A B w).trace

theorem wordValue_eq_wval {W : ℕ} (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (ω : BlockBand.Internal.Contracts.TransmissionPath.GrowthPath W) (w : TraceWord nT nI) :
    wordValue b E k q W j ω w =
      wval (letterMatrix b E k q W j ω) (separatorMatrix b E W j ω) w := rfl

section Seg

variable (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)

@[simp] theorem segProd_nil : segProd A B ([] : TraceWord nT nI) = 1 := rfl

@[simp] theorem segProd_cons (x : TraceLetter nT nI × Separator) (w : TraceWord nT nI) :
    segProd A B (x :: w) = A x.1 * B x.2 * segProd A B w := by
  simp [segProd]

@[simp] theorem segProd_append (u v : TraceWord nT nI) :
    segProd A B (u ++ v) = segProd A B u * segProd A B v := by
  simp [segProd]

theorem segProd_singleton (x : TraceLetter nT nI × Separator) :
    segProd A B [x] = A x.1 * B x.2 := by
  simp

end Seg

/-!
### Ordinary separators
-/

/-- `B` is an ordinary separator table: `B I = 1` and `P = B P` is idempotent. -/
structure OrdTable (B : Separator → Matrix ι ι ℂ) : Prop where
  id_eq : B .id = 1
  proj_idem : B .proj * B .proj = B .proj

theorem OrdTable.mul_proj {B : Separator → Matrix ι ι ℂ} (hB : OrdTable B) {s : Separator}
    (hs : s = .id ∨ s = .proj) : B s * B .proj = B .proj := by
  rcases hs with rfl | rfl
  · rw [hB.id_eq, Matrix.one_mul]
  · exact hB.proj_idem

theorem OrdTable.proj_mul {B : Separator → Matrix ι ι ℂ} (hB : OrdTable B) {s : Separator}
    (hs : s = .id ∨ s = .proj) : B .proj * B s = B .proj := by
  rcases hs with rfl | rfl
  · rw [hB.id_eq, Matrix.mul_one]
  · exact hB.proj_idem

/-- `Tr(B_s U P) = Tr(U P)` for an ordinary separator `s`. -/
theorem OrdTable.trace_sep_mul_proj {B : Separator → Matrix ι ι ℂ} (hB : OrdTable B)
    {s : Separator} (hs : s = .id ∨ s = .proj) (U : Matrix ι ι ℂ) :
    (B s * U * B .proj).trace = (U * B .proj).trace := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hB.proj_mul hs]

/-!
### `setLastSep`
-/

theorem setLastSep_concat (u : TraceWord nT nI) (x : TraceLetter nT nI × Separator)
    (s : Separator) : setLastSep (u ++ [x]) s = u ++ [(x.1, s)] := by
  simp [setLastSep]

/-- Replacing an ordinary last separator by `P` multiplies by `P`. -/
theorem segProd_setLastSep_proj (A : TraceLetter nT nI → Matrix ι ι ℂ)
    {B : Separator → Matrix ι ι ℂ} (hB : OrdTable B) (u : TraceWord nT nI)
    (x : TraceLetter nT nI × Separator) (hx : x.2 = .id ∨ x.2 = .proj) :
    segProd A B (setLastSep (u ++ [x]) .proj) = segProd A B (u ++ [x]) * B .proj := by
  rw [setLastSep_concat]
  simp only [segProd_append, segProd_singleton, Matrix.mul_assoc, hB.mul_proj hx]

/-!
### Shapes
-/

theorem exists_single_shape (w : TraceWord nT nI) {i : ℕ} (hi : i < w.length) :
    ∃ (L R : TraceWord nT nI) (x : TraceLetter nT nI × Separator),
      w = L ++ x :: R ∧ L.length = i ∧ x ∈ w := by
  refine ⟨w.take i, w.drop (i + 1), w[i], ?_, by simp; omega, List.getElem_mem hi⟩
  conv_lhs => rw [← List.take_append_drop i w]
  rw [List.drop_eq_getElem_cons hi]

theorem exists_pair_shape (w : TraceWord nT nI) {i j : ℕ} (hij : i < j) (hj : j < w.length) :
    ∃ (L Mid R : TraceWord nT nI) (x y : TraceLetter nT nI × Separator),
      w = L ++ x :: (Mid ++ y :: R) ∧ L.length = i ∧ L.length + 1 + Mid.length = j ∧
        x ∈ w ∧ y ∈ w := by
  obtain ⟨L, R₀, x, hw, hL, hx⟩ := exists_single_shape w (hij.trans hj)
  have hR₀ : j - i - 1 < R₀.length := by
    have := congrArg List.length hw; simp at this; omega
  obtain ⟨Mid, R, y, hR, hM, hy⟩ := exists_single_shape R₀ hR₀
  refine ⟨L, Mid, R, x, y, by rw [hw, hR], hL, by omega, hx, ?_⟩
  rw [hw]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)

section ShapeLemmas

variable (L Mid R : TraceWord nT nI) (x y : TraceLetter nT nI × Separator)

theorem sepAt_shape_left : sepAt (L ++ x :: R) L.length = x.2 := by
  simp [sepAt]

theorem sepAt_pair_right :
    sepAt (L ++ x :: (Mid ++ y :: R)) (L.length + 1 + Mid.length) = y.2 := by
  simp only [sepAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp only [show L.length + 1 + Mid.length - L.length = Mid.length + 1 by omega,
    List.getElem?_cons_succ]
  rw [List.getElem?_append_right le_rfl]
  simp

theorem length_pair_shape :
    (L ++ x :: (Mid ++ y :: R)).length = L.length + 1 + Mid.length + 1 + R.length := by
  simp; omega

/-- `w.rotate (i+1) = Mid ++ y :: R ++ L ++ [x]` for the left marked position `i = |L|`. -/
theorem single_rotate (R : TraceWord nT nI) :
    (L ++ x :: R).rotate (L.length + 1) = R ++ (L ++ [x]) := by
  have h : L ++ x :: R = (L ++ [x]) ++ R := by simp
  rw [h, show L.length + 1 = (L ++ [x]).length by simp, List.rotate_append_length_eq]

/-- `S₁` of `pairTerm`: the letters `j+1, …, i` (cyclically). -/
theorem pair_S₁ :
    ((L ++ x :: (Mid ++ y :: R)).rotate (L.length + 1 + Mid.length + 1)).take
        ((L ++ x :: (Mid ++ y :: R)).length - (L.length + 1 + Mid.length - L.length)) =
      R ++ L ++ [x] := by
  have h : L ++ x :: (Mid ++ y :: R) = (L ++ x :: (Mid ++ [y])) ++ R := by simp
  have hl : L.length + 1 + Mid.length + 1 = (L ++ x :: (Mid ++ [y])).length := by simp; omega
  rw [h, hl, List.rotate_append_length_eq]
  have h2 : R ++ (L ++ x :: (Mid ++ [y])) = (R ++ L ++ [x]) ++ (Mid ++ [y]) := by simp
  rw [h2]
  apply List.take_left'
  simp; omega

/-- `S₂` of `pairTerm`: the letters `i+1, …, j`. -/
theorem pair_S₂ :
    ((L ++ x :: (Mid ++ y :: R)).rotate (L.length + 1)).take
        (L.length + 1 + Mid.length - L.length) = Mid ++ [y] := by
  rw [single_rotate]
  have h2 : Mid ++ y :: R ++ (L ++ [x]) = (Mid ++ [y]) ++ (R ++ (L ++ [x])) := by simp
  rw [h2]
  apply List.take_left'
  simp; omega

end ShapeLemmas

end BlockBand.SourceProcess.FullSourceGenerator
