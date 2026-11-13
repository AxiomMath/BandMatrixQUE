module

public import BlockBand.SourceProcess.FullSourceGenerator.Matching

/-!
# `pairTerm`, `crossTerm`, `wordDrift`, `wordCov` evaluated: the contracted expansion

The second-order terms of the generator, evaluated on ordinary words, are the contractions of the
expansion at marked separators against the rule tensor.

* `pairM w i j = B_j·segProd(S₁)`, `pairN w i j = B_i·segProd(S₂)` with the lists `S₁`, `S₂` of
  `pairTerm` (letters `j+1, …, i` and `i+1, …, j`); `singleM w i = B_i·segProd(w.rotate (i+1))`.
  By `pair_expansion`/`single_expansion` these are the matrices of the
  second-order term `Tr(M X N Y)` and of the first-order term `Tr(M X)` (on shapes).
* `pairTerm_eval`: `eval (pairTerm D₀ w i j) = pairContraction (D₀/2) P P' (pairM) (pairN)`.
* `crossTerm_eval`: `eval (crossTerm D₀ w v i j) = crossContraction (D₀/2) P P' (singleM w i)
  (singleM v j)`.
* `wordDrift_eval`, `wordCov_eval`: the two generator coefficients as sums of contractions, the
  drift with `-(D₀/2)·g·#{separators P}·Tr w`, `g = ½Tr J²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open Matrix MvPolynomial
open BlockBand.Internal.Contracts.TransmissionStatements

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {nT nI : ℕ}

section Defs

variable (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)

/-- `M_{ij} = B_j·(A_{j+1}B_{j+1}⋯A_iB_i)` (the list `S₁` of `pairTerm`). -/
def pairM (w : TraceWord nT nI) (i j : ℕ) : Matrix ι ι ℂ :=
  B (sepAt w j) * segProd A B ((w.rotate (j + 1)).take (w.length - (j - i)))

/-- `N_{ij} = B_i·(A_{i+1}B_{i+1}⋯A_jB_j)` (the list `S₂` of `pairTerm`). -/
def pairN (w : TraceWord nT nI) (i j : ℕ) : Matrix ι ι ℂ :=
  B (sepAt w i) * segProd A B ((w.rotate (i + 1)).take (j - i))

/-- `M_i = B_i·(A_{i+1}B_{i+1}⋯A_iB_i)` (the rotation `S_w` of `crossTerm`). -/
def singleM (w : TraceWord nT nI) (i : ℕ) : Matrix ι ι ℂ :=
  B (sepAt w i) * segProd A B (w.rotate (i + 1))

end Defs

theorem segProd_concat (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (u : TraceWord nT nI) (z : TraceLetter nT nI × Separator) :
    segProd A B (u ++ [z]) = segProd A B u * (A z.1 * B z.2) := by
  simp

theorem segProd_setLastSep_proj' (A : TraceLetter nT nI → Matrix ι ι ℂ)
    {B : Separator → Matrix ι ι ℂ} (hB : OrdTable B) {S u : TraceWord nT nI}
    {x : TraceLetter nT nI × Separator} (hS : u ++ [x] = S) (hx : x.2 = .id ∨ x.2 = .proj) :
    segProd A B (setLastSep S .proj) = segProd A B S * B .proj := by
  subst hS; exact segProd_setLastSep_proj A hB u x hx

omit [DecidableEq ι] in
/-- `Tr(B_s U J) = Tr(U J B_s)`. -/
theorem trace_sep_mul_cur (Bs U J : Matrix ι ι ℂ) :
    (Bs * U * J).trace = (U * (J * Bs)).trace := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

section Shape

variable (A : TraceLetter nT nI → Matrix ι ι ℂ) {B : Separator → Matrix ι ι ℂ} (hB : OrdTable B)
include hB

/-- **`pairTerm` on a shape**: the first line of the word covariance. -/
theorem pairTerm_eval_shape (D0 : ℝ) (L Mid R : TraceWord nT nI)
    (x y : TraceLetter nT nI × Separator) (hx : x.2 = .id ∨ x.2 = .proj)
    (hy : y.2 = .id ∨ y.2 = .proj) :
    eval (wval A B) (pairTerm D0 (L ++ x :: (Mid ++ y :: R)) L.length
        (L.length + 1 + Mid.length)) =
      pairContraction ((D0 / 2 : ℝ) : ℂ) (B .proj) (B .proj + A .current)
        (B y.2 * segProd A B ((R ++ L) ++ [x])) (B x.2 * segProd A B (Mid ++ [y])) := by
  have h1 := pair_S₁ L Mid R x y
  have h2 := pair_S₂ L Mid R x y
  simp only [pairTerm, h1, h2, sepAt_shape_left, sepAt_pair_right]
  generalize hU : (R ++ L) ++ [x] = S₁
  generalize hV : Mid ++ [y] = S₂
  simp only [map_mul, map_add, eval_C, eval_X, wv, wval, segProd_concat,
    segProd_setLastSep_proj' A hB hU hx, segProd_setLastSep_proj' A hB hV hy]
  generalize segProd A B S₁ = U₁
  generalize segProd A B S₂ = U₂
  simp only [pairContraction, Matrix.mul_add, Matrix.trace_add, hB.trace_sep_mul_proj hx,
    hB.trace_sep_mul_proj hy, trace_sep_mul_cur]

/-- **`crossTerm` on shapes**: the second line of the word covariance. -/
theorem crossTerm_eval_shape (D0 : ℝ) (L R L' R' : TraceWord nT nI)
    (x y : TraceLetter nT nI × Separator) (hx : x.2 = .id ∨ x.2 = .proj)
    (hy : y.2 = .id ∨ y.2 = .proj) :
    eval (wval A B) (crossTerm D0 (L ++ x :: R) (L' ++ y :: R') L.length L'.length) =
      crossContraction ((D0 / 2 : ℝ) : ℂ) (B .proj) (B .proj + A .current)
        (B x.2 * segProd A B ((R ++ L) ++ [x])) (B y.2 * segProd A B ((R' ++ L') ++ [y])) := by
  have h1 : (L ++ x :: R).rotate (L.length + 1) = (R ++ L) ++ [x] := by
    rw [single_rotate]; simp
  have h2 : (L' ++ y :: R').rotate (L'.length + 1) = (R' ++ L') ++ [y] := by
    rw [single_rotate]; simp
  simp only [crossTerm, h1, h2, sepAt_shape_left]
  generalize hU : (R ++ L) ++ [x] = S₁
  generalize hV : (R' ++ L') ++ [y] = S₂
  simp only [map_mul, map_add, eval_C, eval_X, wv, wval, segProd_append, segProd_singleton,
    segProd_setLastSep_proj' A hB hU hx, segProd_setLastSep_proj' A hB hV hy]
  generalize segProd A B S₁ = U₁
  generalize segProd A B S₂ = U₂
  have hPx := hB.proj_mul hx
  have hPy := hB.proj_mul hy
  have ea : (B x.2 * U₁ * B .proj * (B y.2 * U₂) * B .proj).trace =
      (U₁ * B .proj * (U₂ * B .proj)).trace := by
    rw [show B x.2 * U₁ * B .proj * (B y.2 * U₂) * B .proj =
      B x.2 * (U₁ * (B .proj * B y.2) * U₂ * B .proj) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, hPy]
    simp only [Matrix.mul_assoc, hPx]
  have eb : (B x.2 * U₁ * B .proj * (B y.2 * U₂) * A .current).trace =
      (U₁ * B .proj * (U₂ * (A .current * B x.2))).trace := by
    rw [show B x.2 * U₁ * B .proj * (B y.2 * U₂) * A .current =
      B x.2 * (U₁ * (B .proj * B y.2) * U₂ * A .current) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, hPy]
    simp only [Matrix.mul_assoc]
  have ec : (B x.2 * U₁ * A .current * (B y.2 * U₂) * B .proj).trace =
      (U₁ * (A .current * B y.2 * (U₂ * B .proj))).trace := by
    rw [show B x.2 * U₁ * A .current * (B y.2 * U₂) * B .proj =
      B x.2 * (U₁ * A .current * B y.2 * U₂ * B .proj) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, hPx]
  simp only [crossContraction, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, ea, eb, ec]
  simp only [Matrix.mul_assoc]

end Shape

/-!
### General positions
-/

section General

variable (A : TraceLetter nT nI → Matrix ι ι ℂ) {B : Separator → Matrix ι ι ℂ} (hB : OrdTable B)
include hB

/-- **`pairTerm` at positions `i < j` of an ordinary word**:
`eval (pairTerm D₀ w i j) = (D₀/2)[Tr(M_{ij}P)Tr(N_{ij}P') + Tr(M_{ij}P')Tr(N_{ij}P)]`. -/
theorem pairTerm_eval (D0 : ℝ) {w : TraceWord nT nI} (hw : IsOrdinaryWord w) {i j : ℕ}
    (hij : i < j) (hj : j < w.length) :
    eval (wval A B) (pairTerm D0 w i j) =
      pairContraction ((D0 / 2 : ℝ) : ℂ) (B .proj) (B .proj + A .current)
        (pairM A B w i j) (pairN A B w i j) := by
  obtain ⟨L, Mid, R, x, y, rfl, rfl, rfl, hx, hy⟩ := exists_pair_shape w hij hj
  rw [pairTerm_eval_shape A hB D0 L Mid R x y (hw.2 x hx) (hw.2 y hy), pairM, pairN,
    pair_S₁, pair_S₂, sepAt_shape_left, sepAt_pair_right]

/-- **`crossTerm` at positions `i < |w|`, `j < |v|` of ordinary words**:
`eval (crossTerm D₀ w v i j) = (D₀/2)[Tr(M_iPN_jP') + Tr(M_iP'N_jP)]`. -/
theorem crossTerm_eval (D0 : ℝ) {w v : TraceWord nT nI} (hw : IsOrdinaryWord w)
    (hv : IsOrdinaryWord v) {i j : ℕ} (hi : i < w.length) (hj : j < v.length) :
    eval (wval A B) (crossTerm D0 w v i j) =
      crossContraction ((D0 / 2 : ℝ) : ℂ) (B .proj) (B .proj + A .current)
        (singleM A B w i) (singleM A B v j) := by
  obtain ⟨L, R, x, rfl, rfl, hx⟩ := exists_single_shape w hi
  obtain ⟨L', R', y, rfl, rfl, hy⟩ := exists_single_shape v hj
  rw [crossTerm_eval_shape A hB D0 L R L' R' x y (hw.2 x hx) (hv.2 y hy), singleM, singleM,
    single_rotate, single_rotate, sepAt_shape_left, sepAt_shape_left]
  simp only [List.append_assoc]

/-- **The bracket coefficient** `eval (wordCov D₀ w v)`: the sum over all separator pairs of the
second line of the word covariance. -/
theorem wordCov_eval (D0 : ℝ) {w v : TraceWord nT nI} (hw : IsOrdinaryWord w)
    (hv : IsOrdinaryWord v) :
    eval (wval A B) (wordCov D0 w v) =
      ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range v.length,
        crossContraction ((D0 / 2 : ℝ) : ℂ) (B .proj) (B .proj + A .current)
          (singleM A B w i) (singleM A B v j) := by
  rw [wordCov, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun j hj => crossTerm_eval A hB D0 hw hv
    (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)

/-- **The drift coefficient** `eval (wordDrift D₀ w)`: `-(D₀/2)·g·#{P}·Tr w` with
`g = ½Tr J²`, plus the sum over separator pairs of the first line of the word covariance. -/
theorem wordDrift_eval (D0 : ℝ) {w : TraceWord nT nI} (hw : IsOrdinaryWord w) :
    eval (wval A B) (wordDrift D0 w) =
      -(((D0 / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (A .current * A .current).trace) *
          ((w.countP fun x => decide (x.2 = Separator.proj) : ℕ) : ℂ) * wval A B w) +
        ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          pairContraction ((D0 / 2 : ℝ) : ℂ) (B .proj) (B .proj + A .current)
            (pairM A B w i j) (pairN A B w i j) := by
  rw [wordDrift, map_add, map_neg, map_sum]
  congr 1
  · simp only [gPoly, wv, map_mul, eval_C, eval_X, wval, segProd, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Matrix.mul_one, hB.id_eq]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hij, hj⟩ := Finset.mem_Ioo.mp hj
    exact pairTerm_eval A hB D0 hw hij hj

end General

end BlockBand.SourceProcess.FullSourceGenerator
