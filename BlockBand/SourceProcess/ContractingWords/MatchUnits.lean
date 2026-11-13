module

public import BlockBand.SourceProcess.ContractingWords.MatchSand

/-!
# The contracted pair and cross functionals as trace forms

For a trace word `w`, letters `A` and a separator table `B`, slot `p` carrying `σ_p = B_{s_p}`:
* `pairF_word`: `pairF(p, q, σ_pGσ_q, σ_qHσ_p) = Tr(M_{pq}G)·Tr(N_{pq}H)` for `p < q`, with
  `pairM`, `pairN` (the two cycles of the pair);
* `crossF_word`: `crossF(p, q, σ_pGσ'_q, σ'_qHσ_p) = Tr(M_p G M'_q H)` with `singleM`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.FullSourceGenerator

variable {ι : Type} [Fintype ι] [DecidableEq ι] {nT nI : ℕ}

theorem get_shape (L R : TraceWord nT nI) (x : TraceLetter nT nI × Separator)
    (h : L.length < (L ++ x :: R).length) : (L ++ x :: R).get ⟨L.length, h⟩ = x := by
  simp

theorem get_pair_shape (L Mid R : TraceWord nT nI) (x y : TraceLetter nT nI × Separator)
    (h : L.length + 1 + Mid.length < (L ++ x :: (Mid ++ y :: R)).length) :
    (L ++ x :: (Mid ++ y :: R)).get ⟨L.length + 1 + Mid.length, h⟩ = y := by
  have e : L ++ x :: (Mid ++ y :: R) = (L ++ x :: Mid) ++ y :: R := by simp
  have hl : (L ++ x :: Mid).length = L.length + 1 + Mid.length := by simp; omega
  simp only [List.get_eq_getElem]
  rw [List.getElem_of_eq e, List.getElem_append_right (by omega)]
  simp [hl]

theorem pairM_shape (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (L Mid R : TraceWord nT nI) (x y : TraceLetter nT nI × Separator) :
    pairM A B (L ++ x :: (Mid ++ y :: R)) L.length (L.length + 1 + Mid.length) =
      B y.2 * segProd A B (R ++ L ++ [x]) := by
  rw [pairM, pair_S₁, sepAt_pair_right]

theorem pairN_shape (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (L Mid R : TraceWord nT nI) (x y : TraceLetter nT nI × Separator) :
    pairN A B (L ++ x :: (Mid ++ y :: R)) L.length (L.length + 1 + Mid.length) =
      B x.2 * segProd A B (Mid ++ [y]) := by
  rw [pairN, pair_S₂, sepAt_shape_left]

theorem singleM_shape (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (L R : TraceWord nT nI) (x : TraceLetter nT nI × Separator) :
    singleM A B (L ++ x :: R) L.length = B x.2 * segProd A B (R ++ (L ++ [x])) := by
  rw [singleM, single_rotate, sepAt_shape_left]

/-- **The pair functional.** -/
theorem pairF_word (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (w : TraceWord nT nI) {p q : Fin w.length} (hpq : p < q) (G H : Matrix ι ι ℂ) :
    pairF (wl A w) (fun i => B (w.get i).2) p q (B (w.get p).2 * G * B (w.get q).2)
        (B (w.get q).2 * H * B (w.get p).2) =
      (pairM A B w p q * G).trace * (pairN A B w p q * H).trace := by
  obtain ⟨pv, hpv⟩ := p
  obtain ⟨qv, hqv⟩ := q
  have hpq' : pv < qv := hpq
  obtain ⟨L, Mid, R, x, y, hw, hL, hM, -, -⟩ := exists_pair_shape w hpq' hqv
  subst hw hL hM
  rw [get_shape, get_pair_shape]
  have key : ∀ a b c d, posTr (wl A (L ++ x :: (Mid ++ y :: R)))
      (pw (fun i => B ((L ++ x :: (Mid ++ y :: R)).get i).2)
        (units2 ⟨L.length, hpv⟩ ⟨L.length + 1 + Mid.length, hqv⟩ a b c d)
        {⟨L.length, hpv⟩, ⟨L.length + 1 + Mid.length, hqv⟩}) =
      (segProd A B R * segProd A B L * A x.1 * unitM a b * (segProd A B Mid * A y.1) *
        unitM c d).trace := fun a b c d => by
    have e : pw (fun i => B ((L ++ x :: (Mid ++ y :: R)).get i).2)
        (units2 ⟨L.length, hpv⟩ ⟨L.length + 1 + Mid.length, hqv⟩ a b c d)
        {⟨L.length, hpv⟩, ⟨L.length + 1 + Mid.length, hqv⟩} = fun i : Fin (L ++ x :: (Mid ++ y :: R)).length =>
        slot2 B L.length (L.length + 1 + Mid.length) (unitM a b) (unitM c d) i
          ((L ++ x :: (Mid ++ y :: R)).get i).2 := by
      funext i
      simp only [pw, units2, slot2, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      split_ifs <;> simp_all [Function.update, Fin.ext_iff]
      omega
    rw [e, posTr_word_pair, Matrix.trace_mul_comm _ (segProd A B R)]
    simp only [Matrix.mul_assoc]
  simp only [pairF, key, trace_pair_units, pairM_shape, pairN_shape]
  congr 1
  · simp only [segProd_append, segProd_singleton, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (B y.2)]
    simp only [Matrix.mul_assoc]
  · simp only [segProd_append, segProd_singleton, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (B x.2)]
    simp only [Matrix.mul_assoc]

theorem posTr_units1 (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (L R : TraceWord nT nI) (x : TraceLetter nT nI × Separator)
    (h : L.length < (L ++ x :: R).length) (a b : ι) :
    posTr (wl A (L ++ x :: R)) (pw (fun i => B ((L ++ x :: R).get i).2)
        (units1 ⟨L.length, h⟩ a b) {⟨L.length, h⟩}) =
      (segProd A B R * segProd A B L * A x.1 * unitM a b).trace := by
  have e : pw (fun i => B ((L ++ x :: R).get i).2) (units1 ⟨L.length, h⟩ a b) {⟨L.length, h⟩} =
      fun i : Fin (L ++ x :: R).length => slot1 B L.length (unitM a b) i ((L ++ x :: R).get i).2 := by
    funext i
    simp only [pw, units1, slot1, Finset.mem_singleton, Fin.ext_iff]
    split_ifs <;> simp_all [Function.update, Fin.ext_iff]
  rw [e, posTr_word_single, Matrix.trace_mul_comm _ (segProd A B R)]
  simp only [Matrix.mul_assoc]

/-- **The cross functional.** -/
theorem crossF_word (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (w v : TraceWord nT nI) (p : Fin w.length) (q : Fin v.length) (G H : Matrix ι ι ℂ) :
    crossF (wl A w) (fun i => B (w.get i).2) (wl A v) (fun i => B (v.get i).2) p q
        (B (w.get p).2 * G * B (v.get q).2) (B (v.get q).2 * H * B (w.get p).2) =
      (singleM A B w p * G * singleM A B v q * H).trace := by
  obtain ⟨pv, hpv⟩ := p
  obtain ⟨qv, hqv⟩ := q
  obtain ⟨L, R, x, hw, hL, -⟩ := exists_single_shape w hpv
  obtain ⟨L', R', y, hv, hL', -⟩ := exists_single_shape v hqv
  subst hw hv hL hL'
  rw [get_shape, get_shape]
  simp only [crossF, posTr_units1]
  rw [trace_cross_units]
  simp only [singleM_shape, segProd_append, segProd_singleton, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (B x.2)]
  simp only [Matrix.mul_assoc]

end BlockBand.SourceProcess.ContractingWords
