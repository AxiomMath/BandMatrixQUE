module

public import BlockBand.Native.ErdosRiabov.QV.Iso

/-!
# Quadratic variation: first-variation entries of chains as words

The bracket of the chain martingales is written with the slot calculus of resolvent chains
(`firstVar B M X = Σ_j slotProd B (update M j (M_j X M_j))`). For a pattern `σ` and sites `x`
of length `n + 1`, with resolvent slots `M_j = G_{σ_j}` (`qvRes`) and the word
`(σ 0, qvPairs σ x)` (`qvPairs σ x = [(x_0, σ_1), …, (x_{n-1}, σ_n)]`):
* iso slots (`isoSlots`, `K = E_{ba}`): the `j`-th first-variation term at `X = E_{cd}` has the
  `(a,b)` entry `(G_{[1,j]})_{ac} (G_{[j,k]})_{db}` with `G_{[1,j]} = W(σ 0, r.take j)` and
  `G_{[j,k]} = W(σ j, r.drop j)` (`qv_iso_term`);
* av slots (`avSlots`, `K = 1`): the `j`-th term has trace `(C_j)_{ba}`,
  `C_j = W(σ j, r.drop j ++ (x_n, σ 0) :: r.take j)` (`qv_av_term`), the rotated chain;
* sizes: `s^iso(a, x, b) = √qvIsoSq(a, r.map fst, b)`, `s^av(x) = √qvAvSq(x_n, r.map fst)`, and
  the cyclic rotation `qvAvSq_rot` (`s^av(c :: u ++ e :: v) = s^av(e :: v ++ c :: u)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.QV

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Chains (slotList slotProd segProd firstVar)
open Matrix Function

variable {N : ℕ}

/-- The word list of a pattern and sites: `[(x_0, σ_1), …, (x_{n-1}, σ_n)]`. -/
def qvPairs {n : ℕ} (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N) : List (Fin N × Bool) :=
  List.ofFn fun i : Fin n => (x i.castSucc, σ i.succ)

theorem qvPairs_length {n : ℕ} (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N) :
    (qvPairs σ x).length = n := by simp [qvPairs]

theorem qvPairs_succ {n : ℕ} (σ : Fin (n + 2) → Bool) (x : Fin (n + 2) → Fin N) :
    qvPairs σ x = (x 0, σ 1) :: qvPairs (fun i => σ i.succ) (fun i => x i.succ) := by
  unfold qvPairs
  rw [List.ofFn_succ]
  congr 1

theorem qvPairs_sites {n : ℕ} (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N) :
    (qvPairs σ x).map Prod.fst = List.ofFn fun i : Fin n => x i.castSucc := by
  unfold qvPairs
  rw [List.map_ofFn]
  rfl

/-- The flag at position `j` of the word `(σ 0, qvPairs σ x)` is `σ j`. -/
theorem qvPairs_flag {n : ℕ} (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N) (j : Fin (n + 1)) :
    (σ 0 :: (qvPairs σ x).map Prod.snd)[j.val]'(by simp [qvPairs_length]; omega) = σ j := by
  rcases j with ⟨_ | j, hj⟩
  · rfl
  · simp [qvPairs, List.getElem_ofFn]

/-!
## Slot lists of words
-/

/-- Slot list of an isotropic word: `[G_{β₀} S^{c_1}, …, G_{β_{m-1}} S^{c_m}, G_{β_m} 1]`. -/
def qvIsoList (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    Bool → List (Fin N × Bool) → List (Matrix (Fin N) (Fin N) ℂ)
  | β₀, [] => [qvRes P t H β₀ * 1]
  | β₀, (c, β) :: r => (qvRes P t H β₀ * obsMat P.S c) :: qvIsoList P t H β r

/-- Slot list of an averaged word closed by `S^c`. -/
def qvAvList (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) (c : Fin N) :
    Bool → List (Fin N × Bool) → List (Matrix (Fin N) (Fin N) ℂ)
  | β₀, [] => [qvRes P t H β₀ * obsMat P.S c]
  | β₀, (c₁, β) :: r => (qvRes P t H β₀ * obsMat P.S c₁) :: qvAvList P t H c β r

section Lists

variable (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ)

theorem slotList_iso_eq : ∀ {n : ℕ} (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N),
    slotList (isoSlots P.S x) (fun j => qvRes P t H (σ j)) = qvIsoList P t H (σ 0) (qvPairs σ x)
  | 0, σ, x => by simp [slotList, isoSlots, qvPairs, qvIsoList]
  | n + 1, σ, x => by
    have ih := slotList_iso_eq (fun i => σ i.succ) (fun i => x i.succ)
    rw [qvPairs_succ, qvIsoList]
    unfold slotList at ih ⊢
    rw [List.ofFn_succ, ← Fin.succ_zero_eq_one, ← ih]
    congr 1
    simp [isoSlots]

theorem slotList_av_eq : ∀ {n : ℕ} (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N),
    slotList (avSlots P.S x) (fun j => qvRes P t H (σ j)) =
      qvAvList P t H (x (Fin.last n)) (σ 0) (qvPairs σ x)
  | 0, σ, x => by simp [slotList, avSlots, qvPairs, qvAvList]
  | n + 1, σ, x => by
    have ih := slotList_av_eq (fun i => σ i.succ) (fun i => x i.succ)
    rw [qvPairs_succ, qvAvList]
    unfold slotList at ih ⊢
    rw [List.ofFn_succ, ← Fin.succ_last, ← Fin.succ_zero_eq_one, ← ih]
    rfl

theorem qvIsoList_take : ∀ (β₀ : Bool) (r : List (Fin N × Bool)) (j : ℕ) (hj : j ≤ r.length),
    ((qvIsoList P t H β₀ r).take j).prod *
        qvRes P t H ((β₀ :: r.map Prod.snd)[j]'(by simp; omega)) = qvW P t H β₀ (r.take j)
  | β₀, r, 0, _ => by simp [qvW_nil]
  | β₀, (c, β) :: r, j + 1, hj => by
    have ih := qvIsoList_take β r j (by simp at hj; omega)
    simp only [qvIsoList, List.take_succ_cons, List.prod_cons, List.map_cons,
      List.getElem_cons_succ]
    rw [Matrix.mul_assoc, ih, qvW_cons]

theorem qvIsoList_prod : ∀ (β₀ : Bool) (r : List (Fin N × Bool)),
    (qvIsoList P t H β₀ r).prod = qvW P t H β₀ r
  | β₀, [] => by simp [qvIsoList, qvW_nil]
  | β₀, (c, β) :: r => by
    rw [qvIsoList, List.prod_cons, qvIsoList_prod β r, qvW_cons]

theorem qvIsoList_drop : ∀ (β₀ : Bool) (r : List (Fin N × Bool)) (j : ℕ) (hj : j ≤ r.length),
    ((qvIsoList P t H β₀ r).drop j).prod =
      qvW P t H ((β₀ :: r.map Prod.snd)[j]'(by simp; omega)) (r.drop j)
  | β₀, r, 0, _ => by simp [qvIsoList_prod]
  | β₀, (c, β) :: r, j + 1, hj => by
    have ih := qvIsoList_drop β r j (by simp at hj; omega)
    simp only [qvIsoList, List.drop_succ_cons, List.map_cons, List.getElem_cons_succ]
    exact ih

theorem qvAvList_take : ∀ (c : Fin N) (β₀ : Bool) (r : List (Fin N × Bool)) (j : ℕ)
    (hj : j ≤ r.length),
    ((qvAvList P t H c β₀ r).take j).prod *
        qvRes P t H ((β₀ :: r.map Prod.snd)[j]'(by simp; omega)) = qvW P t H β₀ (r.take j)
  | c, β₀, r, 0, _ => by simp [qvW_nil]
  | c, β₀, (c₁, β) :: r, j + 1, hj => by
    have ih := qvAvList_take c β r j (by simp at hj; omega)
    simp only [qvAvList, List.take_succ_cons, List.prod_cons, List.map_cons,
      List.getElem_cons_succ]
    rw [Matrix.mul_assoc, ih, qvW_cons]

theorem qvAvList_prod : ∀ (c : Fin N) (β₀ : Bool) (r : List (Fin N × Bool)),
    (qvAvList P t H c β₀ r).prod = qvW P t H β₀ r * obsMat P.S c
  | c, β₀, [] => by simp [qvAvList, qvW_nil]
  | c, β₀, (c₁, β) :: r => by
    rw [qvAvList, List.prod_cons, qvAvList_prod c β r, qvW_cons]
    simp only [Matrix.mul_assoc]

theorem qvAvList_drop : ∀ (c : Fin N) (β₀ : Bool) (r : List (Fin N × Bool)) (j : ℕ)
    (hj : j ≤ r.length),
    ((qvAvList P t H c β₀ r).drop j).prod =
      qvW P t H ((β₀ :: r.map Prod.snd)[j]'(by simp; omega)) (r.drop j) * obsMat P.S c
  | c, β₀, r, 0, _ => by simp [qvAvList_prod]
  | c, β₀, (c₁, β) :: r, j + 1, hj => by
    have ih := qvAvList_drop c β r j (by simp at hj; omega)
    simp only [qvAvList, List.drop_succ_cons, List.map_cons, List.getElem_cons_succ]
    exact ih

theorem qvIsoList_length (β₀ : Bool) (r : List (Fin N × Bool)) :
    (qvIsoList P t H β₀ r).length = r.length + 1 := by
  induction r generalizing β₀ with
  | nil => rfl
  | cons q r ih => obtain ⟨c, β⟩ := q; simp [qvIsoList, ih]

theorem qvAvList_length (c : Fin N) (β₀ : Bool) (r : List (Fin N × Bool)) :
    (qvAvList P t H c β₀ r).length = r.length + 1 := by
  induction r generalizing β₀ with
  | nil => rfl
  | cons q r ih => obtain ⟨c₁, β⟩ := q; simp [qvAvList, ih]

end Lists

/-!
## The first-variation terms
-/

theorem qv_mul_single_mul_apply (A B : Matrix (Fin N) (Fin N) ℂ) (a b a' b' : Fin N) :
    (A * (Matrix.single a b (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) * B) a' b' = A a' a * B b b' := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul]

theorem qv_segProd_zero {k : ℕ} (B M : Fin k → Matrix (Fin N) (Fin N) ℂ) (j : ℕ) :
    segProd B M 0 j = ((slotList B M).take j).prod := by
  simp [segProd]

theorem qv_slotList_drop {k : ℕ} (B M : Fin k → Matrix (Fin N) (Fin N) ℂ) (j : Fin k) :
    M j * B j * segProd B M ((j : ℕ) + 1) k = ((slotList B M).drop j).prod := by
  have hk : (slotList B M).take k = slotList B M :=
    List.take_of_length_le (by simp [Chains.length_slotList])
  have hlt : (j : ℕ) < (slotList B M).length := by simp [Chains.length_slotList]
  rw [segProd, hk, List.drop_eq_getElem_cons hlt, List.prod_cons]
  simp [slotList]

/-- **Q0.2, isotropic term.** For `σ, x` of length `n + 1`, `j`, `a b c d`, with
`r = qvPairs σ x`: the `(a,b)` entry of the `j`-th first-variation term at `X = E_{cd}` is
`W(σ 0, r.take j)_{ac} · W(σ j, r.drop j)_{db}`.
-/
theorem qv_iso_term (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) {n : ℕ}
    (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N) (j : Fin (n + 1)) (a b c d : Fin N) :
    slotProd (isoSlots P.S x) (update (fun i => qvRes P t H (σ i)) j
        (qvRes P t H (σ j) * Matrix.single c d 1 * qvRes P t H (σ j))) a b =
      qvW P t H (σ 0) ((qvPairs σ x).take j) a c *
        qvW P t H (σ j) ((qvPairs σ x).drop j) d b := by
  have hj : (j : ℕ) ≤ (qvPairs σ x).length := by rw [qvPairs_length]; omega
  rw [Chains.slotProd_update]
  have e : segProd (isoSlots P.S x) (fun i => qvRes P t H (σ i)) 0 j *
      (qvRes P t H (σ j) * Matrix.single c d 1 * qvRes P t H (σ j) * isoSlots P.S x j) *
      segProd (isoSlots P.S x) (fun i => qvRes P t H (σ i)) ((j : ℕ) + 1) (n + 1) =
      (segProd (isoSlots P.S x) (fun i => qvRes P t H (σ i)) 0 j * qvRes P t H (σ j)) *
        Matrix.single c d 1 * (qvRes P t H (σ j) * isoSlots P.S x j *
          segProd (isoSlots P.S x) (fun i => qvRes P t H (σ i)) ((j : ℕ) + 1) (n + 1)) := by
    simp only [Matrix.mul_assoc]
  have hd := qv_slotList_drop (isoSlots P.S x) (fun i => qvRes P t H (σ i)) j
  rw [e, qv_mul_single_mul_apply, hd, qv_segProd_zero, slotList_iso_eq,
    qvIsoList_drop P t H _ _ _ hj, qvPairs_flag]
  have h1 := qvIsoList_take P t H (σ 0) (qvPairs σ x) j hj
  rw [qvPairs_flag] at h1
  rw [h1]

/-- **Q0.2, averaged term.** For `σ, x` of length `n + 1` and `j`, with `r = qvPairs σ x`:
the trace of the `j`-th first-variation term at `X = E_{ab}` is
`W(σ j, r.drop j ++ (x_n, σ 0):: r.take j)_{ba}`.
-/
theorem qv_av_term (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) {n : ℕ}
    (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N) (j : Fin (n + 1)) (a b : Fin N) :
    Matrix.trace (slotProd (avSlots P.S x) (update (fun i => qvRes P t H (σ i)) j
        (qvRes P t H (σ j) * Matrix.single a b 1 * qvRes P t H (σ j)))) =
      qvW P t H (σ j) ((qvPairs σ x).drop j ++ (x (Fin.last n), σ 0) :: (qvPairs σ x).take j)
        b a := by
  have hj : (j : ℕ) ≤ (qvPairs σ x).length := by rw [qvPairs_length]; omega
  rw [Chains.slotProd_update]
  have hd := qv_slotList_drop (avSlots P.S x) (fun i => qvRes P t H (σ i)) j
  have e : ∀ (A C R Bj : Matrix (Fin N) (Fin N) ℂ),
      Matrix.trace (A * (R * (Matrix.single a b (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) * R * Bj) * C)
        = ((R * Bj * C) * (A * R)) b a := by
    intro A C R Bj
    rw [show A * (R * (Matrix.single a b (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) * R * Bj) * C =
      (A * R) * ((Matrix.single a b (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) * (R * Bj * C)) by
        simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_single_mul, one_smul]
  rw [e, hd, qv_segProd_zero, slotList_av_eq, qvAvList_drop P t H _ _ _ _ hj, qvPairs_flag]
  have h1 := qvAvList_take P t H (x (Fin.last n)) (σ 0) (qvPairs σ x) j hj
  rw [qvPairs_flag] at h1
  rw [Matrix.mul_assoc (qvW P t H (σ j) _), h1, ← Matrix.mul_assoc, ← qvW_append]

/-!
## Sizes along `qvPairs`
-/

/-- **Cyclic rotation of `s^av`**: `s^av(c :: u ++ e :: v)² = s^av(e :: v ++ c :: u)²`. -/
theorem qvAvSq_rot (P : PsiData N) (t : ℝ) :
    ∀ (u : List (Fin N)) (c e : Fin N) (v : List (Fin N)),
      qvAvSq P t c (u ++ e :: v) = qvAvSq P t e (v ++ c :: u)
  | [], c, e, v => by rw [List.nil_append, qvAvSq_rotate]
  | u₀ :: u, c, e, v => by
    rw [List.cons_append, qvAvSq_rotate, List.append_assoc, List.cons_append,
      qvAvSq_rot P t u u₀ e (v ++ [c])]
    simp

theorem sIso_qvPairs (P : PsiData N) {t : ℝ} (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    {n : ℕ} (σ : Fin (n + 1) → Bool) (a b : Fin N) (x : Fin (n + 1) → Fin N) :
    P.sIso a b x t = Real.sqrt (qvIsoSq P t a ((qvPairs σ x).map Prod.fst) b) := by
  rw [sIso_eq_sqrt P hU hL, qvPairs_sites]

theorem sAv_qvPairs (P : PsiData N) {t : ℝ} (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    {n : ℕ} (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N) :
    P.sAv x t = Real.sqrt (qvAvSq P t (x (Fin.last n)) ((qvPairs σ x).map Prod.fst)) := by
  rw [sAv_eq_sqrt P hU hL, qvPairs_sites]
  rcases n with _ | n
  · rfl
  · congr 1
    have h1 : (List.ofFn fun i : Fin (n + 1) => x i.succ) =
        (List.ofFn fun i : Fin n => x i.castSucc.succ) ++ [x (Fin.last (n + 1))] := by
      rw [List.ofFn_succ', List.concat_eq_append, Fin.succ_last]
    have h2 : (List.ofFn fun i : Fin (n + 1) => x i.castSucc) =
        x 0 :: List.ofFn fun i : Fin n => x i.castSucc.succ := by
      rw [List.ofFn_succ]
      congr 1
    rw [h1, h2, qvAvSq_rotate]

end BlockBand.Native.ErdosRiabov.QV
