module

public import BlockBand.Native.ErdosRiabov.QV.Local

/-!
# Quadratic variation: resolvent words

Encoding of resolvent chains as words, their concatenation and adjoints, and the identification
with the chains and size functions of `Psi`.

A chain `G_0 S^{c_1} G_1 S^{c_2} ⋯ S^{c_m} G_m` along the VS characteristic at time `t` is
encoded by its first pattern bit `β₀` and the list `r = [(c_1, β_1), …, (c_m, β_m)]` of
(observable site, next pattern bit): `qvW P t H β₀ r`, with `G_j = qvRes P t H β_j =
(H - z_{β_j,t})⁻¹`, `z_{false,t} = z_t`, `z_{true,t} = z̄_t`. Its isotropic internal sites are
`r.map Prod.fst`; the averaged chain closes with `S^c`.

* `qvW_append`: `W(β₀, r₁ ++ (c,β) :: r₂) = W(β₀, r₁) S^c W(β, r₂)` (concatenation; the doubled
  chains and the `K`-cut are instances);
* `qvW_conjTranspose`: for Hermitian `H`,
  `W(β₀, r)ᴴ = W(qvAdj β₀ r)`, the reversed chain with complemented bits; its sites are reversed
  (`qvAdj_sites`);
* bridges to `Psi.Defs`: with `qvSig β₀ r` and `qvSites r c`, `gChain … isoSlots = W(β₀, r)`
  (`gChain_iso_qvW`), `gChain … avSlots = W(β₀, r) S^c` (`gChain_av_qvW`),
  `sIso = √(qvIsoSq …)` (`sIso_qvSites`) and `sAv = √(qvAvSq P t c (r.map fst))`
  (`sAv_qvSites`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.QV

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open Matrix
open scoped ComplexConjugate

variable {N : ℕ}

/-- The resolvent of pattern bit `β` at VS time `t`: `(H - z_{β,t})⁻¹`. -/
def qvRes (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) (β : Bool) :
    Matrix (Fin N) (Fin N) ℂ :=
  (H - VS.patConj β (vsTraj P.z t) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- The tail `Π_i S^{c_i} G_{β_i}` of a word. -/
def qvTail (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) (r : List (Fin N × Bool)) :
    Matrix (Fin N) (Fin N) ℂ :=
  (r.map fun q => obsMat P.S q.1 * qvRes P t H q.2).prod

/-- The resolvent word `G_{β₀} S^{c_1} G_{β_1} ⋯ S^{c_m} G_{β_m}`. -/
def qvW (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) (β₀ : Bool)
    (r : List (Fin N × Bool)) : Matrix (Fin N) (Fin N) ℂ :=
  qvRes P t H β₀ * qvTail P t H r

section Words

variable (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ)

theorem qvW_nil (β : Bool) : qvW P t H β [] = qvRes P t H β := by
  simp [qvW, qvTail]

/-- **Concatenation** at an observable `S^c`. -/
theorem qvW_append (β₀ : Bool) (r₁ : List (Fin N × Bool)) (c : Fin N) (β : Bool)
    (r₂ : List (Fin N × Bool)) :
    qvW P t H β₀ (r₁ ++ (c, β) :: r₂) = qvW P t H β₀ r₁ * obsMat P.S c * qvW P t H β r₂ := by
  simp only [qvW, qvTail, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  simp only [Matrix.mul_assoc]

theorem qvW_snoc (β₀ : Bool) (r : List (Fin N × Bool)) (c : Fin N) (β : Bool) :
    qvW P t H β₀ (r ++ [(c, β)]) = qvW P t H β₀ r * obsMat P.S c * qvRes P t H β := by
  rw [qvW_append, qvW_nil]

theorem qvW_cons (β₀ : Bool) (c : Fin N) (β : Bool) (r : List (Fin N × Bool)) :
    qvW P t H β₀ ((c, β) :: r) = qvRes P t H β₀ * obsMat P.S c * qvW P t H β r := by
  have h := qvW_append P t H β₀ [] c β r
  rw [List.nil_append, qvW_nil] at h
  exact h

end Words

/-!
## Adjoints
-/

/-- The adjoint word: first bit and tail of `W(β₀, r)ᴴ`. -/
def qvAdj : Bool → List (Fin N × Bool) → Bool × List (Fin N × Bool)
  | β, [] => (!β, [])
  | β, (c, β') :: r => ((qvAdj β' r).1, (qvAdj β' r).2 ++ [(c, !β)])

theorem qvAdj_sites : ∀ (β : Bool) (r : List (Fin N × Bool)),
    (qvAdj β r).2.map Prod.fst = (r.map Prod.fst).reverse
  | _, [] => rfl
  | _, (c, β') :: r => by
    simp only [qvAdj, List.map_append, List.map_cons, List.map_nil, List.reverse_cons]
    rw [qvAdj_sites β' r]

theorem qvAdj_length (β : Bool) (r : List (Fin N × Bool)) :
    (qvAdj β r).2.length = r.length := by
  rw [← List.length_map Prod.fst, qvAdj_sites, List.length_reverse, List.length_map]

theorem qv_patConj_not (β : Bool) (w : ℂ) : VS.patConj (!β) w = conj (VS.patConj β w) := by
  cases β <;> simp [VS.patConj]

theorem qvRes_conjTranspose (P : PsiData N) (t : ℝ) {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) (β : Bool) : (qvRes P t H β)ᴴ = qvRes P t H (!β) := by
  unfold qvRes
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, hH.eq,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, qv_patConj_not]
  rfl

theorem obsMat_conjTranspose (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin N) :
    (obsMat S x)ᴴ = obsMat S x := by
  unfold obsMat
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp [Split.rowObs]

/-- **Q0.1: the adjoint word.** For Hermitian `H`, `W(β₀, r)ᴴ = W(qvAdj β₀ r)`. -/
theorem qvW_conjTranspose (P : PsiData N) (t : ℝ) {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) :
    ∀ (β₀ : Bool) (r : List (Fin N × Bool)),
      (qvW P t H β₀ r)ᴴ = qvW P t H (qvAdj β₀ r).1 (qvAdj β₀ r).2
  | β₀, [] => by
    rw [qvW_nil, qvRes_conjTranspose P t hH]
    simp [qvAdj, qvW_nil]
  | β₀, (c, β') :: r => by
    rw [qvW_cons, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      qvW_conjTranspose P t hH β' r, obsMat_conjTranspose, qvRes_conjTranspose P t hH]
    simp only [qvAdj]
    rw [qvW_snoc, Matrix.mul_assoc]

/-!
## Bridges to `Psi.Defs`
-/

/-- The pattern of the word `(β₀, r)`: `(β₀, β_1, …, β_m)`. -/
def qvSig (β₀ : Bool) (r : List (Fin N × Bool)) : Fin (r.length + 1) → Bool :=
  fun j => (β₀ :: r.map Prod.snd)[j.val]'(by
    simp only [List.length_cons, List.length_map]; exact j.isLt)

/-- The sites of the word `(β₀, r)` closed by `c`: `(c_1, …, c_m, c)`. -/
def qvSites (r : List (Fin N × Bool)) (c : Fin N) : Fin (r.length + 1) → Fin N :=
  fun j => (r.map Prod.fst ++ [c])[j.val]'(by
    simp only [List.length_append, List.length_map, List.length_singleton]; exact j.isLt)

section Bridges

variable (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ)

theorem qv_gChain_eq_prod {k : ℕ} (w : Fin k → ℂ) (B : Fin k → Matrix (Fin N) (Fin N) ℂ) :
    gChain w B H = (List.ofFn fun j => (H - w j • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ * B j).prod :=
  rfl

/-- **Bridge (iso).** `G_{[1,k]}` of `Psi.Defs` with the pattern `qvSig β₀ r` and the sites
`qvSites r c` (the last site `c` is unused) is the word `W(β₀, r)`.
-/
theorem gChain_iso_qvW : ∀ (β₀ : Bool) (r : List (Fin N × Bool)) (c : Fin N),
    gChain (patZ P.z (qvSig β₀ r) t) (isoSlots P.S (qvSites r c)) H = qvW P t H β₀ r
  | β₀, [], c => by
    rw [qv_gChain_eq_prod, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Matrix.mul_one, qvW_nil]
    simp [isoSlots, patZ, qvSig, qvRes]
  | β₀, (c₁, β₁) :: r, c => by
    have ih := gChain_iso_qvW β₁ r c
    rw [qv_gChain_eq_prod] at ih ⊢
    rw [List.ofFn_succ, List.prod_cons, qvW_cons, ← ih]
    congr 1
    simp [isoSlots, patZ, qvSig, qvSites]

/-- **Bridge (av).** `G_{[1,k]} S^{x_k}` of `Psi.Defs` with `qvSig β₀ r`, `qvSites r c` is
`W(β₀, r) S^c`.
-/
theorem gChain_av_qvW : ∀ (β₀ : Bool) (r : List (Fin N × Bool)) (c : Fin N),
    gChain (patZ P.z (qvSig β₀ r) t) (avSlots P.S (qvSites r c)) H =
      qvW P t H β₀ r * obsMat P.S c
  | β₀, [], c => by
    rw [qv_gChain_eq_prod, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Matrix.mul_one, qvW_nil]
    simp [avSlots, patZ, qvSig, qvSites, qvRes]
  | β₀, (c₁, β₁) :: r, c => by
    have ih := gChain_av_qvW β₁ r c
    rw [qv_gChain_eq_prod] at ih ⊢
    rw [List.ofFn_succ, List.prod_cons, qvW_cons, Matrix.mul_assoc _ (qvW P t H β₁ r), ← ih]
    congr 1

end Bridges

theorem qvSites_castSucc (r : List (Fin N × Bool)) (c : Fin N) :
    (List.ofFn fun i : Fin r.length => qvSites r c i.castSucc) = r.map Prod.fst := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp [qvSites, List.getElem_append_left]

/-- **Bridge (iso size).** `s^iso(a, qvSites r c, b) = √(qvIsoSq P t a (r.map fst) b)`. -/
theorem sIso_qvSites (P : PsiData N) {t : ℝ} (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    (a b : Fin N) (r : List (Fin N × Bool)) (c : Fin N) :
    P.sIso a b (qvSites r c) t = Real.sqrt (qvIsoSq P t a (r.map Prod.fst) b) := by
  rw [sIso_eq_sqrt P hU hL, qvSites_castSucc]

/-- **Bridge (av size).** `s^av(qvSites r c) = √(qvAvSq P t c (r.map fst))` (cyclic order
`c, c_1, …, c_m`).
-/
theorem sAv_qvSites (P : PsiData N) {t : ℝ} (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    (r : List (Fin N × Bool)) (c : Fin N) :
    P.sAv (qvSites r c) t = Real.sqrt (qvAvSq P t c (r.map Prod.fst)) := by
  rw [sAv_eq_sqrt P hU hL]
  cases r with
  | nil => simp [qvSites]
  | cons q r =>
    have h0 : qvSites (q :: r) c 0 = q.1 := by simp [qvSites]
    have hs : (List.ofFn fun i : Fin (q :: r).length => qvSites (q :: r) c i.succ) =
        r.map Prod.fst ++ [c] := by
      refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
      rw [List.getElem_ofFn]
      simp [qvSites]
    rw [h0, hs, List.map_cons, qvAvSq_rotate]

end BlockBand.Native.ErdosRiabov.QV
