module

public import BlockBand.Native.ErdosRiabov.Contr.MoreSplit
public import BlockBand.Native.ErdosRiabov.Contr.Local

/-!
# Quadratic variation: size functions on site lists

The quadratic-variation estimates manipulate size functions of chains that are built by
concatenating,
reversing and rotating other chains. Here the size functions are written on **lists of sites**,
which makes those operations algebraic:
* `qvPath U l = Π_i U(l_i, l_{i+1})` (path product along the list `l`);
* `qvIsoSq P t a u b = L^{-|u|} qvPath Υ (a :: u ++ [b])`: the **square** of
  `s^iso(a, u, b)` (`u` = the internal sites, `L = ℓ_tη_t`, `Υ = Υ_t`);
* `qvAvSq P t c r = L^{-(|r|+1)} qvPath Υ (c :: r ++ [c])`: the square of `s^av(c :: r)`.
Bridges: `sIso_sq_eq` and `sAv_sq_eq` identify them with `Psi.PsiData.sIso` and `sAv`
(for `sAv_1 = 1/L` this uses the exact diagonal `Υ(a,a) = 1/L`).

Identities: (S1) reversal `qvIsoSq_reverse`, rotation `qvAvSq_rotate`;
(S2) `qvAvSq_eq`; the concatenation identity `qvIsoSq_split`
(`s(a,(u,c,v),b)² = L⁻¹ s(a,u,c)² s(c,v,b)²`), of which (S3) doubling and (S4) half-av are
instances; (S5) time comparison `qvIsoSq_time_le`, `qvAvSq_time_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.QV

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Internal.Contracts.Inputs (polynomialControl)

variable {N : ℕ}

/-!
## Path products along lists
-/

/-- The path product `Π_i U(l_i, l_{i+1})` along a list of sites. -/
def qvPath (U : Matrix (Fin N) (Fin N) ℝ) : List (Fin N) → ℝ
  | a :: b :: l => U a b * qvPath U (b :: l)
  | _ => 1

section PathLemmas

variable (U : Matrix (Fin N) (Fin N) ℝ)

theorem qvPath_nil : qvPath U [] = 1 := rfl

theorem qvPath_single (a : Fin N) : qvPath U [a] = 1 := rfl

theorem qvPath_cons_cons (a b : Fin N) (l : List (Fin N)) :
    qvPath U (a :: b :: l) = U a b * qvPath U (b :: l) := rfl

theorem qvPath_pair (a b : Fin N) : qvPath U [a, b] = U a b := by
  rw [qvPath_cons_cons, qvPath_single, mul_one]

theorem qvPath_nonneg {U : Matrix (Fin N) (Fin N) ℝ} (hU : ∀ x y, 0 ≤ U x y) :
    ∀ l, 0 ≤ qvPath U l
  | [] => zero_le_one
  | [_] => zero_le_one
  | a :: b :: l => mul_nonneg (hU a b) (qvPath_nonneg hU (b :: l))

/-- Splitting a path at an interior point `c`. -/
theorem qvPath_append (l₁ : List (Fin N)) (c : Fin N) (l₂ : List (Fin N)) :
    qvPath U (l₁ ++ c :: l₂) = qvPath U (l₁ ++ [c]) * qvPath U (c :: l₂) := by
  induction l₁ with
  | nil => simp [qvPath_single]
  | cons a l ih =>
    cases l with
    | nil => simp [qvPath_cons_cons, qvPath_single]
    | cons b l' =>
      simp only [List.cons_append] at ih ⊢
      rw [qvPath_cons_cons, qvPath_cons_cons, ih]
      ring

/-- Appending one point. -/
theorem qvPath_concat (l : List (Fin N)) (e c : Fin N) :
    qvPath U (l ++ [e, c]) = qvPath U (l ++ [e]) * U e c := by
  rw [qvPath_append U l e [c], qvPath_pair]

/-- Path products of symmetric weights are invariant under reversal. -/
theorem qvPath_reverse {U : Matrix (Fin N) (Fin N) ℝ} (hsym : ∀ x y, U x y = U y x) :
    ∀ l : List (Fin N), qvPath U l.reverse = qvPath U l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    have ih := qvPath_reverse hsym (b :: l)
    rw [List.reverse_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
      qvPath_concat, ← List.reverse_cons, ih, qvPath_cons_cons, hsym b a, mul_comm]

theorem qvPath_mono {U U' : Matrix (Fin N) (Fin N) ℝ} (hU : ∀ x y, 0 ≤ U x y)
    (hUU : ∀ x y, U x y ≤ U' x y) : ∀ l : List (Fin N), qvPath U l ≤ qvPath U' l
  | [] => le_rfl
  | [_] => le_rfl
  | a :: b :: l => by
    rw [qvPath_cons_cons, qvPath_cons_cons]
    exact mul_le_mul (hUU a b) (qvPath_mono hU hUU (b :: l)) (qvPath_nonneg hU _)
      ((hU a b).trans (hUU a b))

/-- The last factor of a path ending in `b`. -/
theorem qvPath_snoc : ∀ (l : List (Fin N)) (hl : l ≠ []) (b : Fin N),
    qvPath U (l ++ [b]) = qvPath U l * U (l.getLast hl) b
  | [a], _, b => by simp [qvPath_pair, qvPath_single]
  | a :: a' :: r, _, b => by
    have ih := qvPath_snoc (a' :: r) (List.cons_ne_nil _ _) b
    simp only [List.cons_append] at ih ⊢
    rw [qvPath_cons_cons, ih, qvPath_cons_cons, List.getLast_cons (List.cons_ne_nil _ _)]
    ring

/-- `qvPath` along `List.ofFn` is the range product. -/
theorem qvPath_ofFn (p : ℕ → Fin N) :
    ∀ n : ℕ, qvPath U (List.ofFn fun i : Fin (n + 1) => p i) =
      ∏ i ∈ Finset.range n, U (p i) (p (i + 1))
  | 0 => by simp [qvPath_single]
  | n + 1 => by
    have ih := qvPath_ofFn (fun i => p (i + 1)) n
    rw [List.ofFn_succ, List.ofFn_succ, Finset.prod_range_succ']
    simp only [Fin.val_zero, Fin.val_succ] at ih ⊢
    rw [qvPath_cons_cons]
    rw [List.ofFn_succ] at ih
    simp only [Fin.val_zero, Fin.val_succ] at ih
    rw [ih, mul_comm]

end PathLemmas

/-- `List.ofFn` over `Fin (n+2)` splits off the first and the last value. -/
theorem qv_ofFn_ends (p : ℕ → Fin N) (n : ℕ) :
    (List.ofFn fun i : Fin (n + 2) => p i) =
      p 0 :: (List.ofFn fun i : Fin n => p (i + 1)) ++ [p (n + 1)] := by
  rw [List.ofFn_succ, List.ofFn_succ']
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last, List.concat_eq_append,
    List.cons_append]

/-!
## Squared size functions on lists
-/

/-- Square of the isotropic size `s^iso_t(a, u, b)` with internal sites `u`:
`L^{-|u|} Π Υ_t` along `a :: u ++ [b]`, `L = ℓ_tη_t`. -/
def qvIsoSq (P : PsiData N) (t : ℝ) (a : Fin N) (u : List (Fin N)) (b : Fin N) : ℝ :=
  (P.lEta t)⁻¹ ^ u.length * qvPath (P.ups t) (a :: u ++ [b])

/-- Square of the averaged size `s^av_t` of the cyclic site list `c :: r`:
`L^{-(|r|+1)} Π Υ_t` along `c :: r ++ [c]`. -/
def qvAvSq (P : PsiData N) (t : ℝ) (c : Fin N) (r : List (Fin N)) : ℝ :=
  (P.lEta t)⁻¹ ^ (r.length + 1) * qvPath (P.ups t) (c :: r ++ [c])

section Sizes

variable (P : PsiData N) (t : ℝ)

theorem qvIsoSq_nil (a b : Fin N) : qvIsoSq P t a [] b = P.ups t a b := by
  simp [qvIsoSq, qvPath_pair]

theorem qvIsoSq_nonneg (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) (a : Fin N)
    (u : List (Fin N)) (b : Fin N) : 0 ≤ qvIsoSq P t a u b :=
  mul_nonneg (pow_nonneg (inv_nonneg.mpr hL.le) _) (qvPath_nonneg hU _)

theorem qvAvSq_nonneg (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) (c : Fin N)
    (r : List (Fin N)) : 0 ≤ qvAvSq P t c r :=
  mul_nonneg (pow_nonneg (inv_nonneg.mpr hL.le) _) (qvPath_nonneg hU _)

/-- (S2) `s^av(c :: r)² = L⁻¹ s^iso(c, r, c)²`. -/
theorem qvAvSq_eq (c : Fin N) (r : List (Fin N)) :
    qvAvSq P t c r = (P.lEta t)⁻¹ * qvIsoSq P t c r c := by
  unfold qvAvSq qvIsoSq
  ring

/-- The concatenation identity `s(a,(u,c,v),b)² = L⁻¹ s(a,u,c)² s(c,v,b)²`. -/
theorem qvIsoSq_split (a : Fin N) (u : List (Fin N)) (c : Fin N) (v : List (Fin N))
    (b : Fin N) :
    qvIsoSq P t a (u ++ c :: v) b =
      (P.lEta t)⁻¹ * qvIsoSq P t a u c * qvIsoSq P t c v b := by
  unfold qvIsoSq
  have hp : a :: (u ++ c :: v) ++ [b] = (a :: u) ++ c :: (v ++ [b]) := by simp
  rw [hp, qvPath_append, List.length_append, List.length_cons, pow_add, pow_succ]
  simp only [List.cons_append]
  ring

/-- (S1) Reversal: `s(a,u,b) = s(b,u^rev,a)`. -/
theorem qvIsoSq_reverse (hsym : ∀ x y, P.ups t x y = P.ups t y x) (a : Fin N)
    (u : List (Fin N)) (b : Fin N) : qvIsoSq P t a u b = qvIsoSq P t b u.reverse a := by
  unfold qvIsoSq
  rw [List.length_reverse, ← qvPath_reverse hsym (a :: u ++ [b])]
  congr 2
  simp

/-- (S1) Rotation of a cycle: `s^av(c :: d :: r) = s^av(d :: r ++ [c])`. -/
theorem qvAvSq_rotate (c d : Fin N) (r : List (Fin N)) :
    qvAvSq P t c (d :: r) = qvAvSq P t d (r ++ [c]) := by
  unfold qvAvSq
  have h1 : c :: (d :: r) ++ [c] = c :: (d :: (r ++ [c])) := by simp
  have h2 : d :: (r ++ [c]) ++ [d] = (d :: r) ++ [c, d] := by simp
  rw [h1, qvPath_cons_cons, h2, qvPath_concat]
  simp only [List.length_cons, List.length_append, List.cons_append, List.length_nil]
  ring

/-- (S3) Doubling: `s(b, (u^rev, c, u), b)² = L⁻¹ (s(c,u,b)²)²`. -/
theorem qvIsoSq_double (hsym : ∀ x y, P.ups t x y = P.ups t y x) (b c : Fin N)
    (u : List (Fin N)) :
    qvIsoSq P t b (u.reverse ++ c :: u) b = (P.lEta t)⁻¹ * qvIsoSq P t c u b ^ 2 := by
  rw [qvIsoSq_split, ← qvIsoSq_reverse P t hsym]
  ring

/-- (S3), second form: `s(a, (u, c, u^rev), a)² = L⁻¹ (s(a,u,c)²)²`. -/
theorem qvIsoSq_double' (hsym : ∀ x y, P.ups t x y = P.ups t y x) (a c : Fin N)
    (u : List (Fin N)) :
    qvIsoSq P t a (u ++ c :: u.reverse) a = (P.lEta t)⁻¹ * qvIsoSq P t a u c ^ 2 := by
  rw [qvIsoSq_split, qvIsoSq_reverse P t hsym c u.reverse a, List.reverse_reverse]
  ring

/-- (S4) Half-av: `s^av(b :: u ++ y :: u^rev)² = L^{-2} (s(b,u,y)²)²`. -/
theorem qvAvSq_half (hsym : ∀ x y, P.ups t x y = P.ups t y x) (b y : Fin N)
    (u : List (Fin N)) :
    qvAvSq P t b (u ++ y :: u.reverse) = (P.lEta t)⁻¹ ^ 2 * qvIsoSq P t b u y ^ 2 := by
  rw [qvAvSq_eq, qvIsoSq_double' P t hsym]
  ring

end Sizes

/-!
## Time comparison
-/

theorem qvIsoSq_time_le (P : PsiData N) {s t : ℝ} (hU : ∀ x y, 0 ≤ P.ups s x y)
    (hst : ∀ x y, P.ups s x y ≤ P.ups t x y) (hLt : 0 < P.lEta t) (hLs : P.lEta t ≤ P.lEta s)
    (a : Fin N) (u : List (Fin N)) (b : Fin N) :
    qvIsoSq P s a u b ≤ (P.lEta t / P.lEta s) ^ u.length * qvIsoSq P t a u b := by
  unfold qvIsoSq
  have hLs0 : 0 < P.lEta s := hLt.trans_le hLs
  have hpow : (P.lEta s)⁻¹ ^ u.length = (P.lEta t / P.lEta s) ^ u.length *
      (P.lEta t)⁻¹ ^ u.length := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hpow, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (qvPath_mono hU hst _) (pow_nonneg (inv_nonneg.mpr hLt.le) _))
    (pow_nonneg (div_nonneg hLt.le hLs0.le) _)

theorem qvAvSq_time_le (P : PsiData N) {s t : ℝ} (hU : ∀ x y, 0 ≤ P.ups s x y)
    (hst : ∀ x y, P.ups s x y ≤ P.ups t x y) (hLt : 0 < P.lEta t) (hLs : P.lEta t ≤ P.lEta s)
    (c : Fin N) (r : List (Fin N)) :
    qvAvSq P s c r ≤ (P.lEta t / P.lEta s) ^ (r.length + 1) * qvAvSq P t c r := by
  unfold qvAvSq
  have hLs0 : 0 < P.lEta s := hLt.trans_le hLs
  have hpow : (P.lEta s)⁻¹ ^ (r.length + 1) = (P.lEta t / P.lEta s) ^ (r.length + 1) *
      (P.lEta t)⁻¹ ^ (r.length + 1) := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hpow, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (qvPath_mono hU hst _) (pow_nonneg (inv_nonneg.mpr hLt.le) _))
    (pow_nonneg (div_nonneg hLt.le hLs0.le) _)

/-!
## Bridges to `Psi.PsiData.sIso` and `sAv`
-/

/-- The exact diagonal `Υ_t(a,a) = 1/(ℓ_tη_t)`. -/
theorem qv_ups_diag (P : PsiData N) (t : ℝ) (a : Fin N) : P.ups t a a = (P.lEta t)⁻¹ := by
  unfold PsiData.ups PsiData.lEta polynomialControl
  rw [Adapters.ErdosRiabov.cyclicDistance_self]
  simp

private theorem qv_rpow_sq {L : ℝ} (hL : 0 < L) (n : ℕ) :
    (L ^ (-(n : ℝ) / 2)) ^ 2 = L⁻¹ ^ n := by
  rw [← Real.rpow_natCast (L ^ (-(n : ℝ) / 2)) 2, ← Real.rpow_mul hL.le, inv_pow,
    ← Real.rpow_natCast L n, ← Real.rpow_neg hL.le]
  congr 1
  push_cast
  ring

/-- `s^iso_t(a,x,b)² = qvIsoSq` with internal sites `x_0, …, x_{n-1}` (the last site of
`x : Fin (n+1) → Fin N` is unused, as in `Psi.Defs`). -/
theorem sIso_sq_eq (P : PsiData N) {t : ℝ} (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    {n : ℕ} (a b : Fin N) (x : Fin (n + 1) → Fin N) :
    P.sIso a b x t ^ 2 = qvIsoSq P t a (List.ofFn fun i : Fin n => x i.castSucc) b := by
  rw [Contr.contr_sIso_eq, mul_pow, Real.sq_sqrt (Contr.contrPathProd_nonneg hU _ _)]
  have he : -(((n + 1 : ℕ) : ℝ) - 1) / 2 = -(n : ℝ) / 2 := by push_cast; ring
  rw [he, qv_rpow_sq hL, qvIsoSq, List.length_ofFn]
  congr 1
  unfold Contr.contrPathProd
  rw [← qvPath_ofFn, qv_ofFn_ends]
  have hl : (List.ofFn fun i : Fin n => isoPoint a b x ((i : ℕ) + 1)) =
      List.ofFn fun i : Fin n => x i.castSucc := by
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    rw [Contr.contr_isoPoint_succ _ _ _ (by omega)]
    rfl
  rw [hl, Contr.contr_isoPoint_zero, Contr.contr_isoPoint_of_le _ _ _ (by omega) (by omega)]

theorem sIso_eq_sqrt (P : PsiData N) {t : ℝ} (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    {n : ℕ} (a b : Fin N) (x : Fin (n + 1) → Fin N) :
    P.sIso a b x t = Real.sqrt (qvIsoSq P t a (List.ofFn fun i : Fin n => x i.castSucc) b) := by
  rw [← sIso_sq_eq P hU hL, Real.sqrt_sq]
  rw [Contr.contr_sIso_eq]
  exact mul_nonneg (Real.rpow_nonneg hL.le _) (Real.sqrt_nonneg _)

/-- `s^av_t(x)² = qvAvSq` of the cycle `x_0 :: x_1, …, x_n` (every length `n + 1 ≥ 1`). -/
theorem sAv_sq_eq (P : PsiData N) {t : ℝ} (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    {n : ℕ} (x : Fin (n + 1) → Fin N) :
    P.sAv x t ^ 2 = qvAvSq P t (x 0) (List.ofFn fun i : Fin n => x i.succ) := by
  rcases n with _ | n
  · rw [Contr.contr_sAv_one P rfl, qvAvSq]
    simp [qvPath_pair, qv_ups_diag]
    ring
  · rw [Contr.contr_sAv_eq P (by omega), mul_pow,
      Real.sq_sqrt (Contr.contrPathProd_nonneg hU _ _)]
    have he : -(((n + 1 + 1 : ℕ) : ℝ)) / 2 = -((n + 2 : ℕ) : ℝ) / 2 := by push_cast; ring
    rw [he, qv_rpow_sq hL, qvAvSq, List.length_ofFn]
    congr 1
    unfold Contr.contrPathProd
    rw [← qvPath_ofFn, qv_ofFn_ends]
    have hl : (List.ofFn fun i : Fin (n + 1) => Contr.contrCycPt x (x ⟨0, by omega⟩) ((i : ℕ) + 1))
        = List.ofFn fun i : Fin (n + 1) => x i.succ := by
      refine List.ofFn_inj.mpr (funext fun i => ?_)
      rw [Contr.contr_cycPt_lt _ _ (by omega)]
      rfl
    rw [hl, Contr.contr_cycPt_lt _ _ (by omega), Contr.contr_cycPt_ge _ _ le_rfl]
    rfl

theorem sAv_eq_sqrt (P : PsiData N) {t : ℝ} (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    {n : ℕ} (x : Fin (n + 1) → Fin N) :
    P.sAv x t = Real.sqrt (qvAvSq P t (x 0) (List.ofFn fun i : Fin n => x i.succ)) := by
  rw [← sAv_sq_eq P hU hL, Real.sqrt_sq]
  unfold PsiData.sAv
  split_ifs
  · exact inv_nonneg.mpr hL.le
  · exact mul_nonneg (Real.rpow_nonneg hL.le _) (Real.sqrt_nonneg _)

end BlockBand.Native.ErdosRiabov.QV
