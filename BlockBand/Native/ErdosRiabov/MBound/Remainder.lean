module

public import BlockBand.Native.ErdosRiabov.MBound.Local

/-!
# The remainder `R` and the extra forcing `F̃`

Bounds on the remainder and the extra forcing of the doubly regularized `M`-chains.

Chain length `k = n+4`, 0-based slots `J = n+3` (anchor `A = n+2`) and `J' = n+1` (anchor
`A' = n`), i.e. the regularizations `Θ̊^{(k)}` and `Θ̊^{(k-2)}`. For any
`X : (Fin (n+4) → Fin N) → ℂ` and kernel `T`:
* `mbRem T X = Γ^{(J)} T^{(J')} X + Γ^{(J')} T^{(J)} X - Γ^{(J')} Γ^{(J)} X` (the remainder `R`,
  with
  `mbRingDecomp`: `T^{(J')}T^{(J)} X = Θ̊^{(J')}Θ̊^{(J)} X + mbRem T X`);
* `mbFt T X = G^{(J)} X + G^{(J')} X` (the extra forcing `F̃`);
* the reduced partial traces `mbTrL X y = Σ_c X(y[J ↦ c])`, `mbTrM X y = Σ_c X(y[J' ↦ c])`
  (`y` with `k-1` sites) and `mbTrLM X w = Σ_b mbTrL X (w[J' ↦ b])` (`k-2` sites).

Main results, for `‖T‖ ≤ C_K Υ` and the single-time inputs `Contr.ContrVSInputs d P t`, if the
reduced traces satisfy `|mbTrL X|, |mbTrM X| ≤ B₁ L s^av_{k-1}` and `|mbTrLM X| ≤ B₂ L s^av_{k-2}`:
* **`mbRem_bound`**: `|R| ≤ (2 C_K (C_K C_wc/η) √C₁'' B₁ + C_K² C₁'' B₂) L s^av_k`;
* **`mbFt_bound`**: `|F̃| ≤ 4 C_K √C₁'' B₁ L s^av_k`.
With `B₁ = A_{k-1}/η`, `B₂ = A_{k-2}/η²` (Ward identity) these are the bounds `R_k η⁻² L s^av`
and `F̃_k η⁻¹ L s^av`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open scoped BigOperators

variable {N : ℕ}

/-!
## Reduced partial traces
-/

theorem mbTr_eq_insertNth {m : ℕ} (j : Fin (m + 1)) (f : (Fin (m + 1) → Fin N) → ℂ)
    (x : Fin (m + 1) → Fin N) :
    mbTr j f x = ∑ c, f (Fin.insertNth j c (Fin.removeNth j x)) := by
  simp only [mbTr, Fin.insertNth_removeNth]

/-- A slot operator on a function of the reduced sites. -/
theorem mbSlot_comp_removeNth (K : Matrix (Fin N) (Fin N) ℂ) {m : ℕ} (p : Fin (m + 1))
    (i : Fin m) (g : (Fin m → Fin N) → ℂ) (x : Fin (m + 1) → Fin N) :
    mbSlot K (p.succAbove i) (fun y => g (Fin.removeNth p y)) x =
      mbSlot K i g (Fin.removeNth p x) := by
  simp only [mbSlot, Fin.removeNth_update_succAbove, Fin.removeNth_apply]

theorem mbTr_slot_comm (K : Matrix (Fin N) (Fin N) ℂ) {k : ℕ} {i j : Fin k} (hij : i ≠ j)
    (f : (Fin k → Fin N) → ℂ) : mbTr j (mbSlot K i f) = mbSlot K i (mbTr j f) := by
  funext x
  simp only [mbTr, mbSlot, update_of_ne hij, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [update_comm hij]

theorem mbTr_tr_comm {k : ℕ} {i j : Fin k} (hij : i ≠ j) (f : (Fin k → Fin N) → ℂ) :
    mbTr i (mbTr j f) = mbTr j (mbTr i f) := by
  funext x
  simp only [mbTr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [update_comm hij]

theorem mbTr_gamma_comm (K : Matrix (Fin N) (Fin N) ℂ) {k : ℕ} {i j a : Fin k} (hij : i ≠ j)
    (hia : i ≠ a) (f : (Fin k → Fin N) → ℂ) :
    mbTr i (mbGamma K j a f) = mbGamma K j a (mbTr i f) := by
  funext x
  simp only [mbTr, mbGamma, update_of_ne hij.symm, update_of_ne hia.symm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [update_comm hij]

/-- `removeNth (i+1) (x[i ↦ x_{i+1}]) = removeNth i x` (adjacent anchor). -/
theorem mb_removeNth_update_adj {m : ℕ} (i : Fin (m + 1)) (x : Fin (m + 2) → Fin N) :
    Fin.removeNth i.succ (update x i.castSucc (x i.succ)) = Fin.removeNth i.castSucc x := by
  funext l
  simp only [Fin.removeNth_apply]
  rcases lt_trichotomy (l : ℕ) i with h | h | h
  · have e1 : i.succ.succAbove l = l.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)
    have e2 : i.castSucc.succAbove l = l.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)
    rw [e1, e2, update_of_ne (by rw [Ne, Fin.ext_iff]; simp; omega)]
  · have hl : l = i := Fin.ext h
    subst hl
    rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp),
      Fin.succAbove_of_le_castSucc _ _ le_rfl, update_self]
  · have e1 : i.succ.succAbove l = l.succ :=
      Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)
    have e2 : i.castSucc.succAbove l = l.succ :=
      Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)
    rw [e1, e2, update_of_ne (by rw [Ne, Fin.ext_iff]; simp; omega)]

/-!
## The objects
-/

section Objects

variable {n : ℕ}

/-- Slot `J = n+3` (the 1-based slot `k`). -/
def mbJ (n : ℕ) : Fin (n + 4) := Fin.last (n + 3)
/-- Anchor `A = n+2` (the 1-based slot `k-1`). -/
def mbA (n : ℕ) : Fin (n + 4) := ⟨n + 2, by omega⟩
/-- Slot `J' = n+1` (the 1-based slot `k-2`). -/
def mbJ' (n : ℕ) : Fin (n + 4) := ⟨n + 1, by omega⟩
/-- Anchor `A' = n` (the 1-based slot `k-3`). -/
def mbA' (n : ℕ) : Fin (n + 4) := ⟨n, by omega⟩

/-- The remainder `R = Γ^{(J)} T^{(J')} X + Γ^{(J')} T^{(J)} X - Γ^{(J')} Γ^{(J)} X`. -/
def mbRem (T : Matrix (Fin N) (Fin N) ℂ) (X : (Fin (n + 4) → Fin N) → ℂ) :
    (Fin (n + 4) → Fin N) → ℂ :=
  mbGamma T (mbJ n) (mbA n) (mbSlot T (mbJ' n) X) +
    mbGamma T (mbJ' n) (mbA' n) (mbSlot T (mbJ n) X) -
      mbGamma T (mbJ' n) (mbA' n) (mbGamma T (mbJ n) (mbA n) X)

/-- The extra forcing `F̃ = G^{(J)} X + G^{(J')} X`. -/
def mbFt (T : Matrix (Fin N) (Fin N) ℂ) (X : (Fin (n + 4) → Fin N) → ℂ) :
    (Fin (n + 4) → Fin N) → ℂ :=
  mbG T (mbJ n) (mbA n) X + mbG T (mbJ' n) (mbA' n) X

/-- `Σ_c X(y[J ↦ c])` as a function of the `n+3` remaining sites. -/
def mbTrL (X : (Fin (n + 4) → Fin N) → ℂ) : (Fin (n + 3) → Fin N) → ℂ :=
  fun y => ∑ c, X (Fin.insertNth (Fin.last (n + 3)) c y)

/-- `Σ_c X(y[J' ↦ c])` as a function of the `n+3` remaining sites. -/
def mbTrM (X : (Fin (n + 4) → Fin N) → ℂ) : (Fin (n + 3) → Fin N) → ℂ :=
  fun y => ∑ c, X (Fin.insertNth (mbJ' n) c y)

/-- `Σ_b Σ_c X(w[J' ↦ b][J ↦ c])` as a function of the `n+2` remaining sites. -/
def mbTrLM (X : (Fin (n + 4) → Fin N) → ℂ) : (Fin (n + 2) → Fin N) → ℂ :=
  fun w => ∑ b, mbTrL X (Fin.insertNth (⟨n + 1, by omega⟩ : Fin (n + 3)) b w)

theorem mbJ'_eq : (mbJ n).succAbove (⟨n + 1, by omega⟩ : Fin (n + 3)) = mbJ' n := by
  apply Fin.ext
  rw [mbJ, Fin.succAbove_last]
  rfl

theorem mbJ_eq : (mbJ' n).succAbove (Fin.last (n + 2)) = mbJ n := by
  apply Fin.ext
  rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp [mbJ'])]
  simp [mbJ]

theorem mbTr_J (X : (Fin (n + 4) → Fin N) → ℂ) (x : Fin (n + 4) → Fin N) :
    mbTr (mbJ n) X x = mbTrL X (Fin.removeNth (mbJ n) x) := by
  rw [mbTr_eq_insertNth]
  rfl

theorem mbTr_J' (X : (Fin (n + 4) → Fin N) → ℂ) (x : Fin (n + 4) → Fin N) :
    mbTr (mbJ' n) X x = mbTrM X (Fin.removeNth (mbJ' n) x) := by
  rw [mbTr_eq_insertNth]
  rfl

theorem mbTr_J'_J (X : (Fin (n + 4) → Fin N) → ℂ) (x : Fin (n + 4) → Fin N) :
    mbTr (mbJ' n) (mbTr (mbJ n) X) x =
      mbTrLM X (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 3)) (Fin.removeNth (mbJ n) x)) := by
  unfold mbTrLM
  show ∑ b, mbTr (mbJ n) X (update x (mbJ' n) b) = _
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mbTr_J, ← mbJ'_eq, Fin.removeNth_update_succAbove, Fin.insertNth_removeNth]

end Objects

/-!
## The bounds
-/

private theorem mb_prev_J (n : ℕ) : mbPrev (mbJ n) = mbA n := by
  apply Fin.ext
  simp only [mbPrev, mbJ, mbA, Fin.val_last]
  rw [show n + 1 + 2 + (n + 1 + 2) = (n + 2) + (n + 4) by ring, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

private theorem mb_prev_J' (n : ℕ) : mbPrev (mbJ' n) = mbA' n := by
  apply Fin.ext
  simp only [mbPrev, mbJ', mbA']
  rw [show n + 1 + (n + 1 + 2) = n + (n + 4) by ring, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

private theorem mb_next_A (n : ℕ) : mbNext (mbA n) = mbJ n := by
  apply Fin.ext
  simp only [mbNext, mbA, mbJ, Fin.val_last]
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem mb_next_A' (n : ℕ) : mbNext (mbA' n) = mbJ' n := by
  apply Fin.ext
  simp only [mbNext, mbA', mbJ']
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem mb_prev_J'_in (n : ℕ) :
    mbPrev (⟨n + 1, by omega⟩ : Fin (n + 3)) = (⟨n, by omega⟩ : Fin (n + 3)) := by
  apply Fin.ext
  simp only [mbPrev]
  rw [show n + 1 + (n + 2) = n + (n + 3) by ring, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

section Remove

variable (P : PsiData N) (t : ℝ) {d : VSData} (hin : ContrVSInputs d P t)
include hin

/-- Removing `J` with the anchor prefactor `Υ(x_J, x_A)` (and with `Υ(x_A, x_J)`). -/
private theorem mb_remove_J {n : ℕ} (x : Fin (n + 4) → Fin N) :
    P.ups t (x (mbJ n)) (x (mbA n)) * (P.lEta t * P.sAv (Fin.removeNth (mbJ n) x) t) ≤
      Real.sqrt d.C1pp * (P.lEta t * P.sAv x t) := by
  have h := (mb_remove_le P t hin (n := n + 1) (mbJ n) x).1
  rwa [mb_prev_J] at h

private theorem mb_remove_J' {n : ℕ} (x : Fin (n + 4) → Fin N) :
    P.ups t (x (mbJ' n)) (x (mbA' n)) * (P.lEta t * P.sAv (Fin.removeNth (mbJ' n) x) t) ≤
      Real.sqrt d.C1pp * (P.lEta t * P.sAv x t) := by
  have h := (mb_remove_le P t hin (n := n + 1) (mbJ' n) x).1
  rwa [mb_prev_J'] at h

private theorem mb_remove_A {n : ℕ} (x : Fin (n + 4) → Fin N) :
    P.ups t (x (mbA n)) (x (mbJ n)) * (P.lEta t * P.sAv (Fin.removeNth (mbA n) x) t) ≤
      Real.sqrt d.C1pp * (P.lEta t * P.sAv x t) := by
  have h := (mb_remove_le P t hin (n := n + 1) (mbA n) x).2
  rwa [mb_next_A] at h

private theorem mb_remove_A' {n : ℕ} (x : Fin (n + 4) → Fin N) :
    P.ups t (x (mbA' n)) (x (mbJ' n)) * (P.lEta t * P.sAv (Fin.removeNth (mbA' n) x) t) ≤
      Real.sqrt d.C1pp * (P.lEta t * P.sAv x t) := by
  have h := (mb_remove_le P t hin (n := n + 1) (mbA' n) x).2
  rwa [mb_next_A'] at h

private theorem mb_LsAv_nonneg {m : ℕ} (y : Fin m → Fin N) : 0 ≤ P.lEta t * P.sAv y t := by
  refine mul_nonneg hin.lEta_pos.le ?_
  unfold PsiData.sAv
  split_ifs
  · exact inv_nonneg.mpr hin.lEta_pos.le
  · exact mul_nonneg (Real.rpow_nonneg hin.lEta_pos.le _) (Real.sqrt_nonneg _)

end Remove

/-- `‖T(u,v)‖ · B · L s^av(y) ≤ C_K √C₁'' B L s^av(x)` after a vertex removal. -/
private theorem mb_entry_remove {d : VSData} {CK : ℝ} (hCK : 0 ≤ CK) {B Ly Lx u : ℝ}
    (hB : 0 ≤ B) (hLy : 0 ≤ Ly)
    {e : ℂ} (he : ‖e‖ ≤ CK * u) (hrem : u * Ly ≤ Real.sqrt d.C1pp * Lx) :
    ‖e‖ * (B * Ly) ≤ CK * Real.sqrt d.C1pp * B * Lx := by
  calc ‖e‖ * (B * Ly) ≤ CK * u * (B * Ly) := mul_le_mul_of_nonneg_right he (mul_nonneg hB hLy)
    _ = CK * B * (u * Ly) := by ring
    _ ≤ CK * B * (Real.sqrt d.C1pp * Lx) :=
        mul_le_mul_of_nonneg_left hrem (mul_nonneg hCK hB)
    _ = CK * Real.sqrt d.C1pp * B * Lx := by ring

section Bounds

variable (P : PsiData N) (t : ℝ) {d : VSData} (hin : ContrVSInputs d P t)
  (T : Matrix (Fin N) (Fin N) ℂ) {CK : ℝ} (hCK : 0 ≤ CK)
  (hT : ∀ a b, ‖T a b‖ ≤ CK * P.ups t a b)
include hin hCK hT

/-- **M.11**: under `|mbTrL X|, |mbTrM X| ≤ B₁ L s^av_{n+3}`
and `|mbTrLM X| ≤ B₂ L s^av_{n+2}`,
`|R(x)| ≤ (2 C_K (C_K C_wc/η) √C₁'' B₁ + C_K² C₁'' B₂) L s^av_{n+4}(x)`.
-/
theorem mbRem_bound {n : ℕ} (X : (Fin (n + 4) → Fin N) → ℂ) {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁)
    (hB₂ : 0 ≤ B₂)
    (hL : ∀ y, ‖mbTrL X y‖ ≤ B₁ * (P.lEta t * P.sAv y t))
    (hM : ∀ y, ‖mbTrM X y‖ ≤ B₁ * (P.lEta t * P.sAv y t))
    (hLM : ∀ w, ‖mbTrLM X w‖ ≤ B₂ * (P.lEta t * P.sAv w t)) (x : Fin (n + 4) → Fin N) :
    ‖mbRem T X x‖ ≤ (2 * CK * (CK * d.Cwc / vsHeight P.z t) * Real.sqrt d.C1pp * B₁ +
      CK ^ 2 * d.C1pp * B₂) * (P.lEta t * P.sAv x t) := by
  have hη := hin.height_pos
  set Cθ := CK * d.Cwc / vsHeight P.z t with hCθ
  have hCθ0 : 0 ≤ Cθ := div_nonneg (mul_nonneg hCK (by
    have := d.one_le_Cwc; linarith)) hη.le
  have hLx := mb_LsAv_nonneg P t hin x
  -- first term
  have h1 : ‖mbGamma T (mbJ n) (mbA n) (mbSlot T (mbJ' n) X) x‖ ≤
      CK * Real.sqrt d.C1pp * (Cθ * B₁) * (P.lEta t * P.sAv x t) := by
    have hc : mbTr (mbJ n) (mbSlot T (mbJ' n) X) x =
        mbSlot T (⟨n + 1, by omega⟩ : Fin (n + 3)) (mbTrL X) (Fin.removeNth (mbJ n) x) := by
      rw [mbTr_slot_comm T (by simp [mbJ', mbJ, Fin.ext_iff]), ← mbSlot_comp_removeNth, mbJ'_eq]
      congr 1
      funext y
      exact mbTr_J X y
    unfold mbGamma
    rw [hc, norm_mul]
    have hact := mb_thetaAction P t hin (n := n + 1) T hCK
      (mul_nonneg hB₁ hin.lEta_pos.le) hT (mbTrL X)
      (fun y => (hL y).trans (le_of_eq (by ring))) ⟨n + 1, by omega⟩ (Fin.removeNth (mbJ n) x)
    have hact' : ‖mbSlot T (⟨n + 1, by omega⟩ : Fin (n + 3)) (mbTrL X)
        (Fin.removeNth (mbJ n) x)‖ ≤ (Cθ * B₁) * (P.lEta t * P.sAv (Fin.removeNth (mbJ n) x) t) :=
      hact.trans (le_of_eq (by rw [hCθ]; ring))
    calc ‖T (x (mbJ n)) (x (mbA n))‖ * ‖_‖
        ≤ ‖T (x (mbJ n)) (x (mbA n))‖ *
          ((Cθ * B₁) * (P.lEta t * P.sAv (Fin.removeNth (mbJ n) x) t)) :=
          mul_le_mul_of_nonneg_left hact' (norm_nonneg _)
      _ ≤ _ := mb_entry_remove hCK (mul_nonneg hCθ0 hB₁)
          (mb_LsAv_nonneg P t hin _) (hT _ _) (mb_remove_J P t hin x)
  -- second term
  have h2 : ‖mbGamma T (mbJ' n) (mbA' n) (mbSlot T (mbJ n) X) x‖ ≤
      CK * Real.sqrt d.C1pp * (Cθ * B₁) * (P.lEta t * P.sAv x t) := by
    have hc : mbTr (mbJ' n) (mbSlot T (mbJ n) X) x =
        mbSlot T (Fin.last (n + 2)) (mbTrM X) (Fin.removeNth (mbJ' n) x) := by
      rw [mbTr_slot_comm T (by simp [mbJ', mbJ, Fin.ext_iff]), ← mbSlot_comp_removeNth, mbJ_eq]
      congr 1
      funext y
      exact mbTr_J' X y
    unfold mbGamma
    rw [hc, norm_mul]
    have hact := mb_thetaAction P t hin (n := n + 1) T hCK
      (mul_nonneg hB₁ hin.lEta_pos.le) hT (mbTrM X)
      (fun y => (hM y).trans (le_of_eq (by ring))) (Fin.last (n + 2)) (Fin.removeNth (mbJ' n) x)
    have hact' : ‖mbSlot T (Fin.last (n + 2)) (mbTrM X) (Fin.removeNth (mbJ' n) x)‖ ≤
        (Cθ * B₁) * (P.lEta t * P.sAv (Fin.removeNth (mbJ' n) x) t) :=
      hact.trans (le_of_eq (by rw [hCθ]; ring))
    calc ‖T (x (mbJ' n)) (x (mbA' n))‖ * ‖_‖
        ≤ ‖T (x (mbJ' n)) (x (mbA' n))‖ *
          ((Cθ * B₁) * (P.lEta t * P.sAv (Fin.removeNth (mbJ' n) x) t)) :=
          mul_le_mul_of_nonneg_left hact' (norm_nonneg _)
      _ ≤ _ := mb_entry_remove hCK (mul_nonneg hCθ0 hB₁)
          (mb_LsAv_nonneg P t hin _) (hT _ _) (mb_remove_J' P t hin x)
  -- third term
  have h3 : ‖mbGamma T (mbJ' n) (mbA' n) (mbGamma T (mbJ n) (mbA n) X) x‖ ≤
      CK ^ 2 * d.C1pp * B₂ * (P.lEta t * P.sAv x t) := by
    have hc : mbTr (mbJ' n) (mbGamma T (mbJ n) (mbA n) X) x =
        T (x (mbJ n)) (x (mbA n)) *
          mbTrLM X (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 3)) (Fin.removeNth (mbJ n) x)) := by
      rw [mbTr_gamma_comm T (by simp [mbJ', mbJ, Fin.ext_iff]) (by simp [mbJ', mbA, Fin.ext_iff])]
      unfold mbGamma
      rw [mbTr_tr_comm (by simp [mbJ', mbJ, Fin.ext_iff]), mbTr_J'_J]
    show ‖T (x (mbJ' n)) (x (mbA' n)) * mbTr (mbJ' n) (mbGamma T (mbJ n) (mbA n) X) x‖ ≤ _
    rw [hc, norm_mul, norm_mul]
    set y := Fin.removeNth (mbJ n) x
    set w := Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 3)) y
    have hw := hLM w
    have hrem1 : P.ups t (y ⟨n + 1, by omega⟩) (y ⟨n, by omega⟩) * (P.lEta t * P.sAv w t) ≤
        Real.sqrt d.C1pp * (P.lEta t * P.sAv y t) := by
      have h := (mb_remove_le P t hin (n := n) (⟨n + 1, by omega⟩ : Fin (n + 3)) y).1
      rwa [mb_prev_J'_in] at h
    have hy1 : y ⟨n + 1, by omega⟩ = x (mbJ' n) := by
      simp only [y, Fin.removeNth_apply]
      rw [← mbJ'_eq]
    have hy0 : y ⟨n, by omega⟩ = x (mbA' n) := by
      simp only [y, Fin.removeNth_apply]
      congr 1
      apply Fin.ext
      rw [mbJ, Fin.succAbove_last]
      rfl
    rw [hy1, hy0] at hrem1
    have hrem2 := mb_remove_J P t hin x
    have hsC : Real.sqrt d.C1pp * Real.sqrt d.C1pp = d.C1pp :=
      Real.mul_self_sqrt (by have := d.one_le_C1pp; linarith)
    calc ‖T (x (mbJ' n)) (x (mbA' n))‖ * (‖T (x (mbJ n)) (x (mbA n))‖ * ‖mbTrLM X w‖)
        ≤ (CK * P.ups t (x (mbJ' n)) (x (mbA' n))) *
            ((CK * P.ups t (x (mbJ n)) (x (mbA n))) * (B₂ * (P.lEta t * P.sAv w t))) := by
          refine mul_le_mul (hT _ _) (mul_le_mul (hT _ _) hw (norm_nonneg _)
            (mul_nonneg hCK (hin.nonneg _ _))) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (mul_nonneg hCK (hin.nonneg _ _))
      _ = CK ^ 2 * B₂ * P.ups t (x (mbJ n)) (x (mbA n)) *
            (P.ups t (x (mbJ' n)) (x (mbA' n)) * (P.lEta t * P.sAv w t)) := by ring
      _ ≤ CK ^ 2 * B₂ * P.ups t (x (mbJ n)) (x (mbA n)) *
            (Real.sqrt d.C1pp * (P.lEta t * P.sAv y t)) :=
          mul_le_mul_of_nonneg_left hrem1 (mul_nonneg (mul_nonneg (sq_nonneg _) hB₂)
            (hin.nonneg _ _))
      _ = CK ^ 2 * B₂ * Real.sqrt d.C1pp *
            (P.ups t (x (mbJ n)) (x (mbA n)) * (P.lEta t * P.sAv y t)) := by ring
      _ ≤ CK ^ 2 * B₂ * Real.sqrt d.C1pp * (Real.sqrt d.C1pp * (P.lEta t * P.sAv x t)) :=
          mul_le_mul_of_nonneg_left hrem2 (mul_nonneg (mul_nonneg (sq_nonneg _) hB₂)
            (Real.sqrt_nonneg _))
      _ = CK ^ 2 * (Real.sqrt d.C1pp * Real.sqrt d.C1pp) * B₂ * (P.lEta t * P.sAv x t) := by
          ring
      _ = CK ^ 2 * d.C1pp * B₂ * (P.lEta t * P.sAv x t) := by rw [hsC]
  unfold mbRem
  simp only [Pi.add_apply, Pi.sub_apply]
  calc ‖_ + _ - _‖ ≤ ‖mbGamma T (mbJ n) (mbA n) (mbSlot T (mbJ' n) X) x‖ +
        ‖mbGamma T (mbJ' n) (mbA' n) (mbSlot T (mbJ n) X) x‖ +
        ‖mbGamma T (mbJ' n) (mbA' n) (mbGamma T (mbJ n) (mbA n) X) x‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ _ := by nlinarith [h1, h2, h3]

/-- **M.12**: under `|mbTrL X|, |mbTrM X| ≤ B₁ L s^av_{n+3}`,
`|F̃(x)| ≤ 4 C_K √C₁'' B₁ L s^av_{n+4}(x)`.
-/
theorem mbFt_bound {n : ℕ} (X : (Fin (n + 4) → Fin N) → ℂ) {B₁ : ℝ} (hB₁ : 0 ≤ B₁)
    (hL : ∀ y, ‖mbTrL X y‖ ≤ B₁ * (P.lEta t * P.sAv y t))
    (hM : ∀ y, ‖mbTrM X y‖ ≤ B₁ * (P.lEta t * P.sAv y t)) (x : Fin (n + 4) → Fin N) :
    ‖mbFt T X x‖ ≤ 4 * CK * Real.sqrt d.C1pp * B₁ * (P.lEta t * P.sAv x t) := by
  have hsymU := hin.symm
  -- the four reduced values
  have eJa : mbTr (mbJ n) X (update x (mbA n) (x (mbJ n))) =
      mbTrL X (Fin.removeNth (mbA n) x) := by
    rw [mbTr_J]
    congr 1
    have := mb_removeNth_update_adj (m := n + 2) (⟨n + 2, by omega⟩ : Fin (n + 3)) x
    simpa [mbJ, mbA, Fin.succ, Fin.castSucc, Fin.last] using this
  have eJ'a : mbTr (mbJ' n) X (update x (mbA' n) (x (mbJ' n))) =
      mbTrM X (Fin.removeNth (mbA' n) x) := by
    rw [mbTr_J']
    congr 1
    have := mb_removeNth_update_adj (m := n + 2) (⟨n, by omega⟩ : Fin (n + 3)) x
    simpa [mbJ', mbA', Fin.succ, Fin.castSucc] using this
  have hT1 : ‖T (x (mbA n)) (x (mbJ n))‖ ≤ CK * P.ups t (x (mbJ n)) (x (mbA n)) := by
    rw [hsymU]; exact hT _ _
  have hT2 : ‖T (x (mbA' n)) (x (mbJ' n))‖ ≤ CK * P.ups t (x (mbJ' n)) (x (mbA' n)) := by
    rw [hsymU]; exact hT _ _
  have t1 := mb_entry_remove hCK hB₁ (mb_LsAv_nonneg P t hin _) (hT _ _)
    (mb_remove_A P t hin x)
  have t2 := mb_entry_remove hCK hB₁ (mb_LsAv_nonneg P t hin _) hT1
    (mb_remove_J P t hin x)
  have t3 := mb_entry_remove hCK hB₁ (mb_LsAv_nonneg P t hin _) (hT _ _)
    (mb_remove_A' P t hin x)
  have t4 := mb_entry_remove hCK hB₁ (mb_LsAv_nonneg P t hin _) hT2
    (mb_remove_J' P t hin x)
  unfold mbFt mbG
  simp only [Pi.add_apply]
  rw [eJa, eJ'a, mbTr_J, mbTr_J']
  calc ‖T (x (mbA n)) (x (mbJ n)) * (mbTrL X (Fin.removeNth (mbA n) x) +
          mbTrL X (Fin.removeNth (mbJ n) x)) +
        T (x (mbA' n)) (x (mbJ' n)) * (mbTrM X (Fin.removeNth (mbA' n) x) +
          mbTrM X (Fin.removeNth (mbJ' n) x))‖
      ≤ ‖T (x (mbA n)) (x (mbJ n))‖ * (B₁ * (P.lEta t * P.sAv (Fin.removeNth (mbA n) x) t)) +
        ‖T (x (mbA n)) (x (mbJ n))‖ * (B₁ * (P.lEta t * P.sAv (Fin.removeNth (mbJ n) x) t)) +
        (‖T (x (mbA' n)) (x (mbJ' n))‖ *
            (B₁ * (P.lEta t * P.sAv (Fin.removeNth (mbA' n) x) t)) +
          ‖T (x (mbA' n)) (x (mbJ' n))‖ *
            (B₁ * (P.lEta t * P.sAv (Fin.removeNth (mbJ' n) x) t))) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, ← mul_add]
          exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hL _) (hL _)))
            (norm_nonneg _)
        · rw [norm_mul, ← mul_add]
          exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hM _) (hM _)))
            (norm_nonneg _)
    _ ≤ _ := by linarith [t1, t2, t3, t4]

end Bounds

end BlockBand.Native.ErdosRiabov.MBound
