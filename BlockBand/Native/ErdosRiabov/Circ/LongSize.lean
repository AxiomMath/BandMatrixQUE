module

public import BlockBand.Native.ErdosRiabov.Circ.LongWard
public import BlockBand.Native.ErdosRiabov.Contr.MoreSplit

/-!
# Removing one site of `s^av`

Removing one site from the averaged size function `s^av` costs a factor `√C₁''` against the
`Υ`-link to a neighbouring site.

Inputs: `hin : Contr.ContrVSInputs d P t` (fields `nonneg`, `symm`, `lEta_pos`, `triangle`:
the triangle bound `Υ(x,a) Υ(a,y) ≤ C₁''/L Υ(x,y)`), `Υ = P.ups t`, `L = P.lEta t`, `C₁'' = d.C1pp`.

* `circ_cyc_eq`: the cyclic product of `y : Fin (k+1) → Fin N` split at the last site.
* `circ_sAv_init_le`: for `x : Fin (m+3) → Fin N` and a cyclic neighbour `u` of the last site,
  `Υ(u, x_last) s^av_{m+2}(init x) ≤ √C₁'' s^av_{m+3}(x)`.
* **`circ_sAv_removeNth_le`**: the same for any site `i` (rotation invariance
  `Contr.contr_sAv_rotate`): `Υ(u, x_i) s^av_{m+2}(x \ x_i) ≤ √C₁'' s^av_{m+3}(x)` for
  `u = x_{i-1}` or `u = x_{i+1}` (cyclic).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open Function
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Native.ErdosRiabov.Flow

variable {N : ℕ}

theorem circ_cyc_eq (U : Matrix (Fin N) (Fin N) ℝ) {k : ℕ} (y : Fin (k + 1) → Fin N) :
    ∏ e : Fin (k + 1), U (y e) (y (finRotate (k + 1) e)) =
      (∏ e : Fin k, U (y e.castSucc) (y e.succ)) * U (y (Fin.last k)) (y 0) := by
  rw [Fin.prod_univ_castSucc, finRotate_last]
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  congr 2
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last e).ne]
  simp

section Remove

variable {d : VSData} (P : PsiData N) {t : ℝ} (hin : ContrVSInputs d P t)
include hin

/-- **Removing the last site**: for a cyclic neighbour `u ∈ {x_{m+1}, x_0}` of the last site,
`Υ(u, x_{m+2}) s^av_{m+2}(init x) ≤ √C₁'' s^av_{m+3}(x)` (triangle bound). -/
theorem circ_sAv_init_le {m : ℕ} (x : Fin (m + 3) → Fin N) {u : Fin N}
    (hu : u = x (Fin.last (m + 1)).castSucc ∨ u = x 0) :
    P.ups t u (x (Fin.last (m + 2))) * P.sAv (Fin.init x) t ≤
      Real.sqrt d.C1pp * P.sAv x t := by
  set U := P.ups t
  set L := P.lEta t
  have hL : 0 < L := hin.lEta_pos
  have hC : 0 ≤ d.C1pp := by linarith [d.one_le_C1pp]
  set R := ∏ e : Fin (m + 1), U (x e.castSucc.castSucc) (x e.succ.castSucc) with hR
  set xp := x (Fin.last (m + 1)).castSucc
  set xl := x (Fin.last (m + 2))
  have hR0 : 0 ≤ R := Finset.prod_nonneg fun e _ => hin.nonneg _ _
  have hcx : ∏ e : Fin (m + 3), U (x e) (x (finRotate (m + 3) e)) = R * U xp xl * U xl (x 0) := by
    rw [circ_cyc_eq, Fin.prod_univ_castSucc]
    simp only [Fin.succ_castSucc, Fin.succ_last, R, xp, xl]
  have hci : ∏ e : Fin (m + 2), U (Fin.init x e) (Fin.init x (finRotate (m + 2) e)) =
      R * U xp (x 0) := by
    rw [circ_cyc_eq]
    simp only [Fin.init, R, xp]
    rfl
  have hsx : P.sAv x t = L ^ (-((m + 3 : ℕ) : ℝ) / 2) * Real.sqrt (R * U xp xl * U xl (x 0)) := by
    unfold PsiData.sAv
    rw [ite_eq_right (by omega), hcx]
  have hsi : P.sAv (Fin.init x) t =
      L ^ (-((m + 2 : ℕ) : ℝ) / 2) * Real.sqrt (R * U xp (x 0)) := by
    unfold PsiData.sAv
    rw [ite_eq_right (by omega), hci]
  set v := U u xl
  have hv : 0 ≤ v := hin.nonneg _ _
  have hab : 0 ≤ U xp xl := hin.nonneg _ _
  have hbb : 0 ≤ U xl (x 0) := hin.nonneg _ _
  -- the triangle bound step
  have hkey : v ^ 2 * (R * U xp (x 0)) ≤ d.C1pp / L * (R * U xp xl * U xl (x 0)) := by
    rcases hu with rfl | rfl
    · have h := hin.triangle xl xp (x 0)
      rw [hin.symm xl xp] at h
      calc U xp xl ^ 2 * (R * U xp (x 0)) = R * U xp xl * (U xp xl * U xp (x 0)) := by ring
        _ ≤ R * U xp xl * (d.C1pp / L * U xl (x 0)) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg hR0 hab)
        _ = _ := by ring
    · have h := hin.triangle xl (x 0) xp
      rw [hin.symm (x 0) xp, hin.symm xl xp] at h
      have hv' : U (x 0) xl = U xl (x 0) := hin.symm _ _
      change U (x 0) xl ^ 2 * (R * U xp (x 0)) ≤ _
      rw [hv']
      calc U xl (x 0) ^ 2 * (R * U xp (x 0)) = R * U xl (x 0) * (U xl (x 0) * U xp (x 0)) := by
            ring
        _ ≤ R * U xl (x 0) * (d.C1pp / L * U xp xl) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg hR0 hbb)
        _ = _ := by ring
  have hsq : v * Real.sqrt (R * U xp (x 0)) ≤
      Real.sqrt d.C1pp * (Real.sqrt L)⁻¹ * Real.sqrt (R * U xp xl * U xl (x 0)) := by
    calc v * Real.sqrt (R * U xp (x 0)) = Real.sqrt (v ^ 2 * (R * U xp (x 0))) := by
          rw [Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv]
      _ ≤ Real.sqrt (d.C1pp / L * (R * U xp xl * U xl (x 0))) := Real.sqrt_le_sqrt hkey
      _ = _ := by
          rw [Real.sqrt_mul (div_nonneg hC hL.le), Real.sqrt_div' _ hL.le, div_eq_mul_inv]
  have he : L ^ (-((m + 3 : ℕ) : ℝ) / 2) = L ^ (-((m + 2 : ℕ) : ℝ) / 2) * (Real.sqrt L)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hL.le, ← Real.rpow_add hL]
    congr 1
    push_cast
    ring
  rw [hsx, hsi, he]
  have hLe : 0 ≤ L ^ (-((m + 2 : ℕ) : ℝ) / 2) := Real.rpow_nonneg hL.le _
  calc v * (L ^ (-((m + 2 : ℕ) : ℝ) / 2) * Real.sqrt (R * U xp (x 0)))
      = L ^ (-((m + 2 : ℕ) : ℝ) / 2) * (v * Real.sqrt (R * U xp (x 0))) := by ring
    _ ≤ L ^ (-((m + 2 : ℕ) : ℝ) / 2) * (Real.sqrt d.C1pp * (Real.sqrt L)⁻¹ *
          Real.sqrt (R * U xp xl * U xl (x 0))) := mul_le_mul_of_nonneg_left hsq hLe
    _ = _ := by ring

/-- **Removing one site** (one application of the triangle bound (U4) restores the dropped
link): for `x : Fin (m+3) → Fin N`, a site `i` and a cyclic neighbour `u` of `x_i`
(`u = x_{i-1}` or `u = x_{i+1}`, indices mod `m+3`):
`Υ(u, x_i) s^av_{m+2}(x \ x_i) ≤ √C₁'' s^av_{m+3}(x)`.
-/
theorem circ_sAv_removeNth_le {m : ℕ} (x : Fin (m + 3) → Fin N) (i : Fin (m + 3)) {u : Fin N}
    (hu : u = x ⟨((i : ℕ) + (m + 2)) % (m + 3), Nat.mod_lt _ (by omega)⟩ ∨
      u = x ⟨((i : ℕ) + 1) % (m + 3), Nat.mod_lt _ (by omega)⟩) :
    P.ups t u (x i) * P.sAv (Fin.removeNth i x) t ≤ Real.sqrt d.C1pp * P.sAv x t := by
  have hi := i.isLt
  set w : Fin (m + 3) → Fin N :=
    fun e => x ⟨((e : ℕ) + ((i : ℕ) + 1)) % (m + 3), Nat.mod_lt _ (by omega)⟩ with hw
  have hw1 : P.sAv w t = P.sAv x t :=
    contr_sAv_rotate P x w ((i : ℕ) + 1) (fun n hn => rfl) t
  have hw2 : P.sAv (Fin.init w) t = P.sAv (Fin.removeNth i x) t := by
    refine contr_sAv_rotate P (Fin.removeNth i x) (Fin.init w) i (fun n hn => ?_) t
    simp only [Fin.init, w, Fin.val_castSucc]
    by_cases h : n + (i : ℕ) < m + 2
    · rw [circ_removeNth_ge _ _ _ (by simp only; rw [Nat.mod_eq_of_lt h]; omega)]
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
      omega
    · have h1 : (n + (i : ℕ)) % (m + 2) = n + i - (m + 2) := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [circ_removeNth_lt _ _ _ (by simp only; rw [h1]; omega)]
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, h1]
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  have hwl : w (Fin.last (m + 2)) = x i := by
    simp only [w, Fin.val_last]
    congr 1
    apply Fin.ext
    simp only
    rw [show m + 2 + ((i : ℕ) + 1) = (i : ℕ) + (m + 3) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  have hu' : u = w (Fin.last (m + 1)).castSucc ∨ u = w 0 := by
    rcases hu with h | h
    · left
      rw [h]
      simp only [w, Fin.val_castSucc, Fin.val_last]
      congr 3
      omega
    · right
      rw [h]
      simp only [w, Fin.val_zero]
      congr 3
      omega
  have h := circ_sAv_init_le P hin w hu'
  rwa [hwl, hw2, hw1] at h

end Remove

end BlockBand.Native.ErdosRiabov.Circ
