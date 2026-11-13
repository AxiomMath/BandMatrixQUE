module

public import BlockBand.Native.ErdosRiabov.Forcing.Index

/-!
# Forcing bounds: further contractions and the VS context

Contractions of size functions against the profile `S`, and the context `FCtx` of the forcing
bounds built from the VS data.

* `sRowSchwarz`: `Σ_a S_{xa} √(Υ(u,a)Υ(a,v)) ≤ C_S √(Υ(x,u)Υ(x,v))` (Cauchy–Schwarz with the
  weights `S_{x·}` and the profile bound `S Υ ≤ C_S Υ`);
* `sIso_split`, `sRowDiag`: `Σ_b S_{xb} s^iso_n(b,u,b) ≤ C_S s^iso_n(x,u,x)` (`n ≥ 2`);
* `sAv_diag`: `s^av_n(x', a) = (ℓη)^{-1/2} s^iso_n(a, x', a)` (`n ≥ 2`);
* `cutDiag`, `cutOff`: the two cut contractions for the longest F1 slot,
  derived from `isoConcat_of`, `isoConvol_of`, `sRowDiag` and `sAv_diag`;
* `fctx_of`: the context `FCtx d P t` from VS data, with `1 ≤ ℓη` as a hypothesis (it needs
  `W² ≥ N^{1+ζ₀}`, `Flow.vsScales`); `ℓη ≤ Nη` is `loc_le_N`; the kernel bound for every pattern
  (`aKer_norm_le`) is the kernel bound `|T̂| ≤ C_K Υ` plus `polynomialControl_mono`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Forcing

open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate

variable {N : ℕ}

section Contractions

variable {d : VSData} {P : PsiData N} {t : ℝ}

/-- **`S`-row Schwarz bound**. -/
theorem sRowSchwarz (c : FCtx d P t) (x u v : Fin N) :
    ∑ a, P.S x a * Real.sqrt (P.ups t u a * P.ups t a v) ≤
      constS d * Real.sqrt (P.ups t x u * P.ups t x v) := by
  have hS := c.stoch.nonneg
  have hU : ∀ a b, 0 ≤ P.ups t a b := fun a b => (c.pos a b).le
  have e : ∀ a, P.S x a * Real.sqrt (P.ups t u a * P.ups t a v) =
      Real.sqrt (P.S x a * P.ups t u a) * Real.sqrt (P.S x a * P.ups t a v) := by
    intro a
    rw [← Real.sqrt_mul (mul_nonneg (hS _ _) (hU _ _)),
      show P.S x a * P.ups t u a * (P.S x a * P.ups t a v) =
        P.S x a ^ 2 * (P.ups t u a * P.ups t a v) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hS _ _)]
  simp_rw [e]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  have h1 : ∑ a, Real.sqrt (P.S x a * P.ups t u a) ^ 2 ≤ constS d * P.ups t x u := by
    simp_rw [Real.sq_sqrt (mul_nonneg (hS _ _) (hU _ _))]
    calc ∑ a, P.S x a * P.ups t u a = ∑ a, P.S x a * P.ups t a u :=
          Finset.sum_congr rfl fun a _ => by rw [c.symm u a]
      _ ≤ _ := c.sUps x u
  have h2 : ∑ a, Real.sqrt (P.S x a * P.ups t a v) ^ 2 ≤ constS d * P.ups t x v := by
    simp_rw [Real.sq_sqrt (mul_nonneg (hS _ _) (hU _ _))]
    exact c.sUps x v
  have hC : 0 ≤ constS d := by unfold constS; positivity
  calc Real.sqrt (∑ a, Real.sqrt (P.S x a * P.ups t u a) ^ 2) *
        Real.sqrt (∑ a, Real.sqrt (P.S x a * P.ups t a v) ^ 2)
      ≤ Real.sqrt (constS d * P.ups t x u) * Real.sqrt (constS d * P.ups t x v) :=
        mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = constS d * Real.sqrt (P.ups t x u * P.ups t x v) := by
        rw [Real.sqrt_mul hC, Real.sqrt_mul hC, Real.sqrt_mul (hU _ _),
          show Real.sqrt (constS d) * Real.sqrt (P.ups t x u) *
              (Real.sqrt (constS d) * Real.sqrt (P.ups t x v)) =
            (Real.sqrt (constS d) * Real.sqrt (constS d)) *
              (Real.sqrt (P.ups t x u) * Real.sqrt (P.ups t x v)) by ring,
          Real.mul_self_sqrt hC]

/-- The isotropic size function with its two end edges split off (`n = m + 2`). -/
theorem sIso_split (P : PsiData N) (t : ℝ) {m : ℕ} (a b : Fin N) (u : Fin (m + 1 + 1) → Fin N) :
    P.sIso a b u t = P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) *
      Real.sqrt (P.ups t a (u ⟨0, by omega⟩) *
        (contrPathProd (P.ups t) (fun n => isoPoint a b u (n + 1)) m *
          P.ups t (u ⟨m, by omega⟩) b)) := by
  rw [contr_sIso_eq P, contrPathProd_succ', contrPathProd_succ, contr_isoPoint_zero,
    contr_isoPoint_succ _ _ _ (show 0 + 1 < m + 1 + 1 by omega),
    contr_isoPoint_succ _ _ _ (show m + 1 < m + 1 + 1 by omega),
    contr_isoPoint_of_le _ _ _ (show m + 1 + 1 ≠ 0 by omega) le_rfl]

theorem pathProd_indep (P : PsiData N) (t : ℝ) {m : ℕ} (a b a' b' : Fin N)
    (u : Fin (m + 1 + 1) → Fin N) :
    contrPathProd (P.ups t) (fun n => isoPoint a b u (n + 1)) m =
      contrPathProd (P.ups t) (fun n => isoPoint a' b' u (n + 1)) m := by
  refine contrPathProd_congr _ fun n hn => ?_
  rw [contr_isoPoint_succ _ _ _ (by omega), contr_isoPoint_succ _ _ _ (by omega)]

/-- `Σ_b S_{xb} s^iso_n(b,u,b) ≤ C_S s^iso_n(x,u,x)` for `n ≥ 2`. -/
theorem sRowDiag (c : FCtx d P t) {m : ℕ} (x : Fin N) (u : Fin (m + 1 + 1) → Fin N) :
    ∑ b, P.S x b * P.sIso b b u t ≤ constS d * P.sIso x x u t := by
  have hU : ∀ a b, 0 ≤ P.ups t a b := fun a b => (c.pos a b).le
  have hM : 0 ≤ contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m :=
    contrPathProd_nonneg hU _ _
  have he : 0 ≤ P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) :=
    Real.rpow_nonneg c.lEta_pos.le _
  have hb : ∀ b, P.S x b * P.sIso b b u t =
      P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) *
        Real.sqrt (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m) *
        (P.S x b * Real.sqrt (P.ups t (u ⟨m, by omega⟩) b * P.ups t b (u ⟨0, by omega⟩))) := by
    intro b
    rw [sIso_split P t b b u, pathProd_indep P t b b x x u,
      show P.ups t b (u ⟨0, by omega⟩) *
          (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m *
            P.ups t (u ⟨m, by omega⟩) b) =
        contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m *
          (P.ups t (u ⟨m, by omega⟩) b * P.ups t b (u ⟨0, by omega⟩)) by ring,
      Real.sqrt_mul hM]
    ring
  have hx : P.sIso x x u t = P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) *
      Real.sqrt (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m) *
      Real.sqrt (P.ups t x (u ⟨m, by omega⟩) * P.ups t x (u ⟨0, by omega⟩)) := by
    rw [sIso_split P t x x u, c.symm (u ⟨m, by omega⟩) x,
      show P.ups t x (u ⟨0, by omega⟩) *
          (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m *
            P.ups t x (u ⟨m, by omega⟩)) =
        contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m *
          (P.ups t x (u ⟨m, by omega⟩) * P.ups t x (u ⟨0, by omega⟩)) by ring,
      Real.sqrt_mul hM]
    ring
  rw [Finset.sum_congr rfl fun b _ => hb b, ← Finset.mul_sum, hx]
  calc P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) *
        Real.sqrt (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m) *
        ∑ b, P.S x b * Real.sqrt (P.ups t (u ⟨m, by omega⟩) b * P.ups t b (u ⟨0, by omega⟩))
      ≤ P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) *
        Real.sqrt (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m) *
        (constS d * Real.sqrt (P.ups t x (u ⟨m, by omega⟩) * P.ups t x (u ⟨0, by omega⟩))) :=
        mul_le_mul_of_nonneg_left (sRowSchwarz c x (u ⟨m, by omega⟩) (u ⟨0, by omega⟩))
          (mul_nonneg he (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- **Diagonal identity**: for `n = p + 1 ≥ 2`, sites `w` equal to `x` on the
first `p` entries and to `a` at the last one: `s^av_n(w) = (ℓη)^{-1/2} s^iso_n(a, x, a)`. -/
theorem sAv_diag (c : FCtx d P t) {p : ℕ} (hp : 1 ≤ p) (a : Fin N) (x w : Fin (p + 1) → Fin N)
    (hw : ∀ (n : ℕ) (hn : n < p), w ⟨n, by omega⟩ = x ⟨n, by omega⟩)
    (hwa : w ⟨p, by omega⟩ = a) :
    P.sAv w t = P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a a x t := by
  have hU : ∀ a b, 0 ≤ P.ups t a b := fun a b => (c.pos a b).le
  set U := P.ups t
  have hpt : ∀ n ≤ p, contrCycPt w (w ⟨0, by omega⟩) n = isoPoint a a x (n + 1) := by
    intro n hn
    rw [contr_cycPt_lt _ _ (by omega)]
    by_cases hnp : n < p
    · rw [contr_isoPoint_succ _ _ _ (by omega), hw n hnp]
    · have hnp' : n = p := by omega
      subst hnp'
      rw [contr_isoPoint_of_le _ _ _ (by omega) le_rfl, hwa]
  have hcyc : contrCycPt w (w ⟨0, by omega⟩) (p + 1) = isoPoint a a x 1 := by
    rw [contr_cycPt_ge _ _ le_rfl, contr_isoPoint_succ _ _ _ (by omega), hw 0 hp]
  have hp1 : contrCycPt w (w ⟨0, by omega⟩) p = a := by
    rw [hpt p le_rfl, contr_isoPoint_of_le _ _ _ (by omega) le_rfl]
  rw [contr_sAv_eq P (by omega) w t, contr_sIso_eq P, contrPathProd_succ U _ p,
    contrPathProd_succ' U (isoPoint a a x) p, contr_isoPoint_zero,
    contrPathProd_congr U hpt, hp1, hcyc]
  set A := contrPathProd U (fun n => isoPoint a a x (n + 1)) p
  have hA : 0 ≤ A := contrPathProd_nonneg hU _ _
  have hexp : P.lEta t ^ (-(((p + 1 : ℕ) : ℝ)) / 2) =
      P.lEta t ^ (-(1 / 2 : ℝ)) * P.lEta t ^ (-(((p + 1 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add c.lEta_pos]
    congr 1
    push_cast
    ring
  rw [hexp, mul_comm A]
  ring

/-- `sRowDiag` for any length `n ≥ 2`. -/
theorem sRowDiag' (c : FCtx d P t) {n : ℕ} (hn : 2 ≤ n) (x : Fin N) (u : Fin n → Fin N) :
    ∑ b, P.S x b * P.sIso b b u t ≤ constS d * P.sIso x x u t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  exact sRowDiag c x u

/-- **Cut, diagonal part**, in the order `B` then `A`:
`Σ_b S_{x*b} s^iso_{i+1}(b,y_A,b) s^iso_{j+1}(b,y_B,b) ≤ C_S √C₁'' (ℓη)^{-1/2} s^iso(x*,w,x*)`
with `w = (y_B, y_A)`. -/
theorem cutDiag (c : FCtx d P t) {i j : ℕ} (hn : 1 ≤ i + j) (xs : Fin N)
    (yA : Fin (i + 1) → Fin N) (yB : Fin (j + 1) → Fin N) (w : Fin (j + i + 1) → Fin N)
    (hwB : ∀ (n : ℕ) (hn : n < j), yB ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hwA : ∀ (n : ℕ) (hn : n < i), yA ⟨n, by omega⟩ = w ⟨j + n, by omega⟩) :
    ∑ b, P.S xs b * (P.sIso b b yA t * P.sIso b b yB t) ≤
      constS d * Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso xs xs w t := by
  have hU : ∀ a b, 0 ≤ P.ups t a b := fun a b => (c.pos a b).le
  have hK : 0 ≤ d.C1pp / P.lEta t := div_nonneg (by linarith [d.one_le_C1pp]) c.lEta_pos.le
  have hsq : Real.sqrt (d.C1pp / P.lEta t) = Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, Real.sqrt_mul (by linarith [d.one_le_C1pp]), Real.sqrt_inv,
      Real.sqrt_eq_rpow (P.lEta t), ← Real.rpow_neg c.lEta_pos.le]
  have hb : ∀ b, P.S xs b * (P.sIso b b yA t * P.sIso b b yB t) ≤
      Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) * (P.S xs b * P.sIso b b w t) := by
    intro b
    have h := isoConcat_of P t hU c.lEta_pos hK c.triangle b b yB yA w hwB hwA b
    rw [hsq] at h
    calc P.S xs b * (P.sIso b b yA t * P.sIso b b yB t)
        = P.S xs b * (P.sIso b b yB t * P.sIso b b yA t) := by ring
      _ ≤ P.S xs b * (Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso b b w t) :=
          mul_le_mul_of_nonneg_left h (c.stoch.nonneg _ _)
      _ = _ := by ring
  have hc0 : 0 ≤ Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg c.lEta_pos.le _)
  calc ∑ b, P.S xs b * (P.sIso b b yA t * P.sIso b b yB t)
      ≤ ∑ b, Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) * (P.S xs b * P.sIso b b w t) :=
        Finset.sum_le_sum fun b _ => hb b
    _ = Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) * ∑ b, P.S xs b * P.sIso b b w t := by
        rw [Finset.mul_sum]
    _ ≤ Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) * (constS d * P.sIso xs xs w t) :=
        mul_le_mul_of_nonneg_left (sRowDiag' c (by omega) xs w) hc0
    _ = _ := by ring

/-- **Cut, off-diagonal part**: with `w = (y_B, y_A)`,
`Σ_a S_{x*a} Σ_p s^iso(p,y_A,a) s^iso(a,y_B,p) ≤ C_S (C₁''/η) √(ℓη) s^iso(x*,w,x*)`. -/
theorem cutOff (c : FCtx d P t) {i j : ℕ} (hn : 1 ≤ i + j) (xs : Fin N)
    (yA : Fin (i + 1) → Fin N) (yB : Fin (j + 1) → Fin N) (w : Fin (j + i + 1) → Fin N)
    (hwB : ∀ (n : ℕ) (hn : n < j), yB ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hwA : ∀ (n : ℕ) (hn : n < i), yA ⟨n, by omega⟩ = w ⟨j + n, by omega⟩) :
    ∑ a, P.S xs a * ∑ p, P.sIso p a yA t * P.sIso a p yB t ≤
      constS d * (d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t)) * P.sIso xs xs w t := by
  have hU : ∀ a b, 0 ≤ P.ups t a b := fun a b => (c.pos a b).le
  have hK : 0 ≤ d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t) :=
    mul_nonneg (div_nonneg (by linarith [d.one_le_C1pp]) c.height_pos.le) (Real.sqrt_nonneg _)
  have h7 : ∀ x y, ∑ q, Real.sqrt (P.ups t x q * P.ups t q y) ≤
      d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t) * Real.sqrt (P.ups t x y) := fun x y => by
    rw [mul_assoc, ← Real.sqrt_mul c.lEta_pos.le]
    exact c.sqrtConvol x y
  have ha : ∀ a, P.S xs a * ∑ p, P.sIso p a yA t * P.sIso a p yB t ≤
      d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t) * (P.S xs a * P.sIso a a w t) := by
    intro a
    have h := isoConvol_of P t hU c.lEta_pos h7 a a yB yA w hwB hwA
    calc P.S xs a * ∑ p, P.sIso p a yA t * P.sIso a p yB t
        = P.S xs a * ∑ p, P.sIso a p yB t * P.sIso p a yA t := by
          congr 1
          exact Finset.sum_congr rfl fun p _ => mul_comm _ _
      _ ≤ P.S xs a * (d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t) * P.sIso a a w t) :=
          mul_le_mul_of_nonneg_left h (c.stoch.nonneg _ _)
      _ = _ := by ring
  calc ∑ a, P.S xs a * ∑ p, P.sIso p a yA t * P.sIso a p yB t
      ≤ ∑ a, d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t) * (P.S xs a * P.sIso a a w t) :=
        Finset.sum_le_sum fun a _ => ha a
    _ = d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t) * ∑ a, P.S xs a * P.sIso a a w t := by
        rw [Finset.mul_sum]
    _ ≤ d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t) * (constS d * P.sIso xs xs w t) :=
        mul_le_mul_of_nonneg_left (sRowDiag' c (by omega) xs w) hK
    _ = _ := by ring

end Contractions

/-!
## The VS context
-/

section VS

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 z) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
include hm hW hz ht0 ht1

/-- The kernel bound `|K| ≤ C_K Υ_t` for every pair of pattern values `m(z_t)`, `conj m(z_t)`,
at the height `η_t` (the `Ξ`-type cases via `polynomialControl_mono`). -/
theorem vsKernel_patConj_le (b b' : Bool) (a q : Fin (m * W)) :
    ‖vsKernel (shortRingProfile d.b m W) (VS.patConj b (semicircleM z))
        (VS.patConj b' (semicircleM z)) t a q‖ ≤
      Propagator.vsCK d * polynomialControl (m * W) W d.D (vsHeight z t) a q := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hD0 : 0 ≤ d.D := by linarith [d.D_ge_six]
  have hη := hz.im_pos hN
  have hS := shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (by omega : 3 ≤ m) hW
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hht := (Flow.vsFlow_b hN d.kappa_pos (by linarith [d.C0_ge_one]) hz).2.2.2.2.1 t ht0 ht1
  have hηt : 0 < vsHeight z t := hη.trans_le hht.1
  obtain ⟨h1, h2, -, -⟩ := Propagator.lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos
    d.kappa_pos d.C0_ge_one d.D_ge_six hm hW hz ht0 ht1
  have hmm : ∀ a q, ‖vsKernel (shortRingProfile d.b m W) (semicircleM z) (semicircleM z) t a q‖ ≤
      Propagator.vsCK d * polynomialControl (m * W) W d.D (vsHeight z t) a q := fun a q =>
    (h2 a q).trans (mul_le_mul_of_nonneg_left
      (polynomialControl_mono hN hW hD0 hηt hht.2 a q) (Propagator.vsCK_pos d).le)
  have hcomm : ∀ μ μ' : ℂ, vsKernel (shortRingProfile d.b m W) μ' μ t =
      vsKernel (shortRingProfile d.b m W) μ μ' t := fun μ μ' => by
    simp only [vsKernel, vsY, mul_comm μ' μ]
  cases b <;> cases b'
  · exact hmm a q
  · exact h1 a q
  · show ‖vsKernel (shortRingProfile d.b m W) (conj (semicircleM z)) (semicircleM z) t a q‖ ≤ _
    rw [hcomm]
    exact h1 a q
  · show ‖vsKernel (shortRingProfile d.b m W) (conj (semicircleM z)) (conj (semicircleM z))
      t a q‖ ≤ _
    rw [LemmaK.lemmaK_vsKernel_conj hS (norm_smul_lt_one hm1 hm1 ht0 ht1), Complex.norm_conj]
    exact hmm a q

/-- **Kernel bound**: `|Â_{j,t}(a,q)| ≤ C_K Υ_t(a,q)` for every pattern and slot. -/
theorem aKer_norm_le (P : PsiData (m * W)) (hPW : P.W = W) (hPD : P.D = d.D)
    (hPS : P.S = shortRingProfile d.b m W) (hPz : P.z = z) {k : ℕ} (σ : Fin k → Bool)
    (j : Fin k) (a q : Fin (m * W)) :
    ‖aKer P σ j t a q‖ ≤ Propagator.vsCK d * P.ups t a q := by
  have hnext : patM P.z σ (nextIdx j) = VS.patConj (σ (if h : (j : ℕ) + 1 < k then
      ⟨(j : ℕ) + 1, h⟩ else ⟨0, j.pos⟩)) (semicircleM P.z) := by
    unfold nextIdx
    split_ifs with h
    · exact patM_of_mem P.z σ ⟨(j : ℕ) + 1, h⟩
    · exact patM_of_mem P.z σ ⟨0, j.pos⟩
  rw [aKer, patM_of_mem, hnext, hPS, PsiData.ups, hPW, hPD, hPz]
  exact vsKernel_patConj_le d hm hW hz ht0 ht1 _ _ a q

/-- The context `FCtx d P t` from VS data (with `1 ≤ ℓη` as a
hypothesis). -/
theorem fctx_of (P : PsiData (m * W)) (hPW : P.W = W) (hPD : P.D = d.D)
    (hPS : P.S = shortRingProfile d.b m W) (hPz : P.z = z) (hL : 1 ≤ P.lEta t) :
    FCtx d P t := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hz' : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z := hPz ▸ hz
  have hin := contrVSInputs_of d hm hW P hPW hPD hz' ht0 ht1
  have hu : P.ups t = polynomialControl (m * W) W d.D (vsHeight P.z t) := by
    unfold PsiData.ups
    rw [hPW, hPD]
  have hD0 : 0 ≤ d.D := by linarith [d.D_ge_six]
  refine ⟨fun x y => ?_, hin.symm, hin.lEta_pos, hin.height_pos, hin.height_le, hL, ?_,
    hin.maxU, hin.triangle, hin.sqrtConvol, hin.schwarz, hin.sqrtConvolN, ?_, ?_,
    fun σ j a q => aKer_norm_le d hm hW hz ht0 ht1 P hPW hPD hPS hPz σ j a q,
    hz'.im_pos hN, ht0, ht1⟩
  · rw [hu]
    exact BlockBand.Adapters.ErdosRiabov.polynomialControl_pos hN hW _ hin.height_pos x y
  · unfold PsiData.lEta
    rw [hPW]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast
      BlockBand.Adapters.ErdosRiabov.loc_le_N _ _ _) hin.height_pos.le
  · rw [hPS]
    exact shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (by omega : 3 ≤ m) hW
  · intro x y
    have h := (LemmaK.lemmaK_K4_explicit d.b_pos d.b_lt_half hm hW d.C0_ge_one hD0
      hin.height_pos hin.height_le x y).2
    rw [Matrix.mul_apply] at h
    rw [hPS, hu]
    exact h

end VS

end BlockBand.Native.ErdosRiabov.Forcing
