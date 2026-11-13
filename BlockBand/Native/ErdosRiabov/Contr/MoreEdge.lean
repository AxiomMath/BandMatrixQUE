module

public import BlockBand.Native.ErdosRiabov.Contr.MoreSplit

/-!
# Local contractions: the edge cases of the averaged insertion and concatenation

The averaged insertion and concatenation bounds in the edge cases `i = 0` and `j = 0`.
(U2)–(U7) denote the properties of the control `Υ` given by `LemmaK.ups_U2_U8_vs`.

The case `i, j ≥ 1` has four `q`-factors and is proved by (U6)/(U4). With `j = 0`
(`s^iso_1(q,q) = √Υ(q,q)`) or `i = 0` (`s^av_1 = 1/(ℓη)`) only two
`√Υ`-factors contain `q`; they are contracted by the second clause of (U4)
(`Σ_a √(Υ(x,a)Υ(a,y)) ≤ K √(ℓη Υ(x,y))`) or its first clause, and the remaining
`√Υ(q,q)`, and the `k = 1` target `s^av_1`, are handled by (U2) `Υ ≤ C₁/(ℓη)`, `C₁ ≥ 1`.
With `L = ℓη`:
* `i = 0`, `j ≥ 1`: `Σ_q s^av_1 s^iso_{j+1}(q,y,q) ≤ √C₁ K L^{-1/2} s^av_j(y)`;
  pointwise `≤ C₁ L^{-3/2} s^av_j(y)`;
* `i ≥ 1`, `j = 0`: `Σ_q s^av_{i+1}(x,q) s^iso_1(q,q) ≤ C₁ K L^{-1/2} s^av_i(x)`;
  pointwise `≤ C₁ √C₁ L^{-3/2} s^av_i(x)`.
VS forms take `hin : ContrVSInputs d P t`: `C₁ = C₁''`, `K = C₁''/η`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Contr

open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow

variable {N : ℕ}

/-!
## Scalar identities
-/

private theorem edge_sqrt_div {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L) :
    Real.sqrt (C / L) = Real.sqrt C * L ^ (-(1 / 2 : ℝ)) := by
  rw [div_eq_mul_inv, Real.sqrt_mul hC, Real.sqrt_inv, Real.sqrt_eq_rpow L,
    ← Real.rpow_neg hL.le]

private theorem edge_inv_sqrt {L : ℝ} (hL : 0 < L) :
    L⁻¹ * Real.sqrt L = L ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hL]
  norm_num

private theorem edge_half_half {L : ℝ} (hL : 0 < L) :
    L ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) = L⁻¹ := by
  rw [← Real.rpow_add hL, ← Real.rpow_neg_one]
  norm_num

private theorem edge_three_half {L : ℝ} (hL : 0 < L) :
    L⁻¹ * L ^ (-(1 / 2 : ℝ)) = L ^ (-(3 / 2 : ℝ)) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hL]
  norm_num

private theorem edge_sqrt_half {L : ℝ} (hL : 0 < L) :
    Real.sqrt L * L ^ (-(1 / 2 : ℝ)) = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL]
  norm_num

/-- `s^iso_1(q,q) = √Υ(q,q)`. -/
theorem contr_sIso_one (P : PsiData N) (q : Fin N) (y : Fin 1 → Fin N) (t : ℝ) :
    P.sIso q q y t = Real.sqrt (P.ups t q q) := by
  rw [contr_sIso_eq P]
  unfold contrPathProd
  rw [Finset.prod_range_one, contr_isoPoint_zero,
    contr_isoPoint_of_le (m := 0 + 1) q q y (by omega) (by omega)]
  norm_num

/-!
## Shapes
-/

section Shapes

variable (P : PsiData N) (t : ℝ)

/-- The averaged factor of the `j = 0` edge: `s^av_{i+1}(x,q) = c √(R · U(u,q)U(q,v))`, and
`c √(R · U(u,v)) ≤ √C₁ L^{-1/2} s^av_i(x)` (`i ≥ 1`). -/
theorem contrSplit_avEdgeJ0_shape (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    {C₁ : ℝ} (hC₁ : 1 ≤ C₁) (hmax : ∀ x y, P.ups t x y ≤ C₁ / P.lEta t)
    {i : ℕ} (hi : 1 ≤ i) (xq : Fin N → Fin (i + 1) → Fin N) (w : Fin i → Fin N)
    (hlast : ∀ q, xq q ⟨i, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < i), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩) :
    ∃ c R : ℝ, ∃ u v : Fin N, 0 ≤ c ∧ 0 ≤ R ∧
      (∀ q, P.sAv (xq q) t = c * Real.sqrt (R * (P.ups t u q * P.ups t q v))) ∧
      c * Real.sqrt (R * P.ups t u v) ≤
        Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨cw, hcw⟩ : ∃ cw, cw = contrCycPt w (w ⟨0, by omega⟩) := ⟨_, rfl⟩
  have hcw_lt : ∀ (n : ℕ) (hn : n < i + 1), cw n = w ⟨n, hn⟩ := fun n hn => by
    rw [hcw, contr_cycPt_lt _ _ hn]
  have hcw_end : cw (i + 1) = w ⟨0, by omega⟩ := by
    rw [hcw, contr_cycPt_ge _ _ le_rfl]
  set U := P.ups t
  obtain ⟨A, hAdef⟩ : ∃ A, A = contrPathProd U cw i := ⟨_, rfl⟩
  have hA : 0 ≤ A := hAdef ▸ contrPathProd_nonneg hU _ _
  have hav : ∀ q, contrPathProd U (contrCycPt (xq q) (xq q ⟨0, by omega⟩)) (i + 1 + 1) =
      A * (U (cw i) q * U q (w ⟨0, by omega⟩)) := by
    intro q
    have hpt : ∀ n ≤ i, contrCycPt (xq q) (xq q ⟨0, by omega⟩) n = cw n := by
      intro n hn
      rw [contr_cycPt_lt _ _ (by omega), hcw_lt n (by omega)]
      exact hxq q n (by omega)
    have h1 : contrCycPt (xq q) (xq q ⟨0, by omega⟩) (i + 1) = q := by
      rw [contr_cycPt_lt _ _ (by omega)]
      exact hlast q
    have h2 : contrCycPt (xq q) (xq q ⟨0, by omega⟩) (i + 1 + 1) = w ⟨0, by omega⟩ := by
      rw [contr_cycPt_ge _ _ le_rfl]
      exact hxq q 0 (by omega)
    rw [contrPathProd_succ, contrPathProd_succ, contrPathProd_congr U hpt, hpt i le_rfl, h1, h2,
      ← hAdef, mul_assoc]
  have hs : Real.sqrt (U (w ⟨0, by omega⟩) (w ⟨0, by omega⟩)) ≤
      Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) :=
    (Real.sqrt_le_sqrt (hmax _ _)).trans_eq (edge_sqrt_div (by linarith) hL)
  have hC0 : 1 ≤ Real.sqrt C₁ := Real.one_le_sqrt.mpr hC₁
  refine ⟨P.lEta t ^ (-(((i + 1 + 1 : ℕ) : ℝ)) / 2), A, cw i, w ⟨0, by omega⟩,
    Real.rpow_nonneg hL.le _, hA, fun q => ?_, ?_⟩
  · rw [contr_sAv_eq P (by omega) (xq q) t, hav q]
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      rw [contr_sAv_one P rfl]
      have hA1 : A = 1 := by rw [hAdef]; exact contrPathProd_zero _ _
      have hc : P.lEta t ^ (-(((0 + 1 + 1 : ℕ) : ℝ)) / 2) = (P.lEta t)⁻¹ := by
        rw [← Real.rpow_neg_one]
        congr 1
        norm_num
      rw [hA1, one_mul, hcw_lt 0 (by omega), hc]
      calc (P.lEta t)⁻¹ * Real.sqrt (U (w ⟨0, by omega⟩) (w ⟨0, by omega⟩))
          ≤ (P.lEta t)⁻¹ * (Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hL.le)
        _ = _ := by ring
    · rw [contr_sAv_eq P (by omega) w t, ← hcw, contrPathProd_succ, hcw_end, ← hAdef]
      have he : P.lEta t ^ (-(((i + 1 + 1 : ℕ) : ℝ)) / 2) =
          P.lEta t ^ (-(1 / 2 : ℝ)) * P.lEta t ^ (-(((i + 1 : ℕ) : ℝ)) / 2) := by
        rw [← Real.rpow_add hL]
        congr 1
        push_cast
        ring
      rw [he]
      have hX : 0 ≤ P.lEta t ^ (-(1 / 2 : ℝ)) * (P.lEta t ^ (-(((i + 1 : ℕ) : ℝ)) / 2) *
          Real.sqrt (A * U (cw i) (w ⟨0, by omega⟩))) := by positivity
      calc P.lEta t ^ (-(1 / 2 : ℝ)) * P.lEta t ^ (-(((i + 1 : ℕ) : ℝ)) / 2) *
            Real.sqrt (A * U (cw i) (w ⟨0, by omega⟩))
          = 1 * (P.lEta t ^ (-(1 / 2 : ℝ)) * (P.lEta t ^ (-(((i + 1 : ℕ) : ℝ)) / 2) *
            Real.sqrt (A * U (cw i) (w ⟨0, by omega⟩)))) := by ring
        _ ≤ Real.sqrt C₁ * (P.lEta t ^ (-(1 / 2 : ℝ)) *
            (P.lEta t ^ (-(((i + 1 : ℕ) : ℝ)) / 2) *
              Real.sqrt (A * U (cw i) (w ⟨0, by omega⟩)))) :=
            mul_le_mul_of_nonneg_right hC0 hX
        _ = _ := by ring

/-- The isotropic factor of the `i = 0` edge: `s^iso_{j+1}(q,y,q) = c √(R · U(u,q)U(q,v))`, and
`c √(R · U(u,v)) ≤ √C₁ s^av_j(y)` (`j ≥ 1`). -/
theorem contrSplit_avEdgeI0_shape (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    {C₁ : ℝ} (hC₁ : 1 ≤ C₁) (hmax : ∀ x y, P.ups t x y ≤ C₁ / P.lEta t)
    {j : ℕ} (hj : 1 ≤ j) (y : Fin (j + 1) → Fin N) (w : Fin j → Fin N)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨n, by omega⟩) :
    ∃ c R : ℝ, ∃ u v : Fin N, 0 ≤ c ∧ 0 ≤ R ∧
      (∀ q, P.sIso q q y t = c * Real.sqrt (R * (P.ups t u q * P.ups t q v))) ∧
      c * Real.sqrt (R * P.ups t u v) ≤ Real.sqrt C₁ * P.sAv w t := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨cw, hcw⟩ : ∃ cw, cw = contrCycPt w (w ⟨0, by omega⟩) := ⟨_, rfl⟩
  have hcw_lt : ∀ (n : ℕ) (hn : n < j + 1), cw n = w ⟨n, hn⟩ := fun n hn => by
    rw [hcw, contr_cycPt_lt _ _ hn]
  have hcw_end : cw (j + 1) = w ⟨0, by omega⟩ := by
    rw [hcw, contr_cycPt_ge _ _ le_rfl]
  set U := P.ups t
  obtain ⟨B, hBdef⟩ : ∃ B, B = contrPathProd U cw j := ⟨_, rfl⟩
  have hB : 0 ≤ B := hBdef ▸ contrPathProd_nonneg hU _ _
  have hiso : ∀ q, contrPathProd U (isoPoint q q y) (j + 1 + 1) =
      B * (U (cw j) q * U q (w ⟨0, by omega⟩)) := by
    intro q
    have hpt : ∀ n ≤ j, isoPoint q q y (n + 1) = cw n := by
      intro n hn
      rw [contr_isoPoint_succ _ _ _ (by omega), hcw_lt n (by omega)]
      exact hy n (by omega)
    rw [contrPathProd_succ', contrPathProd_succ U _ j, contr_isoPoint_zero,
      hpt 0 (Nat.zero_le _), hpt j le_rfl, contr_isoPoint_of_le _ _ _ (by omega) le_rfl,
      contrPathProd_congr U hpt, hcw_lt 0 (by omega), ← hBdef]
    ring
  have hC0 : 1 ≤ Real.sqrt C₁ := Real.one_le_sqrt.mpr hC₁
  refine ⟨P.lEta t ^ (-(((j + 1 + 1 : ℕ) : ℝ) - 1) / 2), B, cw j, w ⟨0, by omega⟩,
    Real.rpow_nonneg hL.le _, hB, fun q => ?_, ?_⟩
  · rw [contr_sIso_eq P, hiso q]
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      rw [contr_sAv_one P rfl]
      have hB1 : B = 1 := by rw [hBdef]; exact contrPathProd_zero _ _
      have hc : P.lEta t ^ (-(((0 + 1 + 1 : ℕ) : ℝ) - 1) / 2) = P.lEta t ^ (-(1 / 2 : ℝ)) := by
        congr 1
        norm_num
      have hs : Real.sqrt (U (w ⟨0, by omega⟩) (w ⟨0, by omega⟩)) ≤
          Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) :=
        (Real.sqrt_le_sqrt (hmax _ _)).trans_eq (edge_sqrt_div (by linarith) hL)
      rw [hB1, one_mul, hcw_lt 0 (by omega), hc]
      calc P.lEta t ^ (-(1 / 2 : ℝ)) * Real.sqrt (U (w ⟨0, by omega⟩) (w ⟨0, by omega⟩))
          ≤ P.lEta t ^ (-(1 / 2 : ℝ)) * (Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hL.le _)
        _ = Real.sqrt C₁ * (P.lEta t ^ (-(1 / 2 : ℝ)) * P.lEta t ^ (-(1 / 2 : ℝ))) := by ring
        _ = _ := by rw [edge_half_half hL]
    · rw [contr_sAv_eq P (by omega) w t, ← hcw, contrPathProd_succ, hcw_end, ← hBdef]
      have he : P.lEta t ^ (-(((j + 1 + 1 : ℕ) : ℝ) - 1) / 2) =
          P.lEta t ^ (-(((j + 1 : ℕ) : ℝ)) / 2) := by
        congr 1
        push_cast
        ring
      rw [he]
      have hX : 0 ≤ P.lEta t ^ (-(((j + 1 : ℕ) : ℝ)) / 2) *
          Real.sqrt (B * U (cw j) (w ⟨0, by omega⟩)) := by positivity
      calc P.lEta t ^ (-(((j + 1 : ℕ) : ℝ)) / 2) * Real.sqrt (B * U (cw j) (w ⟨0, by omega⟩))
          = 1 * (P.lEta t ^ (-(((j + 1 : ℕ) : ℝ)) / 2) *
            Real.sqrt (B * U (cw j) (w ⟨0, by omega⟩))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hC0 hX

end Shapes

/-!
## Abstract forms
-/

section Abstract

variable (P : PsiData N) (t : ℝ)

/-- **Averaged insertion, edge case `i = 0` (abstract form).** If `Υ = P.ups t ≥ 0`, `L = ℓη > 0`,
`Υ ≤ C₁/L` (U2) with `C₁ ≥ 1` and `Σ_a √(Υ(x,a)Υ(a,y)) ≤ K √(L Υ(x,y))`, `K ≥ 0` ((U4),
second clause),
then for `j ≥ 1`, any `xq q : Fin 1 → Fin N`, isotropic sites `y` (the first `j` entries of
`y : Fin (j+1)`) equal to `w : Fin j → Fin N`:
`Σ_q s^av_1(xq q) s^iso_{j+1}(q,y,q) ≤ √C₁ K L^{-1/2} s^av_j(w)`. -/
theorem avInsertionI0_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {C₁ K : ℝ}
    (hC₁ : 1 ≤ C₁) (hK : 0 ≤ K) (hmax : ∀ x y, P.ups t x y ≤ C₁ / P.lEta t)
    (hsc : ∀ x y, ∑ a, Real.sqrt (P.ups t x a * P.ups t a y) ≤
      K * Real.sqrt (P.lEta t * P.ups t x y))
    {j : ℕ} (hj : 1 ≤ j) (xq : Fin N → Fin 1 → Fin N) (y : Fin (j + 1) → Fin N)
    (w : Fin j → Fin N) (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨n, by omega⟩) :
    ∑ q, P.sAv (xq q) t * P.sIso q q y t ≤
      Real.sqrt C₁ * K * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t := by
  obtain ⟨c, R, u, v, hc, hR, hq, hw⟩ :=
    contrSplit_avEdgeI0_shape P t hU hL hC₁ hmax hj y w hy
  have h7 : ∀ x y, ∑ a, Real.sqrt (P.ups t x a * P.ups t a y) ≤
      K * Real.sqrt (P.lEta t) * Real.sqrt (P.ups t x y) := fun x y => by
    rw [mul_assoc, ← Real.sqrt_mul hL.le]
    exact hsc x y
  have hsum := localContraction_two_sum h7 hc hR u v
  have hK' : 0 ≤ K * Real.sqrt (P.lEta t) := mul_nonneg hK (Real.sqrt_nonneg _)
  simp_rw [contr_sAv_one P rfl, hq]
  rw [← Finset.mul_sum]
  calc (P.lEta t)⁻¹ * ∑ q, c * Real.sqrt (R * (P.ups t u q * P.ups t q v))
      ≤ (P.lEta t)⁻¹ * (K * Real.sqrt (P.lEta t) * (c * Real.sqrt (R * P.ups t u v))) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hL.le)
    _ ≤ (P.lEta t)⁻¹ * (K * Real.sqrt (P.lEta t) * (Real.sqrt C₁ * P.sAv w t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hK') (inv_nonneg.mpr hL.le)
    _ = Real.sqrt C₁ * K * ((P.lEta t)⁻¹ * Real.sqrt (P.lEta t)) * P.sAv w t := by ring
    _ = _ := by rw [edge_inv_sqrt hL]

/-- **Averaged concatenation, edge case `i = 0` (abstract form).** Under the hypotheses of
`avInsertionI0_of` with (U4) `Υ(x,a)Υ(a,y) ≤ C₁/L Υ(x,y)` in place of the √-convolution, for
every `q`: `s^av_1(xq q) s^iso_{j+1}(q,y,q) ≤ C₁ L^{-3/2} s^av_j(w)`. -/
theorem avConcatI0_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {C₁ : ℝ}
    (hC₁ : 1 ≤ C₁) (hmax : ∀ x y, P.ups t x y ≤ C₁ / P.lEta t)
    (htri : ∀ x a y, P.ups t x a * P.ups t a y ≤ C₁ / P.lEta t * P.ups t x y)
    {j : ℕ} (hj : 1 ≤ j) (xq : Fin N → Fin 1 → Fin N) (y : Fin (j + 1) → Fin N)
    (w : Fin j → Fin N) (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (q : Fin N) :
    P.sAv (xq q) t * P.sIso q q y t ≤ C₁ * P.lEta t ^ (-(3 / 2 : ℝ)) * P.sAv w t := by
  obtain ⟨c, R, u, v, hc, hR, hq, hw⟩ :=
    contrSplit_avEdgeI0_shape P t hU hL hC₁ hmax hj y w hy
  have hC0 : 0 ≤ C₁ := by linarith
  have hK : 0 ≤ C₁ / P.lEta t := div_nonneg hC0 hL.le
  have hmx := localContraction_two_max hK htri hc hR u v q
  rw [edge_sqrt_div hC0 hL] at hmx
  have hLi : 0 ≤ (P.lEta t)⁻¹ := inv_nonneg.mpr hL.le
  have hS : 0 ≤ Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hL.le _)
  rw [contr_sAv_one P rfl, hq]
  calc (P.lEta t)⁻¹ * (c * Real.sqrt (R * (P.ups t u q * P.ups t q v)))
      ≤ (P.lEta t)⁻¹ * (Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) *
          (c * Real.sqrt (R * P.ups t u v))) := mul_le_mul_of_nonneg_left hmx hLi
    _ ≤ (P.lEta t)⁻¹ * (Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) *
          (Real.sqrt C₁ * P.sAv w t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hS) hLi
    _ = (Real.sqrt C₁ * Real.sqrt C₁) * ((P.lEta t)⁻¹ * P.lEta t ^ (-(1 / 2 : ℝ))) *
          P.sAv w t := by ring
    _ = _ := by rw [Real.mul_self_sqrt hC0, edge_three_half hL]

/-- **Averaged insertion, edge case `j = 0` (abstract form).** If `Υ = P.ups t ≥ 0`, `L = ℓη > 0`,
`Υ ≤ C₁/L` (U2) with `C₁ ≥ 1` and `Σ_a √(Υ(x,a)Υ(a,y)) ≤ K √(L Υ(x,y))`, `K ≥ 0` ((U4),
second clause), then for `i ≥ 1`, averaged site vectors `xq q` (the `i` entries of
`w : Fin i → Fin N`, then `q`) and any `y : Fin 1 → Fin N`:
`Σ_q s^av_{i+1}(xq q) s^iso_1(q,q) ≤ C₁ K L^{-1/2} s^av_i(w)`. -/
theorem avInsertionJ0_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {C₁ K : ℝ}
    (hC₁ : 1 ≤ C₁) (hK : 0 ≤ K) (hmax : ∀ x y, P.ups t x y ≤ C₁ / P.lEta t)
    (hsc : ∀ x y, ∑ a, Real.sqrt (P.ups t x a * P.ups t a y) ≤
      K * Real.sqrt (P.lEta t * P.ups t x y))
    {i : ℕ} (hi : 1 ≤ i) (xq : Fin N → Fin (i + 1) → Fin N) (y : Fin 1 → Fin N)
    (w : Fin i → Fin N) (hlast : ∀ q, xq q ⟨i, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < i), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩) :
    ∑ q, P.sAv (xq q) t * P.sIso q q y t ≤
      C₁ * K * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t := by
  obtain ⟨c, R, u, v, hc, hR, hq, hw⟩ :=
    contrSplit_avEdgeJ0_shape P t hU hL hC₁ hmax hi xq w hlast hxq
  have hC0 : 0 ≤ C₁ := by linarith
  have h7 : ∀ x y, ∑ a, Real.sqrt (P.ups t x a * P.ups t a y) ≤
      K * Real.sqrt (P.lEta t) * Real.sqrt (P.ups t x y) := fun x y => by
    rw [mul_assoc, ← Real.sqrt_mul hL.le]
    exact hsc x y
  have hsum := localContraction_two_sum h7 hc hR u v
  have hS : 0 ≤ Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hL.le _)
  have hqq : ∀ q, Real.sqrt (P.ups t q q) ≤ Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) :=
    fun q => (Real.sqrt_le_sqrt (hmax q q)).trans_eq (edge_sqrt_div hC0 hL)
  have hterm : ∀ q, P.sAv (xq q) t * P.sIso q q y t ≤
      Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) *
        (c * Real.sqrt (R * (P.ups t u q * P.ups t q v))) := fun q => by
    rw [hq, contr_sIso_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (hqq q)
      (mul_nonneg hc (Real.sqrt_nonneg _))
  have hK' : 0 ≤ K * Real.sqrt (P.lEta t) := mul_nonneg hK (Real.sqrt_nonneg _)
  calc ∑ q, P.sAv (xq q) t * P.sIso q q y t
      ≤ ∑ q, Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) *
          (c * Real.sqrt (R * (P.ups t u q * P.ups t q v))) :=
        Finset.sum_le_sum fun q _ => hterm q
    _ = Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) *
          ∑ q, c * Real.sqrt (R * (P.ups t u q * P.ups t q v)) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) *
          (K * Real.sqrt (P.lEta t) * (c * Real.sqrt (R * P.ups t u v))) :=
        mul_le_mul_of_nonneg_left hsum hS
    _ ≤ Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) *
          (K * Real.sqrt (P.lEta t) *
            (Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hK') hS
    _ = (Real.sqrt C₁ * Real.sqrt C₁) * K *
          (Real.sqrt (P.lEta t) * P.lEta t ^ (-(1 / 2 : ℝ))) *
          P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t := by ring
    _ = _ := by rw [Real.mul_self_sqrt hC0, edge_sqrt_half hL, mul_one]

/-- **Averaged concatenation, edge case `j = 0` (abstract form).** Under the hypotheses of
`avInsertionJ0_of` with (U4) `Υ(x,a)Υ(a,y) ≤ C₁/L Υ(x,y)` in place of the √-convolution, for
every `q`: `s^av_{i+1}(xq q) s^iso_1(q,q) ≤ C₁ √C₁ L^{-3/2} s^av_i(w)`. -/
theorem avConcatJ0_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {C₁ : ℝ}
    (hC₁ : 1 ≤ C₁) (hmax : ∀ x y, P.ups t x y ≤ C₁ / P.lEta t)
    (htri : ∀ x a y, P.ups t x a * P.ups t a y ≤ C₁ / P.lEta t * P.ups t x y)
    {i : ℕ} (hi : 1 ≤ i) (xq : Fin N → Fin (i + 1) → Fin N) (y : Fin 1 → Fin N)
    (w : Fin i → Fin N) (hlast : ∀ q, xq q ⟨i, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < i), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (q : Fin N) :
    P.sAv (xq q) t * P.sIso q q y t ≤
      C₁ * Real.sqrt C₁ * P.lEta t ^ (-(3 / 2 : ℝ)) * P.sAv w t := by
  obtain ⟨c, R, u, v, hc, hR, hq, hw⟩ :=
    contrSplit_avEdgeJ0_shape P t hU hL hC₁ hmax hi xq w hlast hxq
  have hC0 : 0 ≤ C₁ := by linarith
  have hK : 0 ≤ C₁ / P.lEta t := div_nonneg hC0 hL.le
  have hmx := localContraction_two_max hK htri hc hR u v q
  rw [edge_sqrt_div hC0 hL] at hmx
  have hS : 0 ≤ Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hL.le _)
  have hqq : Real.sqrt (P.ups t q q) ≤ Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) :=
    (Real.sqrt_le_sqrt (hmax q q)).trans_eq (edge_sqrt_div hC0 hL)
  rw [hq, contr_sIso_one]
  calc c * Real.sqrt (R * (P.ups t u q * P.ups t q v)) * Real.sqrt (P.ups t q q)
      ≤ (Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) * (c * Real.sqrt (R * P.ups t u v))) *
          (Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul hmx hqq (Real.sqrt_nonneg _)
          (mul_nonneg hS (mul_nonneg hc (Real.sqrt_nonneg _)))
    _ ≤ (Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) *
          (Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t)) *
          (Real.sqrt C₁ * P.lEta t ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hS) hS
    _ = (Real.sqrt C₁ * Real.sqrt C₁) * Real.sqrt C₁ *
          ((P.lEta t ^ (-(1 / 2 : ℝ)) * P.lEta t ^ (-(1 / 2 : ℝ))) *
            P.lEta t ^ (-(1 / 2 : ℝ))) * P.sAv w t := by ring
    _ = _ := by rw [Real.mul_self_sqrt hC0, edge_half_half hL, edge_three_half hL]

end Abstract

/-!
## VS forms
-/

section VS

variable (d : VSData) (P : PsiData N) {t : ℝ}

/-- **Averaged insertion, edge case `i = 0`, along the VS flow.** With `hin : ContrVSInputs d P t`
and sites as in `avInsertionI0_of` (`j ≥ 1`): `Σ_q s^av_1(xq q) s^iso_{j+1}(q,y,q) ≤
√C₁'' · C₁''/η · (ℓη)^{-1/2} · s^av_j(w)`. -/
theorem avInsertionI0_vs (hin : ContrVSInputs d P t) {j : ℕ} (hj : 1 ≤ j)
    (xq : Fin N → Fin 1 → Fin N) (y : Fin (j + 1) → Fin N) (w : Fin j → Fin N)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨n, by omega⟩) :
    ∑ q, P.sAv (xq q) t * P.sIso q q y t ≤
      Real.sqrt d.C1pp * (d.C1pp / vsHeight P.z t) * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t :=
  avInsertionI0_of P t hin.nonneg hin.lEta_pos d.one_le_C1pp
    (div_nonneg (by linarith [d.one_le_C1pp]) hin.height_pos.le) hin.maxU hin.sqrtConvol hj
    xq y w hy

/-- **Averaged concatenation, edge case `i = 0`, along the VS flow.** With
`hin : ContrVSInputs d P t` and sites as in `avInsertionI0_of`, for every `q`:
`s^av_1(xq q) s^iso_{j+1}(q,y,q) ≤ C₁'' (ℓη)^{-3/2} s^av_j(w)`. -/
theorem avConcatI0_vs (hin : ContrVSInputs d P t) {j : ℕ} (hj : 1 ≤ j)
    (xq : Fin N → Fin 1 → Fin N) (y : Fin (j + 1) → Fin N) (w : Fin j → Fin N)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨n, by omega⟩) (q : Fin N) :
    P.sAv (xq q) t * P.sIso q q y t ≤ d.C1pp * P.lEta t ^ (-(3 / 2 : ℝ)) * P.sAv w t :=
  avConcatI0_of P t hin.nonneg hin.lEta_pos d.one_le_C1pp hin.maxU hin.triangle hj xq y w hy q

/-- **Averaged insertion, edge case `j = 0`, along the VS flow.** With `hin : ContrVSInputs d P t`
and sites as in `avInsertionJ0_of` (`i ≥ 1`): `Σ_q s^av_{i+1}(xq q) s^iso_1(q,q) ≤
C₁'' · C₁''/η · (ℓη)^{-1/2} · s^av_i(w)`. -/
theorem avInsertionJ0_vs (hin : ContrVSInputs d P t) {i : ℕ} (hi : 1 ≤ i)
    (xq : Fin N → Fin (i + 1) → Fin N) (y : Fin 1 → Fin N) (w : Fin i → Fin N)
    (hlast : ∀ q, xq q ⟨i, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < i), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩) :
    ∑ q, P.sAv (xq q) t * P.sIso q q y t ≤
      d.C1pp * (d.C1pp / vsHeight P.z t) * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t :=
  avInsertionJ0_of P t hin.nonneg hin.lEta_pos d.one_le_C1pp
    (div_nonneg (by linarith [d.one_le_C1pp]) hin.height_pos.le) hin.maxU hin.sqrtConvol hi
    xq y w hlast hxq

/-- **Averaged concatenation, edge case `j = 0`, along the VS flow.** With
`hin : ContrVSInputs d P t` and sites as in `avInsertionJ0_of`, for every `q`:
`s^av_{i+1}(xq q) s^iso_1(q,q) ≤ C₁'' √C₁'' (ℓη)^{-3/2} s^av_i(w)`. -/
theorem avConcatJ0_vs (hin : ContrVSInputs d P t) {i : ℕ} (hi : 1 ≤ i)
    (xq : Fin N → Fin (i + 1) → Fin N) (y : Fin 1 → Fin N) (w : Fin i → Fin N)
    (hlast : ∀ q, xq q ⟨i, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < i), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (q : Fin N) :
    P.sAv (xq q) t * P.sIso q q y t ≤
      d.C1pp * Real.sqrt d.C1pp * P.lEta t ^ (-(3 / 2 : ℝ)) * P.sAv w t :=
  avConcatJ0_of P t hin.nonneg hin.lEta_pos d.one_le_C1pp hin.maxU hin.triangle hi xq y w
    hlast hxq q

end VS

end BlockBand.Native.ErdosRiabov.Contr
