module

public import BlockBand.Native.ErdosRiabov.Contr.Paths
public import BlockBand.Native.ErdosRiabov.LemmaK.Ups
public import BlockBand.Native.ErdosRiabov.LemmaK.PartA

/-!
# Local contractions of the size functions: the five instances

The isotropic convolution and concatenation, the averaged insertion and concatenation, and the
`S`-bound for the size functions. All five hold at a single time `t`, for `Psi.PsiData.sIso` and
`Psi.PsiData.sAv`
(`Υ = P.ups t`, `ℓη = P.lEta t`, `η = vsHeight P.z t`). Concatenations are given by hypotheses
on the site vectors (`hx`, `hy`, …), so any concrete concatenation (e.g. `Fin.append`) can be
used. Isotropic site vectors `x : Fin (i+1) → Fin N` carry `i` sites (`s^iso_{i+1}` ignores the
last entry). The items (U2)–(U7) are the properties of the control `Υ` in the control lemma
(`LemmaK.ups_U2_U8_vs`).

* Abstract form (`*_of`): for any `P`, `t` and any constants in the inputs (U2) max, (U4)
  triangle, (U5), (U6), (U7) and the profile bound `S Υ ≤ C_S Υ` with `S` symmetric.
* VS form (`*_vs`): for `P : PsiData (m W)` with `P.W = W`, `P.D = d.D`,
  `P.z ∈ BulkDomain (m W) d.δ₀ d.κ d.C₀`, `t ∈ [0,1]` (and `P.S = shortRingProfile d.b m W` for
  the `S`-bound), with the inputs supplied by `LemmaK.ups_U2_U8_vs` at `s = t` and
  `LemmaK.lemmaK_K4_explicit`. The constants are explicit in `VSData`:
  - isotropic convolution:
    `Σ_q s^iso_{i+1}(a,x,q) s^iso_{j+1}(q,y,b) ≤ C₁''/η · √(Nη) · s^iso_{i+j+1}`;
  - isotropic concatenation:
    `s^iso_{i+1}(a,x,q) s^iso_{j+1}(q,y,b) ≤ √C₁'' (ℓη)^{-1/2} s^iso_{i+j+1}`;
  - averaged insertion (`i, j ≥ 1`):
    `Σ_q s^av_{i+1}(x,q) s^iso_{j+1}(q,y,q) ≤ C_wc/η · (ℓη)^{-1/2} s^av_{i+j}(x,y)`;
  - averaged concatenation (`i, j ≥ 1`):
    `s^av_{i+1}(x,q) s^iso_{j+1}(q,y,q) ≤ C₁'' (ℓη)^{-3/2} s^av_{i+j}`;
  - the `S`-bound (`k ≥ 1`): `Σ_{q',q} S_{q'q} s^iso_{k+1}(q',x,q)² ≤ (1+2√(C₀+1))^D C_wc C₁''/η ·
    s^av_k(x)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Contr

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Internal.Contracts.Inputs (polynomialControl shortRingProfile)
open BlockBand.Adapters.ErdosRiabov (polynomialControl_pos shortRingProfile_symm)

variable {N : ℕ}

/-!
## Decompositions of the path products
-/

section Decomp

variable (U : Matrix (Fin N) (Fin N) ℝ)

private theorem contr_iso_left {i j : ℕ} (a b q : Fin N) (x : Fin (i + 1) → Fin N)
    (w : Fin (i + j + 1) → Fin N)
    (hx : ∀ (n : ℕ) (hn : n < i), x ⟨n, by omega⟩ = w ⟨n, by omega⟩) :
    contrPathProd U (isoPoint a q x) (i + 1) =
      contrPathProd U (isoPoint a b w) i * U (isoPoint a b w i) q := by
  have hpt : ∀ n ≤ i, isoPoint a q x n = isoPoint a b w n := by
    intro n hn
    rcases n with _ | n
    · rw [contr_isoPoint_zero, contr_isoPoint_zero]
    · rw [contr_isoPoint_succ _ _ _ (by omega), contr_isoPoint_succ _ _ _ (by omega)]
      exact hx n (by omega)
  rw [contrPathProd_succ, contrPathProd_congr U hpt, hpt i le_rfl,
    contr_isoPoint_of_le _ _ _ (by omega) le_rfl]

private theorem contr_iso_right {i j : ℕ} (a b q : Fin N) (y : Fin (j + 1) → Fin N)
    (w : Fin (i + j + 1) → Fin N)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) :
    contrPathProd U (isoPoint q b y) (j + 1) =
      U q (isoPoint a b w (i + 1)) * contrPathProd U (fun n => isoPoint a b w (i + 1 + n)) j := by
  have hpt : ∀ n ≤ j, isoPoint q b y (n + 1) = isoPoint a b w (i + 1 + n) := by
    intro n hn
    rw [show i + 1 + n = (i + n) + 1 by omega]
    rcases Nat.lt_or_ge n j with h | h
    · rw [contr_isoPoint_succ _ _ _ (by omega), contr_isoPoint_succ _ _ _ (by omega)]
      exact hy n h
    · rw [contr_isoPoint_of_le _ _ _ (by omega) (by omega),
        contr_isoPoint_of_le _ _ _ (by omega) (by omega)]
  rw [contrPathProd_succ', contr_isoPoint_zero, hpt 0 (Nat.zero_le _),
    contrPathProd_congr U hpt]

private theorem contr_iso_join {i j : ℕ} (a b : Fin N) (w : Fin (i + j + 1) → Fin N) :
    contrPathProd U (isoPoint a b w) (i + j + 1) =
      contrPathProd U (isoPoint a b w) i * U (isoPoint a b w i) (isoPoint a b w (i + 1)) *
        contrPathProd U (fun n => isoPoint a b w (i + 1 + n)) j := by
  have h := contrPathProd_add U (isoPoint a b w) (i + 1) j
  rw [show i + 1 + j = i + j + 1 by omega, contrPathProd_succ U _ i] at h
  exact h

end Decomp

/-!
## The abstract instances
-/

section Abstract

variable (P : PsiData N) (t : ℝ)

/-- The isotropic join: both sides of the isotropic convolution and concatenation in the form
`c √(R · U(u,q)U(q,v))` and `c √(R · U(u,v))`. -/
private theorem contr_iso_shape (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {i j : ℕ}
    (a b : Fin N) (x : Fin (i + 1) → Fin N) (y : Fin (j + 1) → Fin N)
    (w : Fin (i + j + 1) → Fin N)
    (hx : ∀ (n : ℕ) (hn : n < i), x ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) :
    ∃ c R : ℝ, ∃ u v : Fin N, 0 ≤ c ∧ 0 ≤ R ∧
      (∀ q, P.sIso a q x t * P.sIso q b y t =
        c * Real.sqrt (R * (P.ups t u q * P.ups t q v))) ∧
      P.sIso a b w t = c * Real.sqrt (R * P.ups t u v) := by
  set U := P.ups t
  set p := isoPoint a b w
  set A := contrPathProd U p i
  set B := contrPathProd U (fun n => p (i + 1 + n)) j
  have hA : 0 ≤ A := contrPathProd_nonneg hU _ _
  have hB : 0 ≤ B := contrPathProd_nonneg hU _ _
  set e₁ : ℝ := -(((i + 1 : ℕ) : ℝ) - 1) / 2
  set e₂ : ℝ := -(((j + 1 : ℕ) : ℝ) - 1) / 2
  refine ⟨P.lEta t ^ e₁ * P.lEta t ^ e₂, A * B, p i, p (i + 1),
    mul_nonneg (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hL.le _), mul_nonneg hA hB,
    fun q => ?_, ?_⟩
  · rw [contr_sIso_eq P, contr_sIso_eq P, contr_iso_left U a b q x w hx,
      contr_iso_right U a b q y w hy]
    have hAq : 0 ≤ A * U (p i) q := mul_nonneg hA (hU _ _)
    calc P.lEta t ^ e₁ * Real.sqrt (A * U (p i) q) *
          (P.lEta t ^ e₂ * Real.sqrt (U q (p (i + 1)) * B))
        = P.lEta t ^ e₁ * P.lEta t ^ e₂ *
            (Real.sqrt (A * U (p i) q) * Real.sqrt (U q (p (i + 1)) * B)) := by ring
      _ = P.lEta t ^ e₁ * P.lEta t ^ e₂ *
            Real.sqrt (A * B * (U (p i) q * U q (p (i + 1)))) := by
          rw [← Real.sqrt_mul hAq]
          congr 2
          ring
  · rw [contr_sIso_eq P, contr_iso_join U a b w, ← Real.rpow_add hL]
    congr 1
    · congr 1
      simp only [e₁, e₂]
      push_cast
      ring
    · congr 1
      ring

/-- **Isotropic convolution (abstract form).** If `Υ = P.ups t ≥ 0`, `ℓη > 0` and
`Σ_q √(Υ(x,q)Υ(q,y)) ≤ K √Υ(x,y)` (U7), then for sites `x` (`i` entries), `y` (`j` entries) and
any `w` whose first `i` entries are `x` and next `j` entries are `y`:
`Σ_q s^iso_{i+1}(a,x,q) s^iso_{j+1}(q,y,b) ≤ K s^iso_{i+j+1}(a,w,b)`. -/
theorem isoConvol_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {K : ℝ}
    (h7 : ∀ x y, ∑ q, Real.sqrt (P.ups t x q * P.ups t q y) ≤ K * Real.sqrt (P.ups t x y))
    {i j : ℕ} (a b : Fin N) (x : Fin (i + 1) → Fin N) (y : Fin (j + 1) → Fin N)
    (w : Fin (i + j + 1) → Fin N)
    (hx : ∀ (n : ℕ) (hn : n < i), x ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) :
    ∑ q, P.sIso a q x t * P.sIso q b y t ≤ K * P.sIso a b w t := by
  obtain ⟨c, R, u, v, hc, hR, hq, hw⟩ := contr_iso_shape P t hU hL a b x y w hx hy
  simp_rw [hq]
  rw [hw]
  exact localContraction_two_sum h7 hc hR u v

/-- **Isotropic concatenation (abstract form).** If `Υ = P.ups t ≥ 0`, `ℓη > 0` and
`Υ(x,a)Υ(a,y) ≤ K Υ(x,y)` (U4), `K ≥ 0`, then, with `x, y, w` as in `isoConvol_of`, for every
`q`: `s^iso_{i+1}(a,x,q) s^iso_{j+1}(q,y,b) ≤ √K s^iso_{i+j+1}(a,w,b)`. -/
theorem isoConcat_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {K : ℝ} (hK : 0 ≤ K)
    (h4 : ∀ x a y, P.ups t x a * P.ups t a y ≤ K * P.ups t x y)
    {i j : ℕ} (a b : Fin N) (x : Fin (i + 1) → Fin N) (y : Fin (j + 1) → Fin N)
    (w : Fin (i + j + 1) → Fin N)
    (hx : ∀ (n : ℕ) (hn : n < i), x ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) (q : Fin N) :
    P.sIso a q x t * P.sIso q b y t ≤ Real.sqrt K * P.sIso a b w t := by
  obtain ⟨c, R, u, v, hc, hR, hq, hw⟩ := contr_iso_shape P t hU hL a b x y w hx hy
  rw [hq, hw]
  exact localContraction_two_max hK h4 hc hR u v q

/-- The averaged join: both sides of the averaged insertion and concatenation in the form
`c √(R · U(x₁,q)U(x₂,q)U(q,y₁)U(q,y₂))` and `(ℓη)^{-1/2} s^av = c √(R · U(x₁,y₁)U(x₂,y₂))`. -/
private theorem contr_av_shape (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {i j : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j) (xq : Fin N → Fin (i + 1) → Fin N) (y : Fin (j + 1) → Fin N)
    (w : Fin (i + j) → Fin N) (hlast : ∀ q, xq q ⟨i, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < i), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) :
    ∃ c R : ℝ, ∃ x₁ x₂ y₁ y₂ : Fin N, 0 ≤ c ∧ 0 ≤ R ∧
      (∀ q, P.sAv (xq q) t * P.sIso q q y t =
        c * Real.sqrt (R * (P.ups t x₁ q * P.ups t x₂ q * P.ups t q y₁ * P.ups t q y₂))) ∧
      P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t =
        c * Real.sqrt (R * (P.ups t x₁ y₁ * P.ups t x₂ y₂)) := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨cw, hcw⟩ : ∃ cw, cw = contrCycPt w (w ⟨0, by omega⟩) := ⟨_, rfl⟩
  have hcw_lt : ∀ (n : ℕ) (hn : n < i + 1 + (j + 1)), cw n = w ⟨n, hn⟩ := fun n hn => by
    rw [hcw, contr_cycPt_lt _ _ hn]
  have hcw_end : cw (i + 1 + (j + 1)) = w ⟨0, by omega⟩ := by
    rw [hcw, contr_cycPt_ge _ _ le_rfl]
  set U := P.ups t
  set A := contrPathProd U cw i
  set B := contrPathProd U (fun n => cw (i + 1 + n)) j
  have hA : 0 ≤ A := contrPathProd_nonneg hU _ _
  have hB : 0 ≤ B := contrPathProd_nonneg hU _ _
  -- the averaged factor
  have hav : ∀ q, contrPathProd U (contrCycPt (xq q) (xq q ⟨0, by omega⟩)) (i + 1 + 1) =
      A * U (cw i) q * U q (w ⟨0, by omega⟩) := by
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
    rw [contrPathProd_succ, contrPathProd_succ, contrPathProd_congr U hpt, hpt i le_rfl, h1, h2]
  -- the isotropic factor
  have hiso : ∀ q, contrPathProd U (isoPoint q q y) (j + 1 + 1) =
      U q (cw (i + 1)) * (B * U (cw (i + 1 + j)) q) := by
    intro q
    have hpt : ∀ n ≤ j, isoPoint q q y (n + 1) = cw (i + 1 + n) := by
      intro n hn
      rw [contr_isoPoint_succ _ _ _ (by omega), hcw_lt _ (by omega)]
      exact hy n (by omega)
    rw [contrPathProd_succ', contrPathProd_succ U _ j, contr_isoPoint_zero, hpt 0 (Nat.zero_le _),
      hpt j le_rfl, contr_isoPoint_of_le _ _ _ (by omega) le_rfl, contrPathProd_congr U hpt]
  -- the target
  have htgt : contrPathProd U cw (i + 1 + (j + 1)) =
      A * U (cw i) (cw (i + 1)) * (B * U (cw (i + 1 + j)) (w ⟨0, by omega⟩)) := by
    rw [contrPathProd_add, contrPathProd_succ U _ i, contrPathProd_succ U _ j]
    simp only [hcw_end, A, B]
  set ea : ℝ := -(((i + 1 + 1 : ℕ) : ℝ)) / 2
  set ei : ℝ := -(((j + 1 + 1 : ℕ) : ℝ) - 1) / 2
  set ew : ℝ := -(((i + 1 + (j + 1) : ℕ) : ℝ)) / 2
  have hexp : P.lEta t ^ ea * P.lEta t ^ ei = P.lEta t ^ (-(1 / 2 : ℝ)) * P.lEta t ^ ew := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL]
    congr 1
    simp only [ea, ei, ew]
    push_cast
    ring
  refine ⟨P.lEta t ^ ea * P.lEta t ^ ei, A * B, cw i, cw (i + 1 + j), cw (i + 1),
    w ⟨0, by omega⟩, mul_nonneg (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hL.le _),
    mul_nonneg hA hB, fun q => ?_, ?_⟩
  · rw [contr_sAv_eq P (by omega) (xq q) t, contr_sIso_eq P, hav q, hiso q]
    have hAq : 0 ≤ A * U (cw i) q * U q (w ⟨0, by omega⟩) :=
      mul_nonneg (mul_nonneg hA (hU _ _)) (hU _ _)
    calc P.lEta t ^ ea * Real.sqrt (A * U (cw i) q * U q (w ⟨0, by omega⟩)) *
          (P.lEta t ^ ei * Real.sqrt (U q (cw (i + 1)) * (B * U (cw (i + 1 + j)) q)))
        = P.lEta t ^ ea * P.lEta t ^ ei *
            (Real.sqrt (A * U (cw i) q * U q (w ⟨0, by omega⟩)) *
              Real.sqrt (U q (cw (i + 1)) * (B * U (cw (i + 1 + j)) q))) := by ring
      _ = _ := by
          rw [← Real.sqrt_mul hAq]
          congr 2
          ring
  · rw [contr_sAv_eq P (by omega) w t, ← hcw, htgt, hexp]
    have e : A * U (cw i) (cw (i + 1)) * (B * U (cw (i + 1 + j)) (w ⟨0, by omega⟩)) =
        A * B * (U (cw i) (cw (i + 1)) * U (cw (i + 1 + j)) (w ⟨0, by omega⟩)) := by ring
    rw [e]
    ring

/-- **Averaged insertion (abstract form).** If `Υ = P.ups t ≥ 0`, `ℓη > 0` and the Schwarz
convolution (U6) `Σ_q √(Υ(x₁,q)Υ(x₂,q)Υ(q,y₁)Υ(q,y₂)) ≤ K √(Υ(x₁,y₁)Υ(x₂,y₂))` holds, then for
`i, j ≥ 1`, sites `w : Fin (i+j) → Fin N`, averaged site vectors `xq q` (`i+1` entries: the first
`i` entries of `w`, then `q`) and isotropic sites `y` (`j` entries: the last `j` entries of `w`):
`Σ_q s^av_{i+1}(x,q) s^iso_{j+1}(q,y,q) ≤ K (ℓη)^{-1/2} s^av_{i+j}(w)`. -/
theorem avInsertion_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {K : ℝ}
    (h6 : ∀ x₁ x₂ y₁ y₂, ∑ q, Real.sqrt (P.ups t x₁ q * P.ups t x₂ q * P.ups t q y₁ *
      P.ups t q y₂) ≤ K * Real.sqrt (P.ups t x₁ y₁ * P.ups t x₂ y₂))
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (xq : Fin N → Fin (i + 1) → Fin N)
    (y : Fin (j + 1) → Fin N) (w : Fin (i + j) → Fin N) (hlast : ∀ q, xq q ⟨i, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < i), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) :
    ∑ q, P.sAv (xq q) t * P.sIso q q y t ≤ K * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t := by
  obtain ⟨c, R, x₁, x₂, y₁, y₂, hc, hR, hq, hw⟩ :=
    contr_av_shape P t hU hL hi hj xq y w hlast hxq hy
  simp_rw [hq]
  rw [mul_assoc K, hw]
  exact localContraction_sum h6 hc hR x₁ x₂ y₁ y₂

/-- **Averaged concatenation (abstract form).** If `Υ = P.ups t ≥ 0`, `ℓη > 0` and
`Υ(x,a)Υ(a,y) ≤ K Υ(x,y)` (U4), `K ≥ 0`, then, with `xq, y, w` as in `avInsertion_of`, for
every `q`: `s^av_{i+1}(x,q) s^iso_{j+1}(q,y,q) ≤ K (ℓη)^{-1/2} s^av_{i+j}(w)`. -/
theorem avConcat_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {K : ℝ} (hK : 0 ≤ K)
    (h4 : ∀ x a y, P.ups t x a * P.ups t a y ≤ K * P.ups t x y)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (xq : Fin N → Fin (i + 1) → Fin N)
    (y : Fin (j + 1) → Fin N) (w : Fin (i + j) → Fin N) (hlast : ∀ q, xq q ⟨i, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < i), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) (q : Fin N) :
    P.sAv (xq q) t * P.sIso q q y t ≤ K * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t := by
  obtain ⟨c, R, x₁, x₂, y₁, y₂, hc, hR, hq, hw⟩ :=
    contr_av_shape P t hU hL hi hj xq y w hlast hxq hy
  rw [hq, mul_assoc K, hw]
  exact localContraction_max hU hK h4 hc hR x₁ x₂ y₁ y₂ q

/-- **Isotropic `S`-bound (abstract form).** If `Υ = P.ups t ≥ 0`, `ℓη > 0`, `S = P.S` is symmetric
with `Σ_a S(x,a)Υ(a,y) ≤ C_S Υ(x,y)` (K4), `Σ_a Υ(x,a)Υ(a,y) ≤ K Υ(x,y)` (U5), `Υ ≤ C₂/(ℓη)` (U2),
`C_S, K ≥ 0`, `C₂ ≥ 1`, then for `k ≥ 1`, sites `w : Fin k → Fin N` and isotropic sites `x`
(`k` entries, equal to `w`): `Σ_{q'} Σ_q S(q',q) s^iso_{k+1}(q',x,q)² ≤ C_S K C₂ s^av_k(w)²`. -/
theorem isoS_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {CS K C₂ : ℝ}
    (hCS : 0 ≤ CS) (hK : 0 ≤ K) (hC₂ : 1 ≤ C₂) (hSsym : ∀ x y, P.S x y = P.S y x)
    (hSU : ∀ x y, ∑ a, P.S x a * P.ups t a y ≤ CS * P.ups t x y)
    (h5 : ∀ x y, ∑ a, P.ups t x a * P.ups t a y ≤ K * P.ups t x y)
    (hU2 : ∀ x y, P.ups t x y ≤ C₂ / P.lEta t) {k : ℕ} (hk : 1 ≤ k)
    (x : Fin (k + 1) → Fin N) (w : Fin k → Fin N)
    (hx : ∀ (n : ℕ) (hn : n < k), x ⟨n, by omega⟩ = w ⟨n, by omega⟩) :
    ∑ q', ∑ q, P.S q' q * P.sIso q' q x t ^ 2 ≤ CS * K * C₂ * P.sAv w t ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨cw, hcw⟩ : ∃ cw, cw = contrCycPt w (w ⟨0, by omega⟩) := ⟨_, rfl⟩
  have hcw_lt : ∀ (n : ℕ) (hn : n < k + 1), cw n = w ⟨n, hn⟩ := fun n hn => by
    rw [hcw, contr_cycPt_lt _ _ hn]
  have hcw_end : cw (k + 1) = w ⟨0, by omega⟩ := by
    rw [hcw, contr_cycPt_ge _ _ le_rfl]
  set U := P.ups t
  set R := contrPathProd U cw k
  have hR : 0 ≤ R := contrPathProd_nonneg hU _ _
  set e : ℝ := -(((k + 1 + 1 : ℕ) : ℝ) - 1) / 2
  have hdec : ∀ q' q, contrPathProd U (isoPoint q' q x) (k + 1 + 1) =
      U q' (w ⟨0, by omega⟩) * R * U (cw k) q := by
    intro q' q
    have hpt : ∀ n ≤ k, isoPoint q' q x (n + 1) = cw n := by
      intro n hn
      rw [contr_isoPoint_succ _ _ _ (by omega), hcw_lt n (by omega)]
      exact hx n (by omega)
    rw [contrPathProd_succ', contrPathProd_succ U _ k, contr_isoPoint_zero,
      hpt 0 (Nat.zero_le _), hpt k le_rfl, contr_isoPoint_of_le _ _ _ (by omega) le_rfl,
      contrPathProd_congr U hpt, hcw_lt 0 (by omega)]
    ring
  have hsq : ∀ q' q, P.sIso q' q x t ^ 2 =
      (P.lEta t ^ e) ^ 2 * (U q' (w ⟨0, by omega⟩) * R * U (cw k) q) := by
    intro q' q
    rw [contr_sIso_eq P, mul_pow, Real.sq_sqrt (contrPathProd_nonneg hU _ _), hdec]
  simp_rw [hsq]
  refine (localContraction_profile hU hSsym hCS hSU h5 (sq_nonneg _) hR _ _).trans ?_
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    rw [contr_sAv_one P rfl]
    have hR1 : R = 1 := contrPathProd_zero _ _
    have hc : (P.lEta t ^ e) ^ 2 = (P.lEta t)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le,
        show e * ((2 : ℕ) : ℝ) = -1 by simp only [e]; push_cast; ring, Real.rpow_neg_one]
    rw [hR1, hc, hcw_lt 0 (by omega)]
    have h2 := hU2 (w ⟨0, by omega⟩) (w ⟨0, by omega⟩)
    have hLi : 0 ≤ (P.lEta t)⁻¹ := inv_nonneg.mpr hL.le
    calc CS * K * ((P.lEta t)⁻¹ * 1 * U (w ⟨0, by omega⟩) (w ⟨0, by omega⟩))
        ≤ CS * K * ((P.lEta t)⁻¹ * 1 * (C₂ / P.lEta t)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCS hK)
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = CS * K * C₂ * ((P.lEta t)⁻¹ ^ 2) := by ring
  · rw [contr_sAv_eq P (by omega) w t, ← hcw, mul_pow,
      Real.sq_sqrt (contrPathProd_nonneg hU _ _), contrPathProd_succ, hcw_end]
    have he : P.lEta t ^ e = P.lEta t ^ (-((k + 1 : ℕ) : ℝ) / 2) := by
      congr 1
      simp only [e]
      push_cast
      ring
    rw [he]
    have hX : 0 ≤ CS * K * ((P.lEta t ^ (-((k + 1 : ℕ) : ℝ) / 2)) ^ 2 *
        (R * U (cw k) (w ⟨0, by omega⟩))) :=
      mul_nonneg (mul_nonneg hCS hK) (mul_nonneg (sq_nonneg _) (mul_nonneg hR (hU _ _)))
    calc CS * K * ((P.lEta t ^ (-((k + 1 : ℕ) : ℝ) / 2)) ^ 2 * R * U (cw k) (w ⟨0, by omega⟩))
        = 1 * (CS * K * ((P.lEta t ^ (-((k + 1 : ℕ) : ℝ) / 2)) ^ 2 *
            (R * U (cw k) (w ⟨0, by omega⟩)))) := by ring
      _ ≤ C₂ * (CS * K * ((P.lEta t ^ (-((k + 1 : ℕ) : ℝ) / 2)) ^ 2 *
            (R * U (cw k) (w ⟨0, by omega⟩)))) := mul_le_mul_of_nonneg_right hC₂ hX
      _ = _ := by ring

end Abstract

/-!
## The VS instances
-/

section VS

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W))
  (hPW : P.W = W) (hPD : P.D = d.D) (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
  {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)

include hm hW hPW hPD hz ht0 ht1

/-- The inputs (U2) max, (U4) triangle, (U5), (U6), (U7) at the single time `t`
(`LemmaK.ups_U2_U8_vs` with `s = t`), with positivity and `η_t ≤ C₀+1`. -/
private theorem contr_vs_inputs :
    (∀ x y, 0 ≤ P.ups t x y) ∧ 0 < P.lEta t ∧ 0 < vsHeight P.z t ∧
      vsHeight P.z t ≤ d.C0 + 1 ∧
      (∀ x y, P.ups t x y ≤ d.C1pp / P.lEta t) ∧
      (∀ x a y, P.ups t x a * P.ups t a y ≤ d.C1pp / P.lEta t * P.ups t x y) ∧
      (∀ x y, ∑ a, P.ups t x a * P.ups t a y ≤ d.Cwc / vsHeight P.z t * P.ups t x y) ∧
      (∀ x₁ x₂ y₁ y₂, ∑ q, Real.sqrt (P.ups t x₁ q * P.ups t x₂ q * P.ups t q y₁ *
        P.ups t q y₂) ≤ d.Cwc / vsHeight P.z t * Real.sqrt (P.ups t x₁ y₁ * P.ups t x₂ y₂)) ∧
      (∀ x y, ∑ q, Real.sqrt (P.ups t x q * P.ups t q y) ≤
        d.C1pp / vsHeight P.z t * Real.sqrt (((m * W : ℕ) : ℝ) * vsHeight P.z t) *
          Real.sqrt (P.ups t x y)) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hWN : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
  obtain ⟨hη, hηC, hL, -⟩ :=
    P.height_bounds hN hW hWN d.kappa_pos (by linarith [d.C0_ge_one]) hz hPW ht0 ht1
  have hu : P.ups t = polynomialControl (m * W) W d.D (vsHeight P.z t) := by
    unfold PsiData.ups
    rw [hPW, hPD]
  have hl : P.lEta t = localizationLength (m * W) W (vsHeight P.z t) * vsHeight P.z t := by
    unfold PsiData.lEta
    rw [hPW]
  obtain ⟨hU2a, -, -, -, -, -, hU4, hU5, hU6, hU7, -, -, -⟩ :=
    LemmaK.ups_U2_U8_vs d hm hW hz ht0 le_rfl ht1
  refine ⟨fun x y => ?_, hL, hη, hηC, fun x y => ?_, fun x a y => ?_, fun x y => ?_,
    fun x₁ x₂ y₁ y₂ => ?_, fun x y => ?_⟩
  · rw [hu]
    exact (polynomialControl_pos hN hW _ hη x y).le
  · rw [hu, hl]
    exact hU2a x y
  · rw [hu, hl]
    exact (hU4 x y).1 a
  · rw [hu]
    exact hU5 x y
  · rw [hu]
    exact hU6 x₁ x₂ y₁ y₂
  · rw [hu]
    exact hU7 x y

/-- **Isotropic convolution along the VS flow.** For VS data `d`, `m ≥ 4`, `W ≥ 1`,
`P : PsiData (mW)` with `P.W = W`, `P.D = d.D`, `P.z ∈ BulkDomain (mW) d.δ₀ d.κ d.C₀`, `t ∈ [0,1]`,
`η = vsHeight P.z t`; isotropic sites `x` (`i` entries), `y` (`j` entries) and `w` whose first `i`
entries are `x` and next `j` entries are `y`: `Σ_q s^iso_{i+1}(a,x,q) s^iso_{j+1}(q,y,b) ≤
C₁''/η · √(mW η) · s^iso_{i+j+1}(a,w,b)`. Input (U7). -/
theorem isoConvol_vs {i j : ℕ} (a b : Fin (m * W)) (x : Fin (i + 1) → Fin (m * W))
    (y : Fin (j + 1) → Fin (m * W)) (w : Fin (i + j + 1) → Fin (m * W))
    (hx : ∀ (n : ℕ) (hn : n < i), x ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) :
    ∑ q, P.sIso a q x t * P.sIso q b y t ≤
      d.C1pp / vsHeight P.z t * Real.sqrt (((m * W : ℕ) : ℝ) * vsHeight P.z t) *
        P.sIso a b w t := by
  obtain ⟨hU, hL, -, -, -, -, -, -, h7⟩ := contr_vs_inputs d hm hW P hPW hPD hz ht0 ht1
  exact isoConvol_of P t hU hL h7 a b x y w hx hy

/-- **Isotropic concatenation along the VS flow.** Under the hypotheses of `isoConvol_vs`, for every
`q`: `s^iso_{i+1}(a,x,q) s^iso_{j+1}(q,y,b) ≤ √C₁'' · (ℓη)^{-1/2} · s^iso_{i+j+1}(a,w,b)`.
Input (U4). -/
theorem isoConcat_vs {i j : ℕ} (a b : Fin (m * W)) (x : Fin (i + 1) → Fin (m * W))
    (y : Fin (j + 1) → Fin (m * W)) (w : Fin (i + j + 1) → Fin (m * W))
    (hx : ∀ (n : ℕ) (hn : n < i), x ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) (q : Fin (m * W)) :
    P.sIso a q x t * P.sIso q b y t ≤
      Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a b w t := by
  obtain ⟨hU, hL, -, -, -, h4, -⟩ := contr_vs_inputs d hm hW P hPW hPD hz ht0 ht1
  have hK : 0 ≤ d.C1pp / P.lEta t := div_nonneg (by linarith [d.one_le_C1pp]) hL.le
  have h := isoConcat_of P t hU hL hK h4 a b x y w hx hy q
  have e : Real.sqrt (d.C1pp / P.lEta t) = Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, Real.sqrt_mul (by linarith [d.one_le_C1pp]), Real.sqrt_inv,
      Real.sqrt_eq_rpow (P.lEta t), ← Real.rpow_neg hL.le]
  rwa [e] at h

/-- **Averaged insertion along the VS flow.** Under the VS hypotheses of `isoConvol_vs`, for
`i, j ≥ 1`, sites `w : Fin (i+j) → Fin (mW)`, averaged site vectors `xq q` (the first `i` entries of
`w`, then `q`) and isotropic sites `y` (`j` entries: the last `j` entries of `w`):
`Σ_q s^av_{i+1}(x,q) s^iso_{j+1}(q,y,q) ≤ C_wc/η · (ℓη)^{-1/2} · s^av_{i+j}(w)`.
Input (U6). -/
theorem avInsertion_vs {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (xq : Fin (m * W) → Fin (i + 1) → Fin (m * W)) (y : Fin (j + 1) → Fin (m * W))
    (w : Fin (i + j) → Fin (m * W)) (hlast : ∀ q, xq q ⟨i, by omega⟩ = q)
    (hxq : ∀ (q : Fin (m * W)) (n : ℕ) (hn : n < i), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) :
    ∑ q, P.sAv (xq q) t * P.sIso q q y t ≤
      d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t := by
  obtain ⟨hU, hL, -, -, -, -, -, h6, -⟩ := contr_vs_inputs d hm hW P hPW hPD hz ht0 ht1
  exact avInsertion_of P t hU hL h6 hi hj xq y w hlast hxq hy

/-- **Averaged concatenation along the VS flow.** Under the hypotheses of `avInsertion_vs`, for
every `q`: `s^av_{i+1}(x,q) s^iso_{j+1}(q,y,q) ≤ C₁'' · (ℓη)^{-3/2} · s^av_{i+j}(w)`.
Input (U4). -/
theorem avConcat_vs {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (xq : Fin (m * W) → Fin (i + 1) → Fin (m * W)) (y : Fin (j + 1) → Fin (m * W))
    (w : Fin (i + j) → Fin (m * W)) (hlast : ∀ q, xq q ⟨i, by omega⟩ = q)
    (hxq : ∀ (q : Fin (m * W)) (n : ℕ) (hn : n < i), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) (q : Fin (m * W)) :
    P.sAv (xq q) t * P.sIso q q y t ≤ d.C1pp * P.lEta t ^ (-(3 / 2 : ℝ)) * P.sAv w t := by
  obtain ⟨hU, hL, -, -, -, h4, -⟩ := contr_vs_inputs d hm hW P hPW hPD hz ht0 ht1
  have hK : 0 ≤ d.C1pp / P.lEta t := div_nonneg (by linarith [d.one_le_C1pp]) hL.le
  have h := avConcat_of P t hU hL hK h4 hi hj xq y w hlast hxq hy q
  have e : d.C1pp / P.lEta t * P.lEta t ^ (-(1 / 2 : ℝ)) =
      d.C1pp * P.lEta t ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add hL]
    norm_num
  rwa [e] at h

/-- **Isotropic `S`-bound along the VS flow.** Under the VS hypotheses of `isoConvol_vs` and
`P.S = shortRingProfile d.b m W`, for `k ≥ 1`, sites `w : Fin k → Fin (mW)` and isotropic sites
`x` (`k` entries, equal to `w`):
`Σ_{q'} Σ_q S(q',q) s^iso_{k+1}(q',x,q)² ≤ (1+2√(C₀+1))^D · C_wc · C₁''/η · s^av_k(w)²`.
Inputs (K4) (`lemmaK_K4_explicit`), (U5), (U2). -/
theorem isoS_vs (hPS : P.S = shortRingProfile d.b m W) {k : ℕ} (hk : 1 ≤ k)
    (x : Fin (k + 1) → Fin (m * W)) (w : Fin k → Fin (m * W))
    (hx : ∀ (n : ℕ) (hn : n < k), x ⟨n, by omega⟩ = w ⟨n, by omega⟩) :
    ∑ q', ∑ q, P.S q' q * P.sIso q' q x t ^ 2 ≤
      (1 + 2 * Real.sqrt (d.C0 + 1)) ^ d.D * d.Cwc * d.C1pp / vsHeight P.z t *
        P.sAv w t ^ 2 := by
  obtain ⟨hU, hL, hη, hηC, hU2, -, h5, -⟩ := contr_vs_inputs d hm hW P hPW hPD hz ht0 ht1
  have hD0 : 0 ≤ d.D := by linarith [d.D_ge_six]
  have hCS : 0 ≤ (1 + 2 * Real.sqrt (d.C0 + 1)) ^ d.D := by positivity
  have hK : 0 ≤ d.Cwc / vsHeight P.z t := div_nonneg (by linarith [d.one_le_Cwc]) hη.le
  have hSsym : ∀ x y, P.S x y = P.S y x := fun x y => by
    rw [hPS]
    exact shortRingProfile_symm d.b m W x y
  have hSU : ∀ x y, ∑ a, P.S x a * P.ups t a y ≤
      (1 + 2 * Real.sqrt (d.C0 + 1)) ^ d.D * P.ups t x y := fun x y => by
    have h := (LemmaK.lemmaK_K4_explicit d.b_pos d.b_lt_half hm hW d.C0_ge_one hD0 hη hηC
      x y).2
    rw [Matrix.mul_apply] at h
    have hu : P.ups t = polynomialControl (m * W) W d.D (vsHeight P.z t) := by
      unfold PsiData.ups
      rw [hPW, hPD]
    rw [hPS, hu]
    exact h
  have h := isoS_of P t hU hL hCS hK d.one_le_C1pp hSsym hSU h5 hU2 hk x w hx
  calc ∑ q', ∑ q, P.S q' q * P.sIso q' q x t ^ 2
      ≤ (1 + 2 * Real.sqrt (d.C0 + 1)) ^ d.D * (d.Cwc / vsHeight P.z t) * d.C1pp *
          P.sAv w t ^ 2 := h
    _ = _ := by ring

end VS

end BlockBand.Native.ErdosRiabov.Contr
