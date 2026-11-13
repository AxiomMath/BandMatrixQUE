module

public import BlockBand.Native.ErdosRiabov.Contr.Paths
public import BlockBand.Native.ErdosRiabov.LemmaK.Ups

/-!
# Local contractions: splitting helpers, rotation and the VS inputs

Path-splitting lemmas for the size functions, rotation invariance of `s^av`, and the single-time
inputs of the local contractions. (U2)–(U7) denote the properties of the control `Υ` given by
`LemmaK.ups_U2_U8_vs`.

* Public path-splitting helpers (copies of private helpers of the local contractions):
  `contrSplit_iso_left`, `contrSplit_iso_right`, `contrSplit_iso_join`,
  `contrSplit_iso_shape`, `contrSplit_av_shape`; and two new shapes,
  `contrSplit_isoIns_shape` (an `s^iso` inserted at an interior site `q` of an `s^iso` chain,
  for the isotropic insertion) and `contrSplit_isoAv_shape` (`Υ(a,q) s^av_k(x',q)`, for the
  isotropic-averaged bound).
* Rotation invariance of `s^av`: `contr_sAv_comp_finRotate_pow`
  (`s^av_k(x ∘ rot^r) = s^av_k(x)`) and `contr_sAv_rotate` (the same for `w_n = x_{(n+r) mod k}`).
* `ContrVSInputs d P t`: the single-time inputs (U2) max, (U4) both clauses, (U5), (U6), (U7),
  symmetry and positivity, as named fields; `contrVSInputs_of` proves them from
  `LemmaK.ups_U2_U8_vs` (at `s = t`) under `P.W = W`, `P.D = d.D`, `P.z ∈ 𝒟`, `t ∈ [0,1]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Contr

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Internal.Contracts.Inputs (polynomialControl)
open BlockBand.Adapters.ErdosRiabov (polynomialControl_pos polynomialControl_symm)

variable {N : ℕ}

/-!
## Decompositions of the path products
-/

section Decomp

variable (U : Matrix (Fin N) (Fin N) ℝ)

/-- The left isotropic factor: `Π` along `isoPoint a q x` is the prefix of `w` times
`U(p_i, q)`. -/
theorem contrSplit_iso_left {i j : ℕ} (a b q : Fin N) (x : Fin (i + 1) → Fin N)
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

/-- The right isotropic factor: `Π` along `isoPoint q b y` is `U(q, p_{i+1})` times the
suffix of `w`. -/
theorem contrSplit_iso_right {i j : ℕ} (a b q : Fin N) (y : Fin (j + 1) → Fin N)
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

/-- The joined isotropic path: prefix, the edge `(p_i, p_{i+1})`, suffix. -/
theorem contrSplit_iso_join {i j : ℕ} (a b : Fin N) (w : Fin (i + j + 1) → Fin N) :
    contrPathProd U (isoPoint a b w) (i + j + 1) =
      contrPathProd U (isoPoint a b w) i * U (isoPoint a b w i) (isoPoint a b w (i + 1)) *
        contrPathProd U (fun n => isoPoint a b w (i + 1 + n)) j := by
  have h := contrPathProd_add U (isoPoint a b w) (i + 1) j
  rw [show i + 1 + j = i + j + 1 by omega, contrPathProd_succ U _ i] at h
  exact h

end Decomp

/-!
## Shapes of the contracted products
-/

section Shapes

variable (P : PsiData N) (t : ℝ)

/-- The isotropic join: both sides of the isotropic convolution and concatenation in the form
`c √(R · U(u,q)U(q,v))` and `c √(R · U(u,v))`. -/
theorem contrSplit_iso_shape (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {i j : ℕ}
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
  · rw [contr_sIso_eq P, contr_sIso_eq P, contrSplit_iso_left U a b q x w hx,
      contrSplit_iso_right U a b q y w hy]
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
  · rw [contr_sIso_eq P, contrSplit_iso_join U a b w, ← Real.rpow_add hL]
    congr 1
    · congr 1
      simp only [e₁, e₂]
      push_cast
      ring
    · congr 1
      ring

/-- The averaged join: both sides of the averaged insertion and concatenation in the form
`c √(R · U(x₁,q)U(x₂,q)U(q,y₁)U(q,y₂))` and `(ℓη)^{-1/2} s^av = c √(R · U(x₁,y₁)U(x₂,y₂))`. -/
theorem contrSplit_av_shape (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {i j : ℕ}
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

/-- The isotropic insertion: an `s^iso_{p+1}(q,y,q)` (`p ≥ 1` sites `y`)
times an `s^iso_{r+s+2}(a, u, q, v, b)` (`r` sites `u`, the interior site `q`, `s` sites `v`), in
the form `c √(R · U(x₁,q)U(x₂,q)U(q,y₁)U(q,y₂))`, and `(ℓη)^{-1/2} s^iso_{r+p+s+1}(a,(u,y,v),b)`
in the form `c √(R · U(x₁,y₁)U(x₂,y₂))`. -/
theorem contrSplit_isoIns_shape (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t)
    {r p s : ℕ} (hp : 1 ≤ p) (a b : Fin N) (y : Fin (p + 1) → Fin N)
    (zq : Fin N → Fin (r + s + 2) → Fin N) (w : Fin (r + p + s + 1) → Fin N)
    (hzpre : ∀ (q : Fin N) (n : ℕ) (hn : n < r), zq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hzmid : ∀ q, zq q ⟨r, by omega⟩ = q)
    (hzpost : ∀ (q : Fin N) (n : ℕ) (hn : n < s),
      zq q ⟨r + 1 + n, by omega⟩ = w ⟨r + p + n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < p), y ⟨n, by omega⟩ = w ⟨r + n, by omega⟩) :
    ∃ c R : ℝ, ∃ x₁ x₂ y₁ y₂ : Fin N, 0 ≤ c ∧ 0 ≤ R ∧
      (∀ q, P.sIso q q y t * P.sIso a b (zq q) t =
        c * Real.sqrt (R * (P.ups t x₁ q * P.ups t x₂ q * P.ups t q y₁ * P.ups t q y₂))) ∧
      P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a b w t =
        c * Real.sqrt (R * (P.ups t x₁ y₁ * P.ups t x₂ y₂)) := by
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨pw, hpw⟩ : ∃ f, f = isoPoint a b w := ⟨_, rfl⟩
  set U := P.ups t
  -- sites of the outer chain
  have hpre : ∀ q, ∀ n ≤ r, isoPoint a b (zq q) n = pw n := by
    intro q n hn
    rw [hpw]
    rcases n with _ | n
    · rw [contr_isoPoint_zero, contr_isoPoint_zero]
    · rw [contr_isoPoint_succ _ _ _ (by omega), contr_isoPoint_succ _ _ _ (by omega)]
      exact hzpre q n (by omega)
  have hmid : ∀ q, isoPoint a b (zq q) (r + 1) = q := by
    intro q
    rw [contr_isoPoint_succ _ _ _ (by omega)]
    exact hzmid q
  have hpost : ∀ q, ∀ n ≤ s, isoPoint a b (zq q) (r + 1 + 1 + n) = pw (r + (p + 1) + 1 + n) := by
    intro q n hn
    rw [hpw, show r + 1 + 1 + n = (r + 1 + n) + 1 by omega,
      show r + (p + 1) + 1 + n = (r + (p + 1) + n) + 1 by omega]
    rcases Nat.lt_or_ge n s with h | h
    · rw [contr_isoPoint_succ _ _ _ (by omega), contr_isoPoint_succ _ _ _ (by omega)]
      exact hzpost q n h
    · rw [contr_isoPoint_of_le _ _ _ (by omega) (by omega),
        contr_isoPoint_of_le _ _ _ (by omega) (by omega)]
  -- sites of the inserted chain
  have hiy : ∀ q, ∀ n ≤ p, isoPoint q q y (n + 1) = pw (r + 1 + n) := by
    intro q n hn
    rw [hpw, show r + 1 + n = (r + n) + 1 by omega, contr_isoPoint_succ _ _ _ (by omega),
      contr_isoPoint_succ _ _ _ (by omega)]
    exact hy n (by omega)
  -- decompositions
  have hz : ∀ q, contrPathProd U (isoPoint a b (zq q)) (r + s + 2) =
      contrPathProd U pw r * U (pw r) q * U q (pw (r + (p + 1) + 1)) *
        contrPathProd U (fun n => pw (r + (p + 1) + 1 + n)) s := by
    intro q
    have h := contrPathProd_add U (isoPoint a b (zq q)) (r + 1 + 1) s
    rw [show r + 1 + 1 + s = r + s + 2 by omega, contrPathProd_succ U _ (r + 1),
      contrPathProd_succ U _ r] at h
    have h0 := hpost q 0 (Nat.zero_le _)
    simp only [add_zero] at h0
    rw [h, contrPathProd_congr U (hpre q), hpre q r le_rfl, hmid q, h0,
      contrPathProd_congr U (hpost q)]
  have hiso : ∀ q, contrPathProd U (isoPoint q q y) (p + 1 + 1) =
      U q (pw (r + 1)) * (contrPathProd U (fun n => pw (r + 1 + n)) p * U (pw (r + 1 + p)) q) := by
    intro q
    rw [contrPathProd_succ', contrPathProd_succ U _ p, contr_isoPoint_zero,
      hiy q 0 (Nat.zero_le _), hiy q p le_rfl, contr_isoPoint_of_le _ _ _ (by omega) le_rfl,
      contrPathProd_congr U (hiy q)]
  have htgt : contrPathProd U pw (r + (p + 1) + s + 1) =
      contrPathProd U pw r * U (pw r) (pw (r + 1)) *
        (contrPathProd U (fun n => pw (r + 1 + n)) p * U (pw (r + 1 + p)) (pw (r + (p + 1) + 1))) *
        contrPathProd U (fun n => pw (r + (p + 1) + 1 + n)) s := by
    have h1 := contrPathProd_add U pw (r + 1 + (p + 1)) s
    rw [show r + 1 + (p + 1) + s = r + (p + 1) + s + 1 by omega] at h1
    rw [h1, contrPathProd_add U pw (r + 1) (p + 1), contrPathProd_succ U _ r,
      contrPathProd_succ U _ p, show r + 1 + (p + 1) = r + (p + 1) + 1 by omega]
  set A := contrPathProd U pw r
  set B := contrPathProd U (fun n => pw (r + 1 + n)) p
  set C := contrPathProd U (fun n => pw (r + (p + 1) + 1 + n)) s
  have hA : 0 ≤ A := contrPathProd_nonneg hU _ _
  have hB : 0 ≤ B := contrPathProd_nonneg hU _ _
  have hC : 0 ≤ C := contrPathProd_nonneg hU _ _
  set ey : ℝ := -(((p + 1 + 1 : ℕ) : ℝ) - 1) / 2
  set ez : ℝ := -(((r + s + 2 : ℕ) : ℝ) - 1) / 2
  set ew : ℝ := -(((r + (p + 1) + s + 1 : ℕ) : ℝ) - 1) / 2
  have hexp : P.lEta t ^ ey * P.lEta t ^ ez = P.lEta t ^ (-(1 / 2 : ℝ)) * P.lEta t ^ ew := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL]
    congr 1
    simp only [ey, ez, ew]
    push_cast
    ring
  refine ⟨P.lEta t ^ ey * P.lEta t ^ ez, A * B * C, pw r, pw (r + 1 + p), pw (r + 1),
    pw (r + (p + 1) + 1), mul_nonneg (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hL.le _),
    mul_nonneg (mul_nonneg hA hB) hC, fun q => ?_, ?_⟩
  · rw [contr_sIso_eq P, contr_sIso_eq P, hiso q, hz q]
    have hY : 0 ≤ U q (pw (r + 1)) * (B * U (pw (r + 1 + p)) q) :=
      mul_nonneg (hU _ _) (mul_nonneg hB (hU _ _))
    calc P.lEta t ^ ey * Real.sqrt (U q (pw (r + 1)) * (B * U (pw (r + 1 + p)) q)) *
          (P.lEta t ^ ez * Real.sqrt (A * U (pw r) q * U q (pw (r + (p + 1) + 1)) * C))
        = P.lEta t ^ ey * P.lEta t ^ ez *
            (Real.sqrt (U q (pw (r + 1)) * (B * U (pw (r + 1 + p)) q)) *
              Real.sqrt (A * U (pw r) q * U q (pw (r + (p + 1) + 1)) * C)) := by ring
      _ = _ := by
          rw [← Real.sqrt_mul hY]
          congr 2
          ring
  · rw [contr_sIso_eq P, ← hpw, htgt, hexp]
    have e : A * U (pw r) (pw (r + 1)) *
          (B * U (pw (r + 1 + p)) (pw (r + (p + 1) + 1))) * C =
        A * B * C * (U (pw r) (pw (r + 1)) * U (pw (r + 1 + p)) (pw (r + (p + 1) + 1))) := by
      ring
    rw [e]
    ring

/-- The isotropic-averaged contraction shape: for a symmetric `U`,
`Υ(a,q) s^av_{p+1}(x',q)` (`p ≥ 1` sites `x'`, then `q`) in the form
`c √(R · U(x₁,q)U(x₂,q)U(q,y₁)U(q,y₂))`, and `(ℓη)^{-1/2} s^iso_{p+1}(a,x',a)` in the form
`c √(R · U(x₁,y₁)U(x₂,y₂))`. -/
theorem contrSplit_isoAv_shape (hU : ∀ x y, 0 ≤ P.ups t x y)
    (hsym : ∀ x y, P.ups t x y = P.ups t y x) (hL : 0 < P.lEta t) {p : ℕ} (hp : 1 ≤ p)
    (a : Fin N) (xq : Fin N → Fin (p + 1) → Fin N) (x : Fin (p + 1) → Fin N)
    (hlast : ∀ q, xq q ⟨p, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < p), xq q ⟨n, by omega⟩ = x ⟨n, by omega⟩) :
    ∃ c R : ℝ, ∃ x₁ x₂ y₁ y₂ : Fin N, 0 ≤ c ∧ 0 ≤ R ∧
      (∀ q, P.ups t a q * P.sAv (xq q) t =
        c * Real.sqrt (R * (P.ups t x₁ q * P.ups t x₂ q * P.ups t q y₁ * P.ups t q y₂))) ∧
      P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a a x t =
        c * Real.sqrt (R * (P.ups t x₁ y₁ * P.ups t x₂ y₂)) := by
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  set U := P.ups t
  have hix : ∀ (n : ℕ) (hn : n ≤ p), isoPoint a a x (n + 1) = x ⟨n, by omega⟩ := by
    intro n hn
    have h : n + 1 < p + 1 + 1 := by omega
    exact contr_isoPoint_succ _ _ _ h
  have hav : ∀ q, contrPathProd U (contrCycPt (xq q) (xq q ⟨0, by omega⟩)) (p + 1 + 1) =
      contrPathProd U (fun n => isoPoint a a x (n + 1)) p * U (isoPoint a a x (p + 1)) q *
        U q (isoPoint a a x 1) := by
    intro q
    have hpt : ∀ n ≤ p, contrCycPt (xq q) (xq q ⟨0, by omega⟩) n = isoPoint a a x (n + 1) := by
      intro n hn
      rw [contr_cycPt_lt _ _ (by omega), hix n hn]
      exact hxq q n (by omega)
    have h1 : contrCycPt (xq q) (xq q ⟨0, by omega⟩) (p + 1) = q := by
      rw [contr_cycPt_lt _ _ (by omega)]
      exact hlast q
    have h2 : contrCycPt (xq q) (xq q ⟨0, by omega⟩) (p + 1 + 1) = isoPoint a a x 1 := by
      rw [contr_cycPt_ge _ _ le_rfl, contr_isoPoint_succ _ _ _ (by omega)]
      exact hxq q 0 (by omega)
    rw [contrPathProd_succ, contrPathProd_succ, contrPathProd_congr U hpt, hpt p le_rfl, h1, h2]
  have hiso : contrPathProd U (isoPoint a a x) (p + 1 + 1) =
      U a (isoPoint a a x 1) *
        (contrPathProd U (fun n => isoPoint a a x (n + 1)) p * U (isoPoint a a x (p + 1)) a) := by
    rw [contrPathProd_succ', contrPathProd_succ U _ p, contr_isoPoint_zero,
      contr_isoPoint_of_le _ _ _ (by omega) (le_refl (p + 1 + 1))]
  set A := contrPathProd U (fun n => isoPoint a a x (n + 1)) p
  have hA : 0 ≤ A := contrPathProd_nonneg hU _ _
  set u := isoPoint a a x (p + 1)
  set v := isoPoint a a x 1
  set ea : ℝ := -(((p + 1 + 1 : ℕ) : ℝ)) / 2
  set ei : ℝ := -(((p + 1 + 1 : ℕ) : ℝ) - 1) / 2
  have hexp : P.lEta t ^ ea = P.lEta t ^ (-(1 / 2 : ℝ)) * P.lEta t ^ ei := by
    rw [← Real.rpow_add hL]
    congr 1
    simp only [ea, ei]
    push_cast
    ring
  refine ⟨P.lEta t ^ ea, A, u, a, a, v, Real.rpow_nonneg hL.le _, hA, fun q => ?_, ?_⟩
  · rw [contr_sAv_eq P (by omega) (xq q) t, hav q]
    have haq : U a q = Real.sqrt (U a q * U q a) := by
      rw [hsym q a, Real.sqrt_mul_self (hU _ _)]
    have hX : 0 ≤ U a q * U q a := mul_nonneg (hU _ _) (hU _ _)
    calc U a q * (P.lEta t ^ ea * Real.sqrt (A * U u q * U q v))
        = Real.sqrt (U a q * U q a) * (P.lEta t ^ ea * Real.sqrt (A * U u q * U q v)) := by
          rw [← haq]
      _ = P.lEta t ^ ea * (Real.sqrt (U a q * U q a) * Real.sqrt (A * U u q * U q v)) := by
          ring
      _ = _ := by
          rw [← Real.sqrt_mul hX]
          congr 2
          ring
  · rw [contr_sIso_eq P, hiso, hexp]
    have e : U a v * (A * U u a) = A * (U u a * U a v) := by ring
    rw [e]
    ring

end Shapes

/-!
## Rotation invariance of `s^av`
-/

/-- `(finRotate k ^ r) j = (j + r) mod k`. -/
theorem contr_finRotate_pow_val {k : ℕ} (r : ℕ) (j : Fin k) :
    ((finRotate k ^ r) j : ℕ) = (j + r) % k := by
  rcases k with _ | n
  · exact j.elim0
  induction r generalizing j with
  | zero => simp [Nat.mod_eq_of_lt j.isLt]
  | succ r ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, coe_finRotate]
    split_ifs with h
    · subst h
      rw [Fin.val_last, show n + (r + 1) = r + (n + 1) by ring, Nat.add_mod_right, zero_add]
    · congr 1
      omega

/-- **Rotation invariance of `s^av`.** `s^av_k(x ∘ rot^r) = s^av_k(x)`, `rot = finRotate k`. -/
theorem contr_sAv_comp_finRotate_pow (P : PsiData N) {k : ℕ} (x : Fin k → Fin N) (r : ℕ)
    (t : ℝ) : P.sAv (fun j => x ((finRotate k ^ r) j)) t = P.sAv x t := by
  unfold PsiData.sAv
  split_ifs with h
  · rfl
  · congr 2
    have hc : ∀ j, (finRotate k ^ r) (finRotate k j) = finRotate k ((finRotate k ^ r) j) := by
      intro j
      have := congrArg (fun f : Equiv.Perm (Fin k) => f j) (Commute.self_pow (finRotate k) r).eq
      simpa only [Equiv.Perm.mul_apply] using this.symm
    simp_rw [hc]
    exact Equiv.prod_comp (finRotate k ^ r) (fun j => P.ups t (x j) (x (finRotate k j)))

/-- **Cyclic shift of the sites of `s^av`.** If
`w_n = x_{(n+r) mod k}` for all `n < k`, then `s^av_k(w) = s^av_k(x)`. -/
theorem contr_sAv_rotate (P : PsiData N) {k : ℕ} (x w : Fin k → Fin N) (r : ℕ)
    (hw : ∀ (n : ℕ) (hn : n < k), w ⟨n, hn⟩ = x ⟨(n + r) % k, Nat.mod_lt _ (by omega)⟩)
    (t : ℝ) : P.sAv w t = P.sAv x t := by
  have hwx : w = fun j => x ((finRotate k ^ r) j) := by
    funext j
    calc w j = w ⟨j, j.isLt⟩ := rfl
      _ = x ⟨(j + r) % k, Nat.mod_lt _ j.pos⟩ := hw _ _
      _ = x ((finRotate k ^ r) j) := congrArg x (Fin.ext (contr_finRotate_pow_val r j).symm)
  rw [hwx, contr_sAv_comp_finRotate_pow]

/-!
## The VS inputs at a single time
-/

/-- The single-time inputs of the local contractions at VS data `d`: positivity, symmetry,
(U2) max, (U4) triangle and √-convolution, (U5), (U6), (U7), with `η = vsHeight P.z t`,
`ℓη = P.lEta t`. -/
structure ContrVSInputs (d : VSData) {N : ℕ} (P : PsiData N) (t : ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ P.ups t x y
  symm : ∀ x y, P.ups t x y = P.ups t y x
  lEta_pos : 0 < P.lEta t
  height_pos : 0 < vsHeight P.z t
  height_le : vsHeight P.z t ≤ d.C0 + 1
  maxU : ∀ x y, P.ups t x y ≤ d.C1pp / P.lEta t
  triangle : ∀ x a y, P.ups t x a * P.ups t a y ≤ d.C1pp / P.lEta t * P.ups t x y
  sqrtConvol : ∀ x y, ∑ a, Real.sqrt (P.ups t x a * P.ups t a y) ≤
    d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t * P.ups t x y)
  convol : ∀ x y, ∑ a, P.ups t x a * P.ups t a y ≤ d.Cwc / vsHeight P.z t * P.ups t x y
  schwarz : ∀ x₁ x₂ y₁ y₂, ∑ q, Real.sqrt (P.ups t x₁ q * P.ups t x₂ q * P.ups t q y₁ *
    P.ups t q y₂) ≤ d.Cwc / vsHeight P.z t * Real.sqrt (P.ups t x₁ y₁ * P.ups t x₂ y₂)
  sqrtConvolN : ∀ x y, ∑ q, Real.sqrt (P.ups t x q * P.ups t q y) ≤
    d.C1pp / vsHeight P.z t * Real.sqrt ((N : ℝ) * vsHeight P.z t) * Real.sqrt (P.ups t x y)

/-- **The VS inputs.** For VS data `d`, `m ≥ 4`, `W ≥ 1`, `P : PsiData (mW)` with
`P.W = W`, `P.D = d.D`, `P.z ∈ BulkDomain (mW) d.δ₀ d.κ d.C₀` and `t ∈ [0,1]`, all fields of
`ContrVSInputs d P t` hold (`LemmaK.ups_U2_U8_vs` at `s = t`, `PsiData.height_bounds`). -/
theorem contrVSInputs_of (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W))
    (hPW : P.W = W) (hPD : P.D = d.D) (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ContrVSInputs d P t := by
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
  refine ⟨fun x y => ?_, fun x y => ?_, hL, hη, hηC, fun x y => ?_, fun x a y => ?_,
    fun x y => ?_, fun x y => ?_, fun x₁ x₂ y₁ y₂ => ?_, fun x y => ?_⟩
  · rw [hu]
    exact (polynomialControl_pos hN hW _ hη x y).le
  · rw [hu]
    exact polynomialControl_symm _ _ _ _ x y
  · rw [hu, hl]
    exact hU2a x y
  · rw [hu, hl]
    exact (hU4 x y).1 a
  · rw [hu, hl]
    exact (hU4 x y).2
  · rw [hu]
    exact hU5 x y
  · rw [hu]
    exact hU6 x₁ x₂ y₁ y₂
  · rw [hu]
    exact hU7 x y

end BlockBand.Native.ErdosRiabov.Contr
