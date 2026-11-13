module

public import BlockBand.Native.ErdosRiabov.Forcing.Contr

/-!
# Forcing bounds: the averaged families

Bounds on the families FQ, FM2 and F1 of the averaged forcing, in terms of the thresholds
`ψ^A`, `ψ^I` and the `M`-bound constants. Per pair `i < j` (0-based; segment length `p = j - i + 1`,
glued length `r = k - (j - i) + 1`)
and per slot `j` (F1), with `L = ℓη`, `η = η_t`, normalized by `L^{β_k} s^av_k(x)`:
* FQ: `η |Σ_q (a_G - a_M)(b_G - b_M)| ≤ C_wc ψ^A_r L^{-(β_k-β_r)} ψ^I_p L^{-(1/2-α_p)}`;
* FM2: `η |Σ_q a_M (b_G - b_M)| ≤ C_wc I_p ψ^A_r L^{-(β_k-β_r)}`;
* F1, `k ≤ 7`: `η |F1_j| ≤ C_wc ψ^A_1 ψ^I_{k+1} L^{-1/2} + E_k ψ^A_1 L^{-β_k}`;
* `k = 1`: `η |𝓕^av| ≤ C_wc ψ^A_1 ψ^I_2 L^{-1/2}`.
The `k = 8` F1 bound and the FM1 family are treated separately.
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
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo (lossAlpha lossBeta)

variable {N k : ℕ}

/-!
## Helpers
-/

theorem mem_kRange {n : ℕ} (h1 : 1 ≤ n) (h8 : n ≤ 8) : n ∈ kRange := by
  simp only [kRange, vsK, Finset.mem_Icc]
  omega

theorem mod_of_ge {a m : ℕ} (h1 : m ≤ a) (h2 : a < m + m) : a % m = a - m := by
  rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

/-- Rotation invariance of `s^av` across a length identity. -/
theorem sAv_rot (P : PsiData N) (t : ℝ) {n m : ℕ} (h : n = m) (w : Fin n → Fin N)
    (x : Fin m → Fin N) (r : ℕ)
    (hw : ∀ (l : ℕ) (hl : l < n), w ⟨l, hl⟩ = x ⟨(l + r) % m, Nat.mod_lt _ (by omega)⟩) :
    P.sAv w t = P.sAv x t := by
  subst h
  exact contr_sAv_rotate P x w r hw t

theorem rpow_three {L : ℝ} (hL : 0 < L) {a b c a' b' c' : ℝ} (h : a + b + c = a' + b' + c') :
    L ^ a * L ^ b * L ^ c = L ^ a' * L ^ b' * L ^ c' := by
  rw [← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL, h]

/-- `√C₁'' · C₁'' = C_wc = C₁''^{3/2}`. -/
theorem sqrt_mul_C1pp (d : VSData) : Real.sqrt d.C1pp * d.C1pp = d.Cwc := by
  have h0 : 0 < d.C1pp := by linarith [d.one_le_C1pp]
  rw [VSData.Cwc, Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.rpow_add h0, Real.rpow_one]

/-!
## The glued averaged sites, rotated so that `q` is last
-/

section GlueRot

/-- The glued sites rotated by `i + 1`: `(x_j, …, x_{k-1}, x_0, …, x_{i-1}, q)`. -/
def glueRot (x : Fin k → Fin N) (i j : Fin k) (q : Fin N) : Fin (k - ((j : ℕ) - i) + 1) → Fin N :=
  fun n => glueSites x i j q ⟨((n : ℕ) + i + 1) % (k - ((j : ℕ) - i) + 1), Nat.mod_lt _ (by omega)⟩

/-- `x` rotated by `j`, of length `(k - (j - i)) + (j - i)`. -/
def wGlue (x : Fin k → Fin N) (i j : Fin k) : Fin (k - ((j : ℕ) - i) + ((j : ℕ) - i)) → Fin N :=
  fun n => x ⟨((n : ℕ) + j) % k, Nat.mod_lt _ j.pos⟩

variable (P : PsiData N) (t : ℝ) (x : Fin k → Fin N)

theorem sAv_glueRot (i j : Fin k) (q : Fin N) :
    P.sAv (glueRot x i j q) t = P.sAv (glueSites x i j q) t :=
  contr_sAv_rotate P _ _ ((i : ℕ) + 1) (fun l hl => by simp only [glueRot, add_assoc]) t

theorem sAv_wGlue {i j : Fin k} (hij : i < j) : P.sAv (wGlue x i j) t = P.sAv x t := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  exact sAv_rot P t (by omega) _ _ j (fun l hl => rfl)

theorem glueRot_last {i j : Fin k} (hij : i < j) (q : Fin N) :
    glueRot x i j q ⟨k - ((j : ℕ) - i), by omega⟩ = q := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  unfold glueRot glueSites
  have e : (k - ((j : ℕ) - i) + i + 1) % (k - ((j : ℕ) - i) + 1) = i := by
    rw [show k - ((j : ℕ) - i) + i + 1 = (k - ((j : ℕ) - i) + 1) + i by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]
  simp only [e, lt_irrefl, ite_false, ite_true]

theorem glueSites_of_lt {i j : Fin k} (q : Fin N) (l : Fin (k - ((j : ℕ) - i) + 1))
    (h : (l : ℕ) < i) : glueSites x i j q l = x ⟨l, by omega⟩ := by
  unfold glueSites
  rw [ite_eq_left h]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem glueSites_of_gt {i j : Fin k} (hij : i < j) (q : Fin N)
    (l : Fin (k - ((j : ℕ) - i) + 1)) (h : (i : ℕ) < l) :
    glueSites x i j q l = x ⟨(l : ℕ) + ((j : ℕ) - i) - 1, by
      have := l.isLt; have := j.isLt; have : (i : ℕ) < j := hij; omega⟩ := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  have hl := l.isLt
  unfold glueSites
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem glueRot_lt {i j : Fin k} (hij : i < j) (q : Fin N) (n : ℕ) (hn : n < k - ((j : ℕ) - i)) :
    glueRot x i j q ⟨n, by omega⟩ = x ⟨(n + j) % k, Nat.mod_lt _ j.pos⟩ := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  unfold glueRot
  set l : Fin (k - ((j : ℕ) - i) + 1) :=
    ⟨(n + i + 1) % (k - ((j : ℕ) - i) + 1), Nat.mod_lt _ (by omega)⟩ with hl
  by_cases h1 : n + i + 1 < k - ((j : ℕ) - i) + 1
  · have hv : (l : ℕ) = n + i + 1 := Nat.mod_eq_of_lt h1
    rw [glueSites_of_gt x hij q l (by omega)]
    congr 1
    exact Fin.ext (by simp only [hv]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
  · have hv : (l : ℕ) = n + i + 1 - (k - ((j : ℕ) - i) + 1) := mod_of_ge (by omega) (by omega)
    rw [glueSites_of_lt x q l (by omega)]
    congr 1
    exact Fin.ext (by simp only [hv]; rw [mod_of_ge (by omega) (by omega)]; omega)

theorem seg_wGlue {i j : Fin k} (hij : i < j) (n : ℕ) (hn : n < (j : ℕ) - i) :
    segSites x i j ⟨n, by omega⟩ = wGlue x i j ⟨k - ((j : ℕ) - i) + n, by omega⟩ := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  rw [segSites_apply x hij.le]
  unfold wGlue
  congr 1
  apply Fin.ext
  simp only
  rw [show k - ((j : ℕ) - i) + n + j = k + (i + n) by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (by omega)]

end GlueRot

/-- The rotated sites without the last entry are a rotation of `x`. -/
theorem sAv_rotSites (P : PsiData N) (t : ℝ) (x : Fin k → Fin N) (j : Fin k) :
    P.sAv (fun n : Fin k => rotSites x j n.castSucc) t = P.sAv x t :=
  contr_sAv_rotate P x _ j (fun n hn => by
    simp only [rotSites, Fin.castSucc_mk, add_comm (j : ℕ) n]) t

/-- The F1 slot term in the form of `famF1_av_term`, i.e. `Σ_p 𝒳¹(p) G_{pp}` of the rotated
chain. -/
def f1Term (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) (j : Fin k) : ℂ :=
  ∑ p, P.avErr (fun _ : Fin 1 => σ j) (fun _ : Fin 1 => p) t H *
    gChain (patZ P.z (rotPat σ j) t) (isoSlots P.S (rotSites x j)) H p p

/-!
## The pair families FQ and FM2
-/

section Pairs

variable {d : VSData} {P : PsiData N} {t : ℝ} (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ}
  {psiI psiA : ℕ → ℝ} (hAP : APriori P t H psiI psiA)
  (hpsi1 : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) (σ : Fin k → Bool) (x : Fin k → Fin N)
include c hAP hpsi1

/-- The contraction behind the FQ and FM2 bounds: with `F(q)` bounded by `f · s^iso_p(q, seg, q)` and
the
glued averaged error by `g · s^av_r(glue q)`. -/
theorem glue_contract (hk : k ≤ 8) {i j : Fin k} (hij : i < j) (F : Fin N → ℂ) {f : ℝ}
    (hF : ∀ q, ‖F q‖ ≤ f * P.sIso q q (segSites x i j) t) (hf : 0 ≤ f) :
    ‖∑ q, F q * P.avErr (gluePat σ i j) (glueSites x i j q) t H‖ ≤
      f * psiA (k - ((j : ℕ) - i) + 1) * P.lEta t ^ lossBeta (k - ((j : ℕ) - i) + 1) *
        (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv x t) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  set r := k - ((j : ℕ) - i) + 1
  have hr : r ∈ kRange := mem_kRange (by omega) (by omega)
  have hpsi : 0 ≤ psiA r * P.lEta t ^ lossBeta r :=
    mul_nonneg (by linarith [(hpsi1 r).2]) (lEta_rpow_pos c _).le
  have hterm : ∀ q, ‖F q * P.avErr (gluePat σ i j) (glueSites x i j q) t H‖ ≤
      f * (psiA r * P.lEta t ^ lossBeta r) *
        (P.sAv (glueRot x i j q) t * P.sIso q q (segSites x i j) t) := by
    intro q
    rw [norm_mul, sAv_glueRot]
    have h1 := hF q
    have h2 := norm_avErr_le c hAP hr (gluePat σ i j) (glueSites x i j q)
    calc ‖F q‖ * ‖P.avErr (gluePat σ i j) (glueSites x i j q) t H‖
        ≤ (f * P.sIso q q (segSites x i j) t) *
            (psiA r * P.lEta t ^ lossBeta r * P.sAv (glueSites x i j q) t) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hf (sIso_pos c _ _ _).le)
      _ = _ := by ring
  have hins := avInsertion_of P t (fun a b => (c.pos a b).le) c.lEta_pos c.schwarz
    (i := k - ((j : ℕ) - i)) (j := (j : ℕ) - i) (by omega) (by omega)
    (glueRot x i j) (segSites x i j) (wGlue x i j) (fun q => glueRot_last x hij q)
    (fun q n hn => glueRot_lt x hij q n hn) (fun n hn => seg_wGlue x hij n hn)
  rw [sAv_wGlue P t x hij] at hins
  calc ‖∑ q, F q * P.avErr (gluePat σ i j) (glueSites x i j q) t H‖
      ≤ ∑ q, ‖F q * P.avErr (gluePat σ i j) (glueSites x i j q) t H‖ := norm_sum_le _ _
    _ ≤ ∑ q, f * (psiA r * P.lEta t ^ lossBeta r) *
          (P.sAv (glueRot x i j q) t * P.sIso q q (segSites x i j) t) :=
        Finset.sum_le_sum fun q _ => hterm q
    _ = f * (psiA r * P.lEta t ^ lossBeta r) *
          ∑ q, P.sAv (glueRot x i j q) t * P.sIso q q (segSites x i j) t := by
        rw [Finset.mul_sum]
    _ ≤ f * (psiA r * P.lEta t ^ lossBeta r) *
          (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv x t) :=
        mul_le_mul_of_nonneg_left hins (mul_nonneg hf hpsi)
    _ = _ := by ring

/-- **FQ**, one pair. -/
theorem pair_avFQ (hk : k ≤ 8) {i j : Fin k} (hij : i < j) :
    vsHeight P.z t * ‖∑ q, (aG P σ t H (avSlots P.S x) i j q - aM P σ x t i j q) *
        (bGav P σ x t H i j q - bMav P σ x t i j q)‖ ≤
      d.Cwc * (psiA (k - ((j : ℕ) - i) + 1) *
          P.lEta t ^ (-(lossBeta k - lossBeta (k - ((j : ℕ) - i) + 1))) *
          psiI ((j : ℕ) - i + 1) * P.lEta t ^ (-(1 / 2 - lossAlpha ((j : ℕ) - i + 1)))) *
        (P.lEta t ^ lossBeta k * P.sAv x t) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  have hp : (j : ℕ) - i + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hsum : ∑ q, (aG P σ t H (avSlots P.S x) i j q - aM P σ x t i j q) *
        (bGav P σ x t H i j q - bMav P σ x t i j q) =
      ∑ q, P.isoErr (segPat σ i j) q q (segSites x i j) t H *
        P.avErr (gluePat σ i j) (glueSites x i j q) t H :=
    Finset.sum_congr rfl fun q _ => by
      rw [aG_sub_aM_av P σ x t H hij.le, bGav_sub_bMav P σ x t H hij]
  rw [hsum]
  have h := glue_contract c hAP hpsi1 σ x hk hij _
    (fun q => norm_isoErr_le c hAP hp (segPat σ i j) q q (segSites x i j))
    (mul_nonneg (by linarith [(hpsi1 ((j : ℕ) - i + 1)).1]) (lEta_rpow_pos c _).le)
  have hη := c.height_pos
  have e := rpow_three c.lEta_pos (a := -(lossBeta k - lossBeta (k - ((j : ℕ) - i) + 1)))
    (b := -(1 / 2 - lossAlpha ((j : ℕ) - i + 1))) (c := lossBeta k)
    (a' := lossAlpha ((j : ℕ) - i + 1)) (b' := lossBeta (k - ((j : ℕ) - i) + 1))
    (c' := -(1 / 2 : ℝ)) (by ring)
  calc vsHeight P.z t * ‖∑ q, P.isoErr (segPat σ i j) q q (segSites x i j) t H *
        P.avErr (gluePat σ i j) (glueSites x i j q) t H‖
      ≤ vsHeight P.z t * (psiI ((j : ℕ) - i + 1) * P.lEta t ^ lossAlpha ((j : ℕ) - i + 1) *
          psiA (k - ((j : ℕ) - i) + 1) * P.lEta t ^ lossBeta (k - ((j : ℕ) - i) + 1) *
          (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv x t)) :=
        mul_le_mul_of_nonneg_left h hη.le
    _ = d.Cwc * psiA (k - ((j : ℕ) - i) + 1) * psiI ((j : ℕ) - i + 1) *
          (P.lEta t ^ lossAlpha ((j : ℕ) - i + 1) *
            P.lEta t ^ lossBeta (k - ((j : ℕ) - i) + 1) * P.lEta t ^ (-(1 / 2 : ℝ))) *
          P.sAv x t := by
        field_simp
    _ = _ := by rw [← e]; ring

/-- **FM2**, one pair with `j - i ≥ 2`. -/
theorem pair_avFM2 (hk : k ≤ 8) {I : ℕ → ℝ} (hI : ∀ n ∈ kRange, IsoBAt P t n (I n))
    (hI0 : ∀ n, 0 ≤ I n) {i j : Fin k} (hij : i < j) :
    vsHeight P.z t * ‖∑ q, aM P σ x t i j q * (bGav P σ x t H i j q - bMav P σ x t i j q)‖ ≤
      d.Cwc * I ((j : ℕ) - i + 1) * (psiA (k - ((j : ℕ) - i) + 1) *
          P.lEta t ^ (-(lossBeta k - lossBeta (k - ((j : ℕ) - i) + 1)))) *
        (P.lEta t ^ lossBeta k * P.sAv x t) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  have hp : (j : ℕ) - i + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hsum : ∑ q, aM P σ x t i j q * (bGav P σ x t H i j q - bMav P σ x t i j q) =
      ∑ q, P.mChain (segPat σ i j) (segSites x i j) t q *
        P.avErr (gluePat σ i j) (glueSites x i j q) t H :=
    Finset.sum_congr rfl fun q _ => by
      rw [aM, mSeg_eq_mChain P σ x t hij.le, bGav_sub_bMav P σ x t H hij]
  rw [hsum]
  have h := glue_contract c hAP hpsi1 σ x hk hij _
    (fun q => hI _ hp (segPat σ i j) (segSites x i j) q)
    (mul_nonneg (hI0 _) (Real.sqrt_nonneg _))
  have hη := c.height_pos
  have e : P.lEta t ^ (-(lossBeta k - lossBeta (k - ((j : ℕ) - i) + 1))) *
      P.lEta t ^ lossBeta k * P.lEta t ^ (0 : ℝ) =
      P.lEta t ^ (1 / 2 : ℝ) * P.lEta t ^ lossBeta (k - ((j : ℕ) - i) + 1) *
        P.lEta t ^ (-(1 / 2 : ℝ)) := rpow_three c.lEta_pos (by ring)
  rw [Real.rpow_zero, mul_one] at e
  calc vsHeight P.z t * ‖∑ q, P.mChain (segPat σ i j) (segSites x i j) t q *
        P.avErr (gluePat σ i j) (glueSites x i j q) t H‖
      ≤ vsHeight P.z t * (I ((j : ℕ) - i + 1) * Real.sqrt (P.lEta t) *
          psiA (k - ((j : ℕ) - i) + 1) * P.lEta t ^ lossBeta (k - ((j : ℕ) - i) + 1) *
          (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv x t)) :=
        mul_le_mul_of_nonneg_left h hη.le
    _ = d.Cwc * I ((j : ℕ) - i + 1) * psiA (k - ((j : ℕ) - i) + 1) *
          (P.lEta t ^ (1 / 2 : ℝ) * P.lEta t ^ lossBeta (k - ((j : ℕ) - i) + 1) *
            P.lEta t ^ (-(1 / 2 : ℝ))) * P.sAv x t := by
        rw [Real.sqrt_eq_rpow]
        field_simp
    _ = _ := by rw [← e]; ring

omit hpsi1 in
/-- `‖𝒳¹(p)‖ ≤ ψ^A_1 s^av_1` (as a size function, `β_1 = 0`). -/
theorem norm_avErr_one_le' (j : Fin k) (p : Fin N) :
    ‖P.avErr (fun _ : Fin 1 => σ j) (fun _ : Fin 1 => p) t H‖ ≤
      psiA 1 * P.sAv (fun _ : Fin 1 => p) t := by
  have h := norm_avErr_le c hAP (mem_kRange le_rfl (by norm_num)) (fun _ : Fin 1 => σ j)
    (fun _ : Fin 1 => p)
  have hb : lossBeta 1 = 0 := by
    rw [lossBeta_eq (by norm_num), lossAlpha_eq_zero (by norm_num)]
  rwa [hb, Real.rpow_zero, mul_one] at h

/-- **F1**, one slot, `k ≤ 7`. -/
theorem slot_avF1 (hk7 : k ≤ 7) {E : ℝ} (hE : ExtraBAt P t k E) (j : Fin k) :
    vsHeight P.z t * ‖f1Term P σ x t H j‖ ≤
      (d.Cwc * (psiA 1 * psiI (k + 1) * P.lEta t ^ (-(1 / 2 : ℝ))) +
        E * (psiA 1 * P.lEta t ^ (-lossBeta k))) * (P.lEta t ^ lossBeta k * P.sAv x t) := by
  have hj := j.isLt
  have hk1 : k + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hL := c.lEta_pos
  have hη := c.height_pos
  have hpa := (hpsi1 1).2
  have hpi := (hpsi1 (k + 1)).1
  have hterm : ∀ p, ‖P.avErr (fun _ : Fin 1 => σ j) (fun _ : Fin 1 => p) t H *
      gChain (patZ P.z (rotPat σ j) t) (isoSlots P.S (rotSites x j)) H p p‖ ≤
      psiA 1 * psiI (k + 1) * P.lEta t ^ lossAlpha (k + 1) *
          (P.sAv (fun _ : Fin 1 => p) t * P.sIso p p (rotSites x j) t) +
        psiA 1 * (P.lEta t)⁻¹ * ‖P.mChain (rotPat σ j) (rotSites x j) t p‖ := by
    intro p
    rw [gChain_iso_eq, ite_eq_left rfl, norm_mul]
    have h1 := norm_avErr_one_le' c hAP σ j p
    rw [contr_sAv_one P rfl] at h1 ⊢
    have h2 := norm_isoErr_le c hAP hk1 (rotPat σ j) p p (rotSites x j)
    calc ‖P.avErr (fun _ : Fin 1 => σ j) (fun _ : Fin 1 => p) t H‖ *
          ‖P.isoErr (rotPat σ j) p p (rotSites x j) t H + P.mChain (rotPat σ j) (rotSites x j) t p‖
        ≤ psiA 1 * (P.lEta t)⁻¹ *
            (psiI (k + 1) * P.lEta t ^ lossAlpha (k + 1) * P.sIso p p (rotSites x j) t +
              ‖P.mChain (rotPat σ j) (rotSites x j) t p‖) :=
          mul_le_mul h1 ((norm_add_le _ _).trans (add_le_add h2 le_rfl)) (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hins := avInsertionI0_of P t (fun a b => (c.pos a b).le) hL d.one_le_C1pp
    (div_nonneg (by linarith [d.one_le_C1pp]) hη.le) c.maxU c.sqrtConvol (j := k) (by omega)
    (fun p _ => p) (rotSites x j) (fun n : Fin k => rotSites x j n.castSucc) (fun n hn => rfl)
  rw [sAv_rotSites P t x j] at hins
  have hins' : ∑ q, P.sAv (fun _ : Fin 1 => q) t * P.sIso q q (rotSites x j) t ≤
      d.Cwc * (vsHeight P.z t)⁻¹ * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv x t := by
    refine hins.trans (le_of_eq ?_)
    rw [← sqrt_mul_C1pp]
    ring
  have hext := hE (rotPat σ j) (rotPat_first_last σ j) (rotSites x j)
  rw [sAv_rotSites P t x j] at hext
  have hα : lossAlpha (k + 1) = lossBeta k := (lossBeta_eq hk7).symm
  calc vsHeight P.z t * ‖f1Term P σ x t H j‖
      ≤ vsHeight P.z t * ∑ p, (psiA 1 * psiI (k + 1) * P.lEta t ^ lossAlpha (k + 1) *
          (P.sAv (fun _ : Fin 1 => p) t * P.sIso p p (rotSites x j) t) +
        psiA 1 * (P.lEta t)⁻¹ * ‖P.mChain (rotPat σ j) (rotSites x j) t p‖) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ =>
          hterm p)) hη.le
    _ = vsHeight P.z t * (psiA 1 * psiI (k + 1) * P.lEta t ^ lossAlpha (k + 1) *
          ∑ p, P.sAv (fun _ : Fin 1 => p) t * P.sIso p p (rotSites x j) t +
        psiA 1 * (P.lEta t)⁻¹ * ∑ p, ‖P.mChain (rotPat σ j) (rotSites x j) t p‖) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ vsHeight P.z t * (psiA 1 * psiI (k + 1) * P.lEta t ^ lossAlpha (k + 1) *
          (d.Cwc * (vsHeight P.z t)⁻¹ * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv x t) +
        psiA 1 * (P.lEta t)⁻¹ * (E / vsHeight P.z t * P.lEta t * P.sAv x t)) := by
        gcongr
    _ = _ := by
        rw [hα]
        have e1 : P.lEta t ^ (-lossBeta k) * P.lEta t ^ lossBeta k = 1 := by
          rw [← Real.rpow_add hL]; simp
        field_simp
        rw [show P.lEta t ^ (-lossBeta k) = (P.lEta t ^ lossBeta k)⁻¹ from
          Real.rpow_neg hL.le _]
        field_simp

omit hAP hpsi1 in
/-- The `k = 1` forcing is `Σ_p 𝒳¹(p) 𝒴²(p, x_1, p)` of the constant length-2 pattern. -/
theorem forcingAv_one_eq (σ : Fin 1 → Bool) (x : Fin 1 → Fin N) :
    forcingAv P σ x t H = ∑ p, P.avErr (fun _ : Fin 1 => σ 0) (fun _ : Fin 1 => p) t H *
      P.isoErr (rotPat σ 0) p p (rotSites x 0) t H := by
  rw [forcingAv_one P c.stoch.symm σ x t H, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hG : slotsH P.z σ t H 0 * obsMat P.S (x 0) * slotsH P.z σ t H 0 =
      gChain (patZ P.z (rotPat σ 0) t) (isoSlots P.S (rotSites x 0)) H := by
    rw [← rot_gChain P σ x t H 0]
    simp [gHead, gTail, segProd_self, avSlots, Matrix.mul_assoc]
  have hM : mSelf P σ x t = P.mChain (rotPat σ 0) (rotSites x 0) t := by
    rw [mSelf, PsiData.mChain]
    refine chainM_shift (m := fun _ => patM P.z σ 1) (A := fun _ => Split.rowObs P.S (x 0))
      t P.S 0 (fun q hq hq' => ?_) (fun q hq hq' => ?_)
    · unfold patM
      rw [dite_eq_left ⟨hq, hq'⟩, dite_eq_left ⟨le_rfl, le_rfl⟩]
      simp only [rotPat]
      congr 2
      exact Subsingleton.elim _ _
    · unfold obsSeq
      rw [dite_eq_left ⟨hq, by omega⟩]
      simp only [rotSites]
      congr 2
      exact Subsingleton.elim _ _
  rw [Matrix.diag_apply, bandSelfEnergy, Matrix.diagonal_mul, hG, hM,
    ← avErr_one_eq P σ t H 0 p, PsiData.isoErr, ite_eq_left rfl, Matrix.sub_apply,
    Matrix.diagonal_apply_eq]

/-- **F1, `k = 1`**: `η |𝓕^av_{[1,1]}| ≤ C_wc ψ^A_1 ψ^I_2 L^{-1/2} · L^{β_1} s^av_1`. -/
theorem av_one (σ : Fin 1 → Bool) (x : Fin 1 → Fin N) :
    vsHeight P.z t * ‖forcingAv P σ x t H‖ ≤
      d.Cwc * (psiA 1 * psiI 2 * P.lEta t ^ (-(1 / 2 : ℝ))) *
        (P.lEta t ^ lossBeta 1 * P.sAv x t) := by
  have hL := c.lEta_pos
  have hη := c.height_pos
  have hpa := (hpsi1 1).2
  have hpi := (hpsi1 2).1
  have h2 : (2 : ℕ) ∈ kRange := mem_kRange (by norm_num) (by norm_num)
  have hb : lossBeta 1 = 0 := by
    rw [lossBeta_eq (by norm_num), lossAlpha_eq_zero (by norm_num)]
  have ha : lossAlpha 2 = 0 := lossAlpha_eq_zero (by norm_num)
  rw [forcingAv_one_eq c σ x, hb, Real.rpow_zero, one_mul]
  have hterm : ∀ p, ‖P.avErr (fun _ : Fin 1 => σ 0) (fun _ : Fin 1 => p) t H *
      P.isoErr (rotPat σ 0) p p (rotSites x 0) t H‖ ≤
      psiA 1 * psiI 2 * (P.sAv (fun _ : Fin 1 => p) t * P.sIso p p (rotSites x 0) t) := by
    intro p
    rw [norm_mul]
    have h1 := norm_avErr_one_le' c hAP σ 0 p
    have h3 := norm_isoErr_le c hAP h2 (rotPat σ 0) p p (rotSites x 0)
    rw [ha, Real.rpow_zero, mul_one] at h3
    calc _ ≤ psiA 1 * P.sAv (fun _ : Fin 1 => p) t * (psiI 2 * P.sIso p p (rotSites x 0) t) :=
          mul_le_mul h1 h3 (norm_nonneg _) (by have := sAv_pos c (fun _ : Fin 1 => p); positivity)
      _ = _ := by ring
  have hins := avInsertionI0_of P t (fun a b => (c.pos a b).le) hL d.one_le_C1pp
    (div_nonneg (by linarith [d.one_le_C1pp]) hη.le) c.maxU c.sqrtConvol (j := 1) le_rfl
    (fun p _ => p) (rotSites x 0) (fun n : Fin 1 => rotSites x 0 n.castSucc) (fun n hn => rfl)
  rw [sAv_rotSites P t x 0] at hins
  calc vsHeight P.z t * ‖∑ p, P.avErr (fun _ : Fin 1 => σ 0) (fun _ : Fin 1 => p) t H *
        P.isoErr (rotPat σ 0) p p (rotSites x 0) t H‖
      ≤ vsHeight P.z t * (psiA 1 * psiI 2 *
          ∑ p, P.sAv (fun _ : Fin 1 => p) t * P.sIso p p (rotSites x 0) t) := by
        rw [Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun p _ => hterm p)) hη.le
    _ ≤ vsHeight P.z t * (psiA 1 * psiI 2 * (Real.sqrt d.C1pp * (d.C1pp / vsHeight P.z t) *
          P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv x t)) := by
        gcongr
    _ = _ := by
        rw [← sqrt_mul_C1pp]
        field_simp

end Pairs

end BlockBand.Native.ErdosRiabov.Forcing
