module

public import BlockBand.Native.ErdosRiabov.Forcing.BoundAv

/-!
# Forcing bounds: the isotropic families

Bounds on the families FQ, FM1, FM2, the last line and F1 of the isotropic forcing. Per pair `i < j`
(segment length `p = j - i + 1`, glued length `r = k - (j - i) + 1`) and per
slot, normalized by `L^{α_k} s^iso_k(a,x',b)`:
* FQ: `≤ C_wc ψ^I_p ψ^I_r L^{-1/2}` (by `α_p + α_{k+2-p} ≤ α_k`);
* FM1: `≤ C_wc I_r ψ^I_p L^{-(α_k-α_p)}`; FM2: `≤ C_wc I_p ψ^I_r L^{-(α_k-α_r)}`;
* last line: `≤ (C₀+1+C_K C_wc) ψ^A_k L^{-(α_k-β_k)} L^{-1/2}`;
* F1, slot `j`: `≤ (C₁'' + (C₀+1)√C₁''(I_{j+1} + I_{k-j} + I_{j+1}I_{k-j}))
  (Y ψ^A_1 ψ^I_{j+1} ψ^I_{k-j} + ψ^A_1 L^{-1/2})` (by `α_j + α_{k-j+1} ≤ α_k`).
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

/-- `s^iso` across a length identity. -/
theorem sIso_congr (P : PsiData N) (t : ℝ) {n n' : ℕ} (h : n = n') (a b : Fin N)
    (u : Fin n → Fin N) (v : Fin n' → Fin N)
    (huv : ∀ (l : ℕ) (hl : l < n), u ⟨l, hl⟩ = v ⟨l, h ▸ hl⟩) :
    P.sIso a b u t = P.sIso a b v t := by
  subst h
  congr 1
  funext l
  exact huv l l.isLt

theorem glueSites_at (x : Fin k → Fin N) {i j : Fin k} (q : Fin N)
    (l : Fin (k - ((j : ℕ) - i) + 1)) (h : (l : ℕ) = i) : glueSites x i j q l = q := by
  unfold glueSites
  rw [ite_eq_right (by omega), ite_eq_left h]

section Pairs

variable {d : VSData} {P : PsiData N} {t : ℝ} (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ}
  {psiI psiA : ℕ → ℝ} (hAP : APriori P t H psiI psiA)
  (hpsi1 : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) (σ : Fin k → Bool) (x : Fin k → Fin N)
include c hAP hpsi1

omit hAP hpsi1 in
/-- The glued isotropic contraction behind the FQ, FM1 and FM2 bounds: `F(q)` bounded by
`f s^iso_p(q,seg,q)`,
`G(q)` by `g s^iso_r(a, glue q, b)`. -/
theorem iso_glue_contract {i j : Fin k} (hij : i < j) (a b : Fin N) (F G : Fin N → ℂ) {f g : ℝ}
    (hF : ∀ q, ‖F q‖ ≤ f * P.sIso q q (segSites x i j) t)
    (hG : ∀ q, ‖G q‖ ≤ g * P.sIso a b (glueSites x i j q) t) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    ‖∑ q, F q * G q‖ ≤ f * g * (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) *
      P.sIso a b x t) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  have hU : ∀ a b, 0 ≤ P.ups t a b := fun a b => (c.pos a b).le
  have hins := isoQuad_of P t hU c.lEta_pos c.schwarz (r := (i : ℕ)) (p := (j : ℕ) - i)
    (s := k - 1 - j) (by omega) a b (segSites x i j)
    (fun q n => glueSites x i j q ⟨n, by omega⟩) (fun n => x ⟨n, by omega⟩)
    (fun q n hn => glueSites_of_lt x q ⟨n, by omega⟩ hn)
    (fun q => glueSites_at x q _ rfl)
    (fun q n hn => by
      rw [glueSites_of_gt x hij q ⟨(i : ℕ) + 1 + n, by omega⟩
        (show (i : ℕ) < (i : ℕ) + 1 + n by omega)]
      congr 1
      exact Fin.ext (show (i : ℕ) + 1 + n + ((j : ℕ) - i) - 1 = (i : ℕ) + ((j : ℕ) - i) + n by
        omega))
    (fun n hn => by rw [segSites_apply x hij.le])
  have e1 : ∀ q, P.sIso a b (fun n : Fin ((i : ℕ) + (k - 1 - j) + 2) =>
      glueSites x i j q ⟨n, by omega⟩) t =
      P.sIso a b (glueSites x i j q) t := fun q =>
    sIso_congr P t (by omega) a b _ _ (fun l hl => rfl)
  have e2 : P.sIso a b (fun n : Fin ((i : ℕ) + ((j : ℕ) - i) + (k - 1 - j) + 1) =>
      x ⟨n, by omega⟩) t = P.sIso a b x t := sIso_congr P t (by omega) a b _ _ (fun l hl => rfl)
  simp only [e1, e2] at hins
  calc ‖∑ q, F q * G q‖ ≤ ∑ q, ‖F q‖ * ‖G q‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => norm_mul _ _))
    _ ≤ ∑ q, f * g * (P.sIso q q (segSites x i j) t * P.sIso a b (glueSites x i j q) t) :=
        Finset.sum_le_sum fun q _ => by
          calc ‖F q‖ * ‖G q‖ ≤ f * P.sIso q q (segSites x i j) t *
                (g * P.sIso a b (glueSites x i j q) t) :=
              mul_le_mul (hF q) (hG q) (norm_nonneg _) (mul_nonneg hf (sIso_pos c _ _ _).le)
            _ = _ := by ring
    _ = f * g * ∑ q, P.sIso q q (segSites x i j) t * P.sIso a b (glueSites x i j q) t := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hins (mul_nonneg hf hg)

/-- **FQ**, one pair. -/
theorem pair_isoFQ (hk : k ≤ 8) {i j : Fin k} (hij : i < j) (a b : Fin N) :
    vsHeight P.z t * ‖∑ q, (aG P σ t H (isoSlots P.S x) i j q - aM P σ x t i j q) *
        (bGiso P σ x t H a b i j q - bMiso P σ x t a b i j q)‖ ≤
      d.Cwc * (psiI ((j : ℕ) - i + 1) * psiI (k - ((j : ℕ) - i) + 1) *
        P.lEta t ^ (-(1 / 2 : ℝ))) * (P.lEta t ^ lossAlpha k * P.sIso a b x t) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  have hp : (j : ℕ) - i + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hr : k - ((j : ℕ) - i) + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hη := c.height_pos
  have hL := c.lEta_pos
  have hsum : ∑ q, (aG P σ t H (isoSlots P.S x) i j q - aM P σ x t i j q) *
        (bGiso P σ x t H a b i j q - bMiso P σ x t a b i j q) =
      ∑ q, P.isoErr (segPat σ i j) q q (segSites x i j) t H *
        P.isoErr (gluePat σ i j) a b (glueSites x i j q) t H :=
    Finset.sum_congr rfl fun q _ => by
      rw [aG_sub_aM_iso P σ x t H hij.le, bGiso_sub_bMiso P σ x t H hij]
  rw [hsum]
  have h := iso_glue_contract c x hij a b
    (fun q => P.isoErr (segPat σ i j) q q (segSites x i j) t H)
    (fun q => P.isoErr (gluePat σ i j) a b (glueSites x i j q) t H)
    (fun q => norm_isoErr_le c hAP hp (segPat σ i j) q q (segSites x i j))
    (fun q => norm_isoErr_le c hAP hr (gluePat σ i j) a b (glueSites x i j q))
    (mul_nonneg (by linarith [(hpsi1 ((j : ℕ) - i + 1)).1]) (lEta_rpow_pos c _).le)
    (mul_nonneg (by linarith [(hpsi1 (k - ((j : ℕ) - i) + 1)).1]) (lEta_rpow_pos c _).le)
  have hX4 := lossAlpha_add_le_X4 (p := (j : ℕ) - i + 1) (k := k) (by omega) (by omega) hk
  rw [show k + 2 - ((j : ℕ) - i + 1) = k - ((j : ℕ) - i) + 1 by omega] at hX4
  have hle : P.lEta t ^ lossAlpha ((j : ℕ) - i + 1) *
      P.lEta t ^ lossAlpha (k - ((j : ℕ) - i) + 1) ≤ P.lEta t ^ lossAlpha k := by
    rw [← Real.rpow_add hL]
    exact lEta_rpow_le c hX4
  have hs := sIso_pos c a b x
  have hpp : 0 ≤ psiI ((j : ℕ) - i + 1) * psiI (k - ((j : ℕ) - i) + 1) :=
    mul_nonneg (by linarith [(hpsi1 ((j : ℕ) - i + 1)).1])
      (by linarith [(hpsi1 (k - ((j : ℕ) - i) + 1)).1])
  calc _ ≤ vsHeight P.z t * (psiI ((j : ℕ) - i + 1) * P.lEta t ^ lossAlpha ((j : ℕ) - i + 1) *
          (psiI (k - ((j : ℕ) - i) + 1) * P.lEta t ^ lossAlpha (k - ((j : ℕ) - i) + 1)) *
          (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a b x t)) :=
        mul_le_mul_of_nonneg_left h hη.le
    _ = d.Cwc * (psiI ((j : ℕ) - i + 1) * psiI (k - ((j : ℕ) - i) + 1) *
          P.lEta t ^ (-(1 / 2 : ℝ))) * ((P.lEta t ^ lossAlpha ((j : ℕ) - i + 1) *
            P.lEta t ^ lossAlpha (k - ((j : ℕ) - i) + 1)) * P.sIso a b x t) := by
        field_simp
    _ ≤ _ := by
        gcongr
        exact mul_nonneg (by linarith [d.one_le_Cwc]) (mul_nonneg hpp (lEta_rpow_pos c _).le)

/-- **FM1**, one pair. -/
theorem pair_isoFM1 (hk : k ≤ 8) {I : ℕ → ℝ} (hI : ∀ n ∈ kRange, IsoBAt P t n (I n))
    (hI0 : ∀ n, 0 ≤ I n) {i j : Fin k} (hij : i < j) (a b : Fin N) :
    vsHeight P.z t * ‖∑ q, (aG P σ t H (isoSlots P.S x) i j q - aM P σ x t i j q) *
        bMiso P σ x t a b i j q‖ ≤
      d.Cwc * I (k - ((j : ℕ) - i) + 1) * (psiI ((j : ℕ) - i + 1) *
        P.lEta t ^ (-(lossAlpha k - lossAlpha ((j : ℕ) - i + 1)))) *
        (P.lEta t ^ lossAlpha k * P.sIso a b x t) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  have hp : (j : ℕ) - i + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hr : k - ((j : ℕ) - i) + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hη := c.height_pos
  have hL := c.lEta_pos
  have hsum : ∑ q, (aG P σ t H (isoSlots P.S x) i j q - aM P σ x t i j q) *
        bMiso P σ x t a b i j q =
      ∑ q, P.isoErr (segPat σ i j) q q (segSites x i j) t H * bMiso P σ x t a b i j q :=
    Finset.sum_congr rfl fun q _ => by rw [aG_sub_aM_iso P σ x t H hij.le]
  rw [hsum]
  have hG : ∀ q, ‖bMiso P σ x t a b i j q‖ ≤ I (k - ((j : ℕ) - i) + 1) *
      Real.sqrt (P.lEta t) * P.sIso a b (glueSites x i j q) t := by
    intro q
    rw [bMiso_eq P σ x t hij]
    split_ifs with hab
    · subst hab
      exact hI _ hr _ _ a
    · rw [norm_zero]
      exact mul_nonneg (mul_nonneg (hI0 _) (Real.sqrt_nonneg _)) (sIso_pos c _ _ _).le
  have h := iso_glue_contract c x hij a b
    (fun q => P.isoErr (segPat σ i j) q q (segSites x i j) t H)
    (fun q => bMiso P σ x t a b i j q)
    (fun q => norm_isoErr_le c hAP hp (segPat σ i j) q q (segSites x i j)) hG
    (mul_nonneg (by linarith [(hpsi1 ((j : ℕ) - i + 1)).1]) (lEta_rpow_pos c _).le)
    (mul_nonneg (hI0 _) (Real.sqrt_nonneg _))
  have e : P.lEta t ^ (-(lossAlpha k - lossAlpha ((j : ℕ) - i + 1))) *
      P.lEta t ^ lossAlpha k * P.lEta t ^ (0 : ℝ) =
      P.lEta t ^ lossAlpha ((j : ℕ) - i + 1) * P.lEta t ^ (1 / 2 : ℝ) *
        P.lEta t ^ (-(1 / 2 : ℝ)) := rpow_three hL (by ring)
  rw [Real.rpow_zero, mul_one] at e
  calc _ ≤ vsHeight P.z t * (psiI ((j : ℕ) - i + 1) * P.lEta t ^ lossAlpha ((j : ℕ) - i + 1) *
          (I (k - ((j : ℕ) - i) + 1) * Real.sqrt (P.lEta t)) *
          (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a b x t)) :=
        mul_le_mul_of_nonneg_left h hη.le
    _ = d.Cwc * I (k - ((j : ℕ) - i) + 1) * psiI ((j : ℕ) - i + 1) *
          (P.lEta t ^ lossAlpha ((j : ℕ) - i + 1) * P.lEta t ^ (1 / 2 : ℝ) *
            P.lEta t ^ (-(1 / 2 : ℝ))) * P.sIso a b x t := by
        rw [Real.sqrt_eq_rpow]
        field_simp
    _ = _ := by rw [← e]; ring

/-- **FM2**, one pair. -/
theorem pair_isoFM2 (hk : k ≤ 8) {I : ℕ → ℝ} (hI : ∀ n ∈ kRange, IsoBAt P t n (I n))
    (hI0 : ∀ n, 0 ≤ I n) {i j : Fin k} (hij : i < j) (a b : Fin N) :
    vsHeight P.z t * ‖∑ q, aM P σ x t i j q *
        (bGiso P σ x t H a b i j q - bMiso P σ x t a b i j q)‖ ≤
      d.Cwc * I ((j : ℕ) - i + 1) * (psiI (k - ((j : ℕ) - i) + 1) *
        P.lEta t ^ (-(lossAlpha k - lossAlpha (k - ((j : ℕ) - i) + 1)))) *
        (P.lEta t ^ lossAlpha k * P.sIso a b x t) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  have hp : (j : ℕ) - i + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hr : k - ((j : ℕ) - i) + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hη := c.height_pos
  have hL := c.lEta_pos
  have hsum : ∑ q, aM P σ x t i j q * (bGiso P σ x t H a b i j q - bMiso P σ x t a b i j q) =
      ∑ q, P.mChain (segPat σ i j) (segSites x i j) t q *
        P.isoErr (gluePat σ i j) a b (glueSites x i j q) t H :=
    Finset.sum_congr rfl fun q _ => by
      rw [aM, mSeg_eq_mChain P σ x t hij.le, bGiso_sub_bMiso P σ x t H hij]
  rw [hsum]
  have h := iso_glue_contract c x hij a b
    (fun q => P.mChain (segPat σ i j) (segSites x i j) t q)
    (fun q => P.isoErr (gluePat σ i j) a b (glueSites x i j q) t H)
    (fun q => hI _ hp (segPat σ i j) (segSites x i j) q)
    (fun q => norm_isoErr_le c hAP hr (gluePat σ i j) a b (glueSites x i j q))
    (mul_nonneg (hI0 _) (Real.sqrt_nonneg _))
    (mul_nonneg (by linarith [(hpsi1 (k - ((j : ℕ) - i) + 1)).1]) (lEta_rpow_pos c _).le)
  have e : P.lEta t ^ (-(lossAlpha k - lossAlpha (k - ((j : ℕ) - i) + 1))) *
      P.lEta t ^ lossAlpha k * P.lEta t ^ (0 : ℝ) =
      P.lEta t ^ lossAlpha (k - ((j : ℕ) - i) + 1) * P.lEta t ^ (1 / 2 : ℝ) *
        P.lEta t ^ (-(1 / 2 : ℝ)) := rpow_three hL (by ring)
  rw [Real.rpow_zero, mul_one] at e
  calc _ ≤ vsHeight P.z t * (I ((j : ℕ) - i + 1) * Real.sqrt (P.lEta t) *
          (psiI (k - ((j : ℕ) - i) + 1) * P.lEta t ^ lossAlpha (k - ((j : ℕ) - i) + 1)) *
          (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a b x t)) :=
        mul_le_mul_of_nonneg_left h hη.le
    _ = d.Cwc * I ((j : ℕ) - i + 1) * psiI (k - ((j : ℕ) - i) + 1) *
          (P.lEta t ^ lossAlpha (k - ((j : ℕ) - i) + 1) * P.lEta t ^ (1 / 2 : ℝ) *
            P.lEta t ^ (-(1 / 2 : ℝ))) * P.sIso a b x t := by
        rw [Real.sqrt_eq_rpow]
        field_simp
    _ = _ := by rw [← e]; ring

/-- **The isotropic last line** `δ_ab m_1 m_k Σ_q (I + tÂ_k)_{aq} 𝒳^k(x', q)`
(`k ≥ 2`). -/
theorem isoLast (hk : k ≤ 8) (hk2 : 2 ≤ k) (a b : Fin N) :
    vsHeight P.z t * ‖lastLine P σ x t H a b ⟨k - 1, by omega⟩‖ ≤
      (d.C0 + 1 + Propagator.vsCK d * d.Cwc) * (psiA k *
        P.lEta t ^ (-(lossAlpha k - lossBeta k)) * P.lEta t ^ (-(1 / 2 : ℝ))) *
        (P.lEta t ^ lossAlpha k * P.sIso a b x t) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hη := c.height_pos
  have hL := c.lEta_pos
  have hU : ∀ a b, 0 ≤ P.ups t a b := fun a b => (c.pos a b).le
  have hkR : k' + 1 ∈ kRange := mem_kRange (by omega) hk
  have hCK := (Propagator.vsCK_pos d).le
  have hpa : 0 ≤ psiA (k' + 1) := by linarith [(hpsi1 (k' + 1)).2]
  set l : Fin (k' + 1) := ⟨k' + 1 - 1, by omega⟩
  have hl : l = ⟨k', by omega⟩ := Fin.ext (by simp [l])
  have hcoef : ∀ q, ‖patM P.z σ 1 * patM P.z σ (k' + 1) *
      (1 + (t : ℂ) • aKer P σ l t) a q‖ ≤
      (if a = q then 1 else 0) + Propagator.vsCK d * P.ups t a q := by
    intro q
    have h1 := (norm_patM_lt_one c.z_im.ne' σ 1).le
    have h2 := (norm_patM_lt_one c.z_im.ne' σ (k' + 1)).le
    rw [norm_mul, norm_mul]
    have h3 : ‖(1 + (t : ℂ) • aKer P σ l t) a q‖ ≤
        (if a = q then 1 else 0) + Propagator.vsCK d * P.ups t a q := by
      rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [Matrix.one_apply]
        split_ifs <;> simp
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg c.t_nonneg]
        calc t * ‖aKer P σ l t a q‖ ≤ 1 * (Propagator.vsCK d * P.ups t a q) :=
              mul_le_mul c.t_le_one (c.kernel σ l a q) (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
    have h4 : 0 ≤ (if a = q then (1 : ℝ) else 0) + Propagator.vsCK d * P.ups t a q :=
      add_nonneg (by split_ifs <;> norm_num) (mul_nonneg hCK (hU _ _))
    calc ‖patM P.z σ 1‖ * ‖patM P.z σ (k' + 1)‖ * ‖(1 + (t : ℂ) • aKer P σ l t) a q‖
        ≤ 1 * 1 * ((if a = q then 1 else 0) + Propagator.vsCK d * P.ups t a q) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _)
            (by norm_num)
      _ = _ := by ring
  unfold lastLine
  split_ifs with hab
  · subst hab
    have hdiag := sAv_diag c (p := k') (by omega) a x (update x l a)
      (fun n hn => by rw [hl, update_of_ne (by simp [Fin.ext_iff]; omega)])
      (by rw [hl, update_self])
    have hav := isoAv_of P t hU c.symm hL c.schwarz (p := k') (by omega) a
      (fun q => update x l q) x (fun q => by rw [hl, update_self])
      (fun q n hn => by rw [hl, update_of_ne (by simp [Fin.ext_iff]; omega)])
    have hterm : ∀ q, ‖patM P.z σ 1 * patM P.z σ (k' + 1) *
        (1 + (t : ℂ) • aKer P σ l t) a q * P.avErr σ (update x l q) t H‖ ≤
        psiA (k' + 1) * P.lEta t ^ lossBeta (k' + 1) *
          ((if a = q then P.sAv (update x l q) t else 0) +
            Propagator.vsCK d * (P.ups t a q * P.sAv (update x l q) t)) := by
      intro q
      rw [norm_mul]
      have h1 := hcoef q
      have h2 := norm_avErr_le c hAP hkR σ (update x l q)
      have hs := sAv_pos c (update x l q)
      calc _ ≤ ((if a = q then 1 else 0) + Propagator.vsCK d * P.ups t a q) *
            (psiA (k' + 1) * P.lEta t ^ lossBeta (k' + 1) * P.sAv (update x l q) t) :=
            mul_le_mul h1 h2 (norm_nonneg _)
              (add_nonneg (by split_ifs <;> norm_num) (mul_nonneg hCK (hU _ _)))
        _ = _ := by split_ifs <;> ring
    have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) =>
      hterm q)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_univ _), ← Finset.mul_sum, hdiag] at hsum
    have hs := sIso_pos c a a x
    have hpl := lEta_rpow_pos c (lossBeta (k' + 1))
    calc vsHeight P.z t * ‖∑ q, patM P.z σ 1 * patM P.z σ (k' + 1) *
          (1 + (t : ℂ) • aKer P σ l t) a q * P.avErr σ (update x l q) t H‖
        ≤ vsHeight P.z t * (psiA (k' + 1) * P.lEta t ^ lossBeta (k' + 1) *
            (P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a a x t + Propagator.vsCK d *
              (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a a x t))) := by
          refine mul_le_mul_of_nonneg_left (hsum.trans ?_) hη.le
          gcongr
      _ = psiA (k' + 1) * (vsHeight P.z t + Propagator.vsCK d * d.Cwc) *
            (P.lEta t ^ lossBeta (k' + 1) * P.lEta t ^ (-(1 / 2 : ℝ))) * P.sIso a a x t := by
          field_simp
      _ ≤ psiA (k' + 1) * (d.C0 + 1 + Propagator.vsCK d * d.Cwc) *
            (P.lEta t ^ lossBeta (k' + 1) * P.lEta t ^ (-(1 / 2 : ℝ))) * P.sIso a a x t := by
          gcongr
          exact c.height_le
      _ = _ := by
          have e := rpow_three hL (a := -(lossAlpha (k' + 1) - lossBeta (k' + 1)))
            (b := -(1 / 2 : ℝ)) (c := lossAlpha (k' + 1)) (a' := lossBeta (k' + 1))
            (b' := -(1 / 2 : ℝ)) (c' := 0) (by ring)
          rw [Real.rpow_zero, mul_one] at e
          rw [← e]
          ring
  · rw [norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (add_nonneg (by linarith [d.C0_ge_one])
      (mul_nonneg hCK (by linarith [d.one_le_Cwc]))) (mul_nonneg (mul_nonneg hpa
      (lEta_rpow_pos c _).le) (lEta_rpow_pos c _).le))
      (mul_nonneg (lEta_rpow_pos c _).le (sIso_pos c _ _ _).le)

/-- The isotropic F1 slot term (`famF1`, entry `(a, b)`). -/
def f1IsoTerm (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) (j : Fin k) (a b : Fin N) : ℂ :=
  (gHead (isoSlots P.S x) (slotsH P.z σ t H) j *
    bandSelfEnergy P.S (slotsH P.z σ t H j - VS.patConj (σ j) (semicircleM P.z) • 1) *
    gTail (isoSlots P.S x) (slotsH P.z σ t H) j) a b

/-- **F1**, one slot `j` (including `j = 0` and `j = k-1`). -/
theorem slot_isoF1 (hk : k ≤ 8) {I : ℕ → ℝ} (hI : ∀ n ∈ kRange, IsoBAt P t n (I n))
    (hI0 : ∀ n, 0 ≤ I n) (j : Fin k) (a b : Fin N) :
    vsHeight P.z t * ‖f1IsoTerm P σ x t H j a b‖ ≤
      (d.C1pp + (d.C0 + 1) * Real.sqrt d.C1pp * (I ((j : ℕ) + 1) + I (k - j) +
          I ((j : ℕ) + 1) * I (k - j))) *
        (yScale P t * psiA 1 * psiI ((j : ℕ) + 1) * psiI (k - j)) *
        (P.lEta t ^ lossAlpha k * P.sIso a b x t) := by
  have hj := j.isLt
  have hη := c.height_pos
  have hL := c.lEta_pos
  have hU : ∀ a b, 0 ≤ P.ups t a b := fun a b => (c.pos a b).le
  have hj0 : (⟨0, j.pos⟩ : Fin k) ≤ j := by simp only [Fin.le_def]; omega
  have hjl : j ≤ (⟨k - 1, by omega⟩ : Fin k) := by simp only [Fin.le_def]; omega
  have hn1 : (j : ℕ) - ((⟨0, j.pos⟩ : Fin k) : ℕ) + 1 = (j : ℕ) + 1 := by simp
  have hn2 : ((⟨k - 1, by omega⟩ : Fin k) : ℕ) - j + 1 = k - j := by simp only; omega
  have h1R : (j : ℕ) + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have h2R : k - j ∈ kRange := mem_kRange (by omega) (by omega)
  -- the bounds on the two factors
  set d1 := psiI ((j : ℕ) + 1) * P.lEta t ^ lossAlpha ((j : ℕ) + 1) with hd1d
  set d2 := psiI (k - j) * P.lEta t ^ lossAlpha (k - j) with hd2d
  set c1 := I ((j : ℕ) + 1) * Real.sqrt (P.lEta t) with hc1d
  set c2 := I (k - j) * Real.sqrt (P.lEta t) with hc2d
  have hd1 : 0 ≤ d1 := mul_nonneg (by linarith [(hpsi1 ((j : ℕ) + 1)).1]) (lEta_rpow_pos c _).le
  have hd2 : 0 ≤ d2 := mul_nonneg (by linarith [(hpsi1 (k - j)).1]) (lEta_rpow_pos c _).le
  have hc1 : 0 ≤ c1 := mul_nonneg (hI0 _) (Real.sqrt_nonneg _)
  have hc2 : 0 ≤ c2 := mul_nonneg (hI0 _) (Real.sqrt_nonneg _)
  have hpa : 0 ≤ psiA 1 := by linarith [(hpsi1 1).2]
  have hA : ∀ p, ‖gHead (isoSlots P.S x) (slotsH P.z σ t H) j a p‖ ≤
      (d1 + if p = a then c1 else 0) * P.sIso a p (segSites x ⟨0, j.pos⟩ j) t := by
    intro p
    rw [gHead_iso_eq P σ x t H j]
    have h := norm_gChain_le c hAP (hn1 ▸ h1R) (hI _ (hn1 ▸ h1R)) (segPat σ ⟨0, j.pos⟩ j) a p
      (segSites x ⟨0, j.pos⟩ j)
    rw [congrArg psiI hn1, congrArg lossAlpha hn1, congrArg I hn1] at h
    refine h.trans (le_of_eq ?_)
    by_cases hap : a = p
    · subst hap; simp only [ite_true]; ring
    · simp only [hap, Ne.symm hap, ite_false]; ring
  have hB : ∀ p, ‖gTail (isoSlots P.S x) (slotsH P.z σ t H) j p b‖ ≤
      (d2 + if p = b then c2 else 0) * P.sIso p b (segSites x j ⟨k - 1, by omega⟩) t := by
    intro p
    rw [gTail_iso_eq P σ x t H j]
    have h := norm_gChain_le c hAP (hn2 ▸ h2R) (hI _ (hn2 ▸ h2R))
      (segPat σ j ⟨k - 1, by omega⟩) p b (segSites x j ⟨k - 1, by omega⟩)
    rw [congrArg psiI hn2, congrArg lossAlpha hn2, congrArg I hn2] at h
    refine h.trans (le_of_eq ?_)
    by_cases hpb : p = b
    · subst hpb; simp only [ite_true]; ring
    · simp only [hpb, ite_false]; ring
  -- pointwise bound
  have hpt : ∀ p, ‖P.avErr (fun _ : Fin 1 => σ j) (fun _ : Fin 1 => p) t H *
      (gHead (isoSlots P.S x) (slotsH P.z σ t H) j a p *
        gTail (isoSlots P.S x) (slotsH P.z σ t H) j p b)‖ ≤
      psiA 1 * (P.lEta t)⁻¹ * (d1 * d2 * (P.sIso a p (segSites x ⟨0, j.pos⟩ j) t *
          P.sIso p b (segSites x j ⟨k - 1, by omega⟩) t) +
        (if p = a then c1 * (d2 + c2) * (P.sIso a p (segSites x ⟨0, j.pos⟩ j) t *
          P.sIso p b (segSites x j ⟨k - 1, by omega⟩) t) else 0) +
        (if p = b then d1 * c2 * (P.sIso a p (segSites x ⟨0, j.pos⟩ j) t *
          P.sIso p b (segSites x j ⟨k - 1, by omega⟩) t) else 0)) := by
    intro p
    rw [norm_mul, norm_mul]
    have hE := norm_avErr_one_le c hAP (fun _ : Fin 1 => σ j) (fun _ : Fin 1 => p)
    have hs1 := sIso_pos c a p (segSites x ⟨0, j.pos⟩ j)
    have hs2 := sIso_pos c p b (segSites x j ⟨k - 1, by omega⟩)
    have hprod : (d1 + if p = a then c1 else 0) * (d2 + if p = b then c2 else 0) ≤
        d1 * d2 + (if p = a then c1 * (d2 + c2) else 0) + (if p = b then d1 * c2 else 0) := by
      split_ifs <;> nlinarith [mul_nonneg hc1 hc2, mul_nonneg hd1 hc2, mul_nonneg hc1 hd2,
        mul_nonneg hd1 hd2]
    have hss := mul_pos hs1 hs2
    have hf1 : 0 ≤ d1 + if p = a then c1 else 0 := add_nonneg hd1 (by split_ifs <;> simp [hc1])
    calc _ ≤ psiA 1 * (P.lEta t)⁻¹ *
          ((d1 + if p = a then c1 else 0) * P.sIso a p (segSites x ⟨0, j.pos⟩ j) t *
          ((d2 + if p = b then c2 else 0) * P.sIso p b (segSites x j ⟨k - 1, by omega⟩) t)) :=
          mul_le_mul hE (mul_le_mul (hA p) (hB p) (norm_nonneg _) (mul_nonneg hf1 hs1.le))
            (by positivity) (mul_nonneg hpa (inv_nonneg.mpr hL.le))
      _ = psiA 1 * (P.lEta t)⁻¹ * (((d1 + if p = a then c1 else 0) *
          (d2 + if p = b then c2 else 0)) * (P.sIso a p (segSites x ⟨0, j.pos⟩ j) t *
            P.sIso p b (segSites x j ⟨k - 1, by omega⟩) t)) := by ring
      _ ≤ psiA 1 * (P.lEta t)⁻¹ * ((d1 * d2 + (if p = a then c1 * (d2 + c2) else 0) +
          (if p = b then d1 * c2 else 0)) * (P.sIso a p (segSites x ⟨0, j.pos⟩ j) t *
            P.sIso p b (segSites x j ⟨k - 1, by omega⟩) t)) := by gcongr
      _ = _ := by split_ifs <;> ring
  -- contractions
  let w : Fin (((j : ℕ) - ((⟨0, j.pos⟩ : Fin k) : ℕ)) +
      (((⟨k - 1, by omega⟩ : Fin k) : ℕ) - j) + 1) → Fin N :=
    fun n => x ⟨n, by have := n.isLt; simp only at this; omega⟩
  have hw : P.sIso a b w t = P.sIso a b x t :=
    sIso_congr P t (by simp only; omega) a b w x (fun l hl => rfl)
  have hx1 : ∀ (n : ℕ) (hn : n < (j : ℕ) - ((⟨0, j.pos⟩ : Fin k) : ℕ)),
      segSites x ⟨0, j.pos⟩ j ⟨n, by omega⟩ = w ⟨n, by omega⟩ := by
    intro n hn
    rw [segSites_apply x hj0]
    congr 1
    exact Fin.ext (by simp)
  have hx2 : ∀ (n : ℕ) (hn : n < ((⟨k - 1, by omega⟩ : Fin k) : ℕ) - j),
      segSites x j ⟨k - 1, by omega⟩ ⟨n, by omega⟩ =
        w ⟨(j : ℕ) - ((⟨0, j.pos⟩ : Fin k) : ℕ) + n, by omega⟩ := by
    intro n hn
    rw [segSites_apply x hjl]
    congr 1
  have hconv := isoConvol_of P t hU hL c.sqrtConvolN a b (segSites x ⟨0, j.pos⟩ j)
    (segSites x j ⟨k - 1, by omega⟩) w hx1 hx2
  have hK : 0 ≤ d.C1pp / P.lEta t := div_nonneg (by linarith [d.one_le_C1pp]) hL.le
  have hcat := fun q => isoConcat_of P t hU hL hK c.triangle a b (segSites x ⟨0, j.pos⟩ j)
    (segSites x j ⟨k - 1, by omega⟩) w hx1 hx2 q
  rw [hw] at hconv
  simp only [hw] at hcat
  -- assembling
  set S := P.sIso a b x t
  set Ak := P.lEta t ^ lossAlpha k
  set A1 := P.lEta t ^ lossAlpha ((j : ℕ) + 1)
  set A2 := P.lEta t ^ lossAlpha (k - j)
  set u := P.lEta t ^ (-(1 / 2 : ℝ))
  set v := Real.sqrt (P.lEta t)
  set Y := yScale P t
  have hS : 0 < S := sIso_pos c a b x
  have hu : 0 < u := lEta_rpow_pos c _
  have hY : 0 < Y := yScale_pos c
  have hAk : 1 ≤ Ak := Real.one_le_rpow c.one_le_lEta (lossAlpha_nonneg k)
  have hA1 : A1 ≤ Ak := lEta_rpow_le c (lossAlpha_mono (by omega))
  have hA2 : A2 ≤ Ak := lEta_rpow_le c (lossAlpha_mono (by omega))
  have hA1p : 0 < A1 := lEta_rpow_pos c _
  have hA2p : 0 < A2 := lEta_rpow_pos c _
  have hX3 : A1 * A2 ≤ Ak := by
    have h := lossAlpha_add_le_X3 (j := (j : ℕ) + 1) (k := k) (by omega) (by omega) hk
    rw [show k - ((j : ℕ) + 1) + 1 = k - j by omega] at h
    rw [← Real.rpow_add hL]
    exact lEta_rpow_le c h
  have hLi : (P.lEta t)⁻¹ ≤ Y := inv_lEta_le_yScale c
  have huY : u ≤ Y := rpow_neg_half_le_yScale c
  have hLi0 : 0 < (P.lEta t)⁻¹ := inv_pos.mpr hL
  have huv : v * u = 1 := by
    simp only [v, u]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL]
    norm_num
  have hLv : (P.lEta t)⁻¹ * (v * v) = 1 := by
    simp only [v]
    rw [Real.mul_self_sqrt hL.le, inv_mul_cancel₀ hL.ne']
  have hsq : Real.sqrt (d.C1pp / P.lEta t) = Real.sqrt d.C1pp * u := by
    rw [div_eq_mul_inv, Real.sqrt_mul (by linarith [d.one_le_C1pp]), Real.sqrt_inv,
      Real.sqrt_eq_rpow (P.lEta t), ← Real.rpow_neg hL.le]
  rw [hsq] at hcat
  have hp1 := (hpsi1 ((j : ℕ) + 1)).1
  have hp2 := (hpsi1 (k - j)).1
  have hpa := (hpsi1 1).2
  have hC1 : 0 ≤ Real.sqrt d.C1pp := Real.sqrt_nonneg _
  have hI1 := hI0 ((j : ℕ) + 1)
  have hI2 := hI0 (k - j)
  set Z := Ak * Y * psiI ((j : ℕ) + 1) * psiI (k - j)
  have hZ1 : psiI (k - j) * A2 * (P.lEta t)⁻¹ ≤ Z := by
    have := mul_le_mul hA2 hLi hLi0.le (by linarith)
    calc psiI (k - j) * A2 * (P.lEta t)⁻¹ = 1 * psiI (k - j) * (A2 * (P.lEta t)⁻¹) := by ring
      _ ≤ psiI ((j : ℕ) + 1) * psiI (k - j) * (Ak * Y) := by gcongr
      _ = Z := by ring
  have hZ2 : psiI ((j : ℕ) + 1) * A1 * (P.lEta t)⁻¹ ≤ Z := by
    have := mul_le_mul hA1 hLi hLi0.le (by linarith)
    calc psiI ((j : ℕ) + 1) * A1 * (P.lEta t)⁻¹ =
          psiI ((j : ℕ) + 1) * 1 * (A1 * (P.lEta t)⁻¹) := by ring
      _ ≤ psiI ((j : ℕ) + 1) * psiI (k - j) * (Ak * Y) := by gcongr
      _ = Z := by ring
  have hZ3 : u ≤ Z := by
    calc u = 1 * 1 * (1 * u) := by ring
      _ ≤ psiI ((j : ℕ) + 1) * psiI (k - j) * (Ak * Y) := by gcongr
      _ = Z := by ring
  have hmain : ‖f1IsoTerm P σ x t H j a b‖ ≤ psiA 1 * (P.lEta t)⁻¹ *
      (psiI ((j : ℕ) + 1) * A1 * (psiI (k - j) * A2) *
          (d.C1pp / vsHeight P.z t * Real.sqrt ((N : ℝ) * vsHeight P.z t) * S) +
        I ((j : ℕ) + 1) * v * (psiI (k - j) * A2 + I (k - j) * v) *
          (Real.sqrt d.C1pp * u * S) +
        psiI ((j : ℕ) + 1) * A1 * (I (k - j) * v) * (Real.sqrt d.C1pp * u * S)) := by
    unfold f1IsoTerm
    rw [famF1_iso_term P σ x t H j a b]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun p _ => hpt p).trans ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _),
      ← Finset.mul_sum]
    have hc1d2 : 0 ≤ c1 * (d2 + c2) := mul_nonneg hc1 (add_nonneg hd2 hc2)
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hconv (mul_nonneg hd1 hd2))
      (mul_le_mul_of_nonneg_left (hcat a) hc1d2))
      (mul_le_mul_of_nonneg_left (hcat b) (mul_nonneg hd1 hc2)))
      (mul_nonneg (by linarith) hLi0.le)
  have hY' : Y = Real.sqrt ((N : ℝ) * vsHeight P.z t) / P.lEta t := rfl
  have e1 : vsHeight P.z t * (psiA 1 * (P.lEta t)⁻¹ *
      (psiI ((j : ℕ) + 1) * A1 * (psiI (k - j) * A2) *
          (d.C1pp / vsHeight P.z t * Real.sqrt ((N : ℝ) * vsHeight P.z t) * S))) =
      d.C1pp * (Y * psiA 1 * psiI ((j : ℕ) + 1) * psiI (k - j)) * (A1 * A2) * S := by
    rw [hY']
    field_simp
  have e23 : vsHeight P.z t * (psiA 1 * (P.lEta t)⁻¹ *
      (I ((j : ℕ) + 1) * v * (psiI (k - j) * A2 + I (k - j) * v) *
          (Real.sqrt d.C1pp * u * S) +
        psiI ((j : ℕ) + 1) * A1 * (I (k - j) * v) * (Real.sqrt d.C1pp * u * S))) =
      vsHeight P.z t * Real.sqrt d.C1pp * psiA 1 *
          (I ((j : ℕ) + 1) * (psiI (k - j) * A2 * (P.lEta t)⁻¹) +
            I (k - j) * (psiI ((j : ℕ) + 1) * A1 * (P.lEta t)⁻¹) +
            I ((j : ℕ) + 1) * I (k - j) * u) * S := by
    linear_combination (vsHeight P.z t * psiA 1 * Real.sqrt d.C1pp * S *
      ((P.lEta t)⁻¹ * I ((j : ℕ) + 1) * psiI (k - j) * A2 +
        (P.lEta t)⁻¹ * psiI ((j : ℕ) + 1) * A1 * I (k - j))) * huv +
      (vsHeight P.z t * psiA 1 * Real.sqrt d.C1pp * S * I ((j : ℕ) + 1) * I (k - j) * u) * hLv
  have hM : 0 ≤ Y * psiA 1 * psiI ((j : ℕ) + 1) * psiI (k - j) := by positivity
  have hp1' : d.C1pp * (Y * psiA 1 * psiI ((j : ℕ) + 1) * psiI (k - j)) * (A1 * A2) * S ≤
      d.C1pp * (Y * psiA 1 * psiI ((j : ℕ) + 1) * psiI (k - j)) * Ak * S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX3
      (mul_nonneg (by linarith [d.one_le_C1pp]) hM)) hS.le
  have hinner : I ((j : ℕ) + 1) * (psiI (k - j) * A2 * (P.lEta t)⁻¹) +
      I (k - j) * (psiI ((j : ℕ) + 1) * A1 * (P.lEta t)⁻¹) + I ((j : ℕ) + 1) * I (k - j) * u ≤
      I ((j : ℕ) + 1) * Z + I (k - j) * Z + I ((j : ℕ) + 1) * I (k - j) * Z :=
    add_le_add (add_le_add (mul_le_mul_of_nonneg_left hZ1 hI1)
      (mul_le_mul_of_nonneg_left hZ2 hI2)) (mul_le_mul_of_nonneg_left hZ3 (mul_nonneg hI1 hI2))
  have hin0 : 0 ≤ I ((j : ℕ) + 1) * (psiI (k - j) * A2 * (P.lEta t)⁻¹) +
      I (k - j) * (psiI ((j : ℕ) + 1) * A1 * (P.lEta t)⁻¹) + I ((j : ℕ) + 1) * I (k - j) * u := by
    positivity
  have hp2' : vsHeight P.z t * Real.sqrt d.C1pp * psiA 1 *
      (I ((j : ℕ) + 1) * (psiI (k - j) * A2 * (P.lEta t)⁻¹) +
        I (k - j) * (psiI ((j : ℕ) + 1) * A1 * (P.lEta t)⁻¹) +
        I ((j : ℕ) + 1) * I (k - j) * u) * S ≤
      (d.C0 + 1) * Real.sqrt d.C1pp * psiA 1 *
        (I ((j : ℕ) + 1) * Z + I (k - j) * Z + I ((j : ℕ) + 1) * I (k - j) * Z) * S := by
    apply mul_le_mul_of_nonneg_right _ hS.le
    apply mul_le_mul _ hinner hin0
      (mul_nonneg (mul_nonneg (by linarith [d.C0_ge_one]) hC1) (by linarith))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c.height_le hC1) (by linarith)
  calc vsHeight P.z t * ‖f1IsoTerm P σ x t H j a b‖
      ≤ _ := mul_le_mul_of_nonneg_left hmain hη.le
    _ = d.C1pp * (Y * psiA 1 * psiI ((j : ℕ) + 1) * psiI (k - j)) * (A1 * A2) * S +
        vsHeight P.z t * Real.sqrt d.C1pp * psiA 1 *
          (I ((j : ℕ) + 1) * (psiI (k - j) * A2 * (P.lEta t)⁻¹) +
            I (k - j) * (psiI ((j : ℕ) + 1) * A1 * (P.lEta t)⁻¹) +
            I ((j : ℕ) + 1) * I (k - j) * u) * S := by
        rw [← e1, ← e23]
        ring
    _ ≤ _ := add_le_add hp1' hp2'
    _ = _ := by simp only [Z]; ring

end Pairs

end BlockBand.Native.ErdosRiabov.Forcing
