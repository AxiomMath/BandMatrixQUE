module

public import BlockBand.Native.ErdosRiabov.Forcing.BoundAv

/-!
# Forcing bounds: the averaged FM1 family by `M`-cyclicity

The FM1 family of the averaged forcing is bounded after rotating the glued `M`-chain with the
cyclicity of `M`-traces.

* `rotK s f`: cyclic rotation `l ↦ f ((l + s) mod r)` of a pattern or of sites;
* `cycT`: `Σ_a M(σ', w)_a S_{w_{r-1}, a}`, the closed `M`-trace with its last observable;
  `cycT_rotK`: `cycT` is invariant under every rotation (from one application of
  `CyclicStatement`, `cycT_step`, and `rotK r = id`);
* `bMav_cyc`: the pairing `Tr[M^{(q)} S^{x_k}]` equals `Σ_a S_{qa} (M^{(x_k)}_{[j,i]})_{aa}`;
* `pair_avFM1`: `η |Σ_q (a_G - a_M) b_M| ≤ C_wc I_r ψ^A_p L^{-(β_k-β_p)} · L^{β_k} s^av_k`.
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
## Rotations
-/

/-- Cyclic rotation `l ↦ f ((l + s) mod r)`. -/
def rotK {α : Type*} {r : ℕ} (s : ℕ) (f : Fin r → α) : Fin r → α :=
  fun l => f ⟨((l : ℕ) + s) % r, Nat.mod_lt _ l.pos⟩

theorem rotK_rotK {α : Type*} {r : ℕ} (a b : ℕ) (f : Fin r → α) :
    rotK a (rotK b f) = rotK (a + b) f := by
  funext l
  simp only [rotK]
  congr 1
  apply Fin.ext
  simp only
  rw [Nat.mod_add_mod, add_assoc]

theorem rotK_self {α : Type*} {r : ℕ} (f : Fin r → α) : rotK r f = f := by
  funext l
  simp only [rotK]
  congr 1
  exact Fin.ext (by simp only; rw [Nat.add_mod_right, Nat.mod_eq_of_lt l.isLt])

theorem rotK_eq_comp {α : Type*} {r : ℕ} (s : ℕ) (f : Fin r → α) :
    rotK s f = fun l => f ((finRotate r ^ s) l) := by
  funext l
  simp only [rotK]
  congr 1
  exact Fin.ext (contr_finRotate_pow_val s l).symm

/-!
## The closed `M`-trace and its rotation invariance
-/

section Cyc

variable (P : PsiData N) (t : ℝ)

/-- `Σ_a M(σ', w)_a S_{w_l, a}`. -/
def cycT {r : ℕ} (σ' : Fin r → Bool) (w : Fin r → Fin N) (l : Fin r) : ℂ :=
  ∑ a, P.mChain σ' w t a * (P.S (w l) a : ℂ)

theorem prod_patM_eq {r : ℕ} (z : ℂ) (τ : Fin r → Bool) :
    ∏ p ∈ Finset.Icc 1 r, patM z τ p = ∏ l : Fin r, VS.patConj (τ l) (semicircleM z) := by
  rw [show Finset.Icc 1 r = (Finset.range r).map (addRightEmbedding 1) by
    rw [Finset.range_eq_Ico, Finset.map_add_right_Ico]
    ext p
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega, Finset.prod_map, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [addRightEmbedding_apply]
  exact patM_of_mem z τ l

theorem prod_patM_rotK {r : ℕ} (z : ℂ) (τ : Fin r → Bool) (s : ℕ) :
    ∏ p ∈ Finset.Icc 1 r, patM z (rotK s τ) p = ∏ p ∈ Finset.Icc 1 r, patM z τ p := by
  rw [prod_patM_eq, prod_patM_eq, rotK_eq_comp]
  exact Equiv.prod_comp (finRotate r ^ s) (fun l => VS.patConj (τ l) (semicircleM z))

theorem patM_rotK_pred {r : ℕ} (hr : 2 ≤ r) (z : ℂ) (τ : Fin r → Bool) {p : ℕ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ r) : patM z (rotK (r - 1) τ) p = Split.rotateChain r (patM z τ) p := by
  unfold Split.rotateChain patM
  rw [dite_eq_left ⟨hp1, hp2⟩]
  by_cases h1 : p = 1
  · subst h1
    rw [ite_eq_left rfl, dite_eq_left ⟨by omega, le_rfl⟩]
    simp only [rotK]
    congr 2
    exact Fin.ext (by simp only; rw [Nat.mod_eq_of_lt (by omega)]; omega)
  · rw [ite_eq_right h1, dite_eq_left ⟨by omega, by omega⟩]
    simp only [rotK]
    congr 2
    exact Fin.ext (by simp only; rw [mod_of_ge (by omega) (by omega)]; omega)

theorem obsSeq_rotK_pred {r : ℕ} (hr : 2 ≤ r) (w : Fin r → Fin N) {p : ℕ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ r) : obsSeq P.S (rotK (r - 1) w) p = Split.rotateChain r (obsSeq P.S w) p := by
  unfold Split.rotateChain obsSeq
  rw [dite_eq_left ⟨hp1, hp2⟩]
  by_cases h1 : p = 1
  · subst h1
    rw [ite_eq_left rfl, dite_eq_left ⟨by omega, le_rfl⟩]
    simp only [rotK]
    congr 2
    exact Fin.ext (by simp only; rw [Nat.mod_eq_of_lt (by omega)]; omega)
  · rw [ite_eq_right h1, dite_eq_left ⟨by omega, by omega⟩]
    simp only [rotK]
    congr 2
    exact Fin.ext (by simp only; rw [mod_of_ge (by omega) (by omega)]; omega)

/-- One application of `Split.CyclicStatement`: `cycT` is invariant under `rotK (r-1)`. -/
theorem cycT_step (hC : Split.CyclicStatement) (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {r : ℕ} (hr : 2 ≤ r) (σ' : Fin r → Bool)
    (w : Fin r → Fin N) :
    cycT P t σ' w ⟨r - 1, by omega⟩ =
      cycT P t (rotK (r - 1) σ') (rotK (r - 1) w) ⟨r - 1, by omega⟩ := by
  have hP : Split.ProfileHyp P.S := ⟨hS.nonneg, hS.symm, hS.rowSum⟩
  have hc := hC N P.S hP t ⟨ht0, ht1⟩ (patM P.z σ') (norm_patM_lt_one hz σ') (obsSeq P.S w) r hr
  have hT : Split.chainTilde t P.S (Split.rotateChain r (patM P.z σ'))
      (Split.rotateChain r (obsSeq P.S w)) 1 r =
      Split.chainTilde t P.S (patM P.z (rotK (r - 1) σ')) (obsSeq P.S (rotK (r - 1) w)) 1 r := by
    have h := chainTilde_shift (m := Split.rotateChain r (patM P.z σ'))
      (A := Split.rotateChain r (obsSeq P.S w)) (m' := patM P.z (rotK (r - 1) σ'))
      (A' := obsSeq P.S (rotK (r - 1) w)) t P.S 0 (r - 1) 1 r (by omega)
      (fun p hp hp' => patM_rotK_pred hr P.z σ' hp hp')
      (fun p hp hp' => obsSeq_rotK_pred P hr w hp hp'.le)
    simpa using h
  have hlast : obsSeq P.S w r = Split.rowObs P.S (w ⟨r - 1, by omega⟩) := by
    rw [obsSeq, dite_eq_left ⟨by omega, le_rfl⟩]
  have hprev : obsSeq P.S w (r - 1) = Split.rowObs P.S (rotK (r - 1) w ⟨r - 1, by omega⟩) := by
    rw [obsSeq, dite_eq_left ⟨by omega, by omega⟩]
    simp only [rotK]
    congr 2
    exact Fin.ext (by simp only; rw [mod_of_ge (by omega) (by omega)]; omega)
  unfold cycT
  simp only [PsiData.mChain, Split.chainM, Pi.smul_apply, smul_eq_mul]
  rw [prod_patM_rotK]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  rw [hlast, hprev, hT] at hc
  simp only [Split.rowObs] at hc
  rw [hc]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- `cycT` is invariant under every rotation. -/
theorem cycT_rotK (hC : Split.CyclicStatement) (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {r : ℕ} (hr : 2 ≤ r) (σ' : Fin r → Bool) (w : Fin r → Fin N)
    (s : ℕ) :
    cycT P t σ' w ⟨r - 1, by omega⟩ = cycT P t (rotK s σ') (rotK s w) ⟨r - 1, by omega⟩ := by
  have hone : ∀ (τ : Fin r → Bool) (u : Fin r → Fin N), cycT P t τ u ⟨r - 1, by omega⟩ =
      cycT P t (rotK 1 τ) (rotK 1 u) ⟨r - 1, by omega⟩ := by
    intro τ u
    have h := cycT_step P t hC hS hz ht0 ht1 hr (rotK 1 τ) (rotK 1 u)
    rw [rotK_rotK, rotK_rotK, show r - 1 + 1 = r by omega, rotK_self, rotK_self] at h
    exact h.symm
  induction s with
  | zero =>
    have h0 : ∀ {α : Type} (f : Fin r → α), rotK 0 f = f := fun f => by
      funext l
      simp only [rotK, add_zero, Nat.mod_eq_of_lt l.isLt]
    rw [h0, h0]
  | succ s ih =>
    rw [ih, hone, rotK_rotK, rotK_rotK, add_comm 1 s]

end Cyc

/-!
## The FM1 conversion
-/

section Conv

variable (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
  (H : Matrix (Fin N) (Fin N) ℂ)

/-- The rotated glued pattern `(σ_j, …, σ_{k-1}, σ_0, …, σ_i)`. -/
def glueRotPat (i j : Fin k) : Fin (k - ((j : ℕ) - i) + 1) → Bool :=
  rotK ((i : ℕ) + 1) (gluePat σ i j)

theorem rotK_glueSites (i j : Fin k) (q : Fin N) :
    rotK ((i : ℕ) + 1) (glueSites x i j q) = glueRot x i j q := by
  funext n
  simp only [rotK, glueRot, add_assoc]

/-- **The FM1 conversion** (given `CyclicStatement`): `Tr[M^{(q)} S^{x_k}] =
Σ_a S_{qa} (M^{(x_k)}_{[j,i]})_{aa}`, with the rotated glued chain. -/
theorem bMav_cyc (hC : Split.CyclicStatement) (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {i j : Fin k} (hij : i < j) (q : Fin N) :
    bMav P σ x t i j q =
      ∑ a, P.mChain (glueRotPat σ i j) (glueRot x i j q) t a * (P.S q a : ℂ) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  have hr : 2 ≤ k - ((j : ℕ) - i) + 1 := by omega
  have h := cycT_rotK P t hC hS hz ht0 ht1 hr (gluePat σ i j) (glueSites x i j q) ((i : ℕ) + 1)
  rw [rotK_glueSites] at h
  unfold cycT at h
  have hq : glueRot x i j q ⟨k - ((j : ℕ) - i) + 1 - 1, by omega⟩ = q := by
    have e : (⟨k - ((j : ℕ) - i) + 1 - 1, by omega⟩ : Fin (k - ((j : ℕ) - i) + 1)) =
        ⟨k - ((j : ℕ) - i), by omega⟩ :=
      Fin.ext (show k - ((j : ℕ) - i) + 1 - 1 = k - ((j : ℕ) - i) by omega)
    rw [e]
    exact glueRot_last x hij q
  rw [hq] at h
  rw [bMav, glueRotPat, ← h]
  have hl : obsSeq P.S x k =
      Split.rowObs P.S (glueSites x i j q ⟨k - ((j : ℕ) - i) + 1 - 1, by omega⟩) := by
    rw [obsSeq_last P.S x (l := ⟨k - 1, by omega⟩) (by simp only; omega),
      glueSites_of_gt x hij q _ (by simp only; omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  rw [hl]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mGlue_eq_mChain P σ x t hij]
  rfl

/-- The rotated glued `M`-term does not depend on the last (unused) site. -/
theorem mChain_glueRot_indep {i j : Fin k} (hij : i < j) (q q' : Fin N) :
    P.mChain (glueRotPat σ i j) (glueRot x i j q) t =
      P.mChain (glueRotPat σ i j) (glueRot x i j q') t := by
  have hij' : (i : ℕ) < j := hij
  unfold PsiData.mChain
  refine chainM_congr _ _ _ fun p hp hp' => ?_
  unfold obsSeq
  rw [dite_eq_left ⟨hp, by omega⟩, dite_eq_left ⟨hp, by omega⟩,
    glueRot_lt x hij q (p - 1) (by omega), glueRot_lt x hij q' (p - 1) (by omega)]

/-- `𝒳` of a chain with its last site set to `a` is the `S^a`-average of the diagonal `𝒴`. -/
theorem avErr_update_last {n : ℕ} (hn : 1 ≤ n) (τ : Fin n → Bool) (y : Fin n → Fin N)
    (a : Fin N) :
    P.avErr τ (update y ⟨n - 1, by omega⟩ a) t H =
      ∑ q, P.isoErr τ q q y t H * (P.S a q : ℂ) := by
  rw [avErr_last P τ y t H (l := ⟨n - 1, by omega⟩) (by simp only; omega) a]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hg : gHead (isoSlots P.S y) (slotsH P.z τ t H) ⟨n - 1, by omega⟩ =
      gChain (patZ P.z τ t) (isoSlots P.S y) H := by
    have h := slotProd_updateB_last (isoSlots P.S y) (slotsH P.z τ t H)
      (i := ⟨n - 1, by omega⟩) (by simp only; omega) 1
    have hu : update (isoSlots P.S y) ⟨n - 1, by omega⟩ 1 = isoSlots P.S y := by
      funext l
      by_cases hl : l = ⟨n - 1, by omega⟩
      · subst hl
        rw [update_self]
        unfold isoSlots
        rw [ite_eq_right (by simp only; omega)]
      · rw [update_of_ne hl]
    rw [hu, Matrix.mul_one] at h
    exact h.symm
  rw [hg, PsiData.isoErr, ite_eq_left rfl]

end Conv

/-!
## The FM1 pair bound
-/

section Pair

variable {d : VSData} {P : PsiData N} {t : ℝ} (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ}
  {psiI psiA : ℕ → ℝ} (hAP : APriori P t H psiI psiA)
  (hpsi1 : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) (σ : Fin k → Bool) (x : Fin k → Fin N)
include c hAP hpsi1

/-- **FM1**, one pair with `j - i ≤ k - 2` (given `CyclicStatement`). -/
theorem pair_avFM1 (hC : Split.CyclicStatement) (hk : k ≤ 8) {I : ℕ → ℝ}
    (hI : ∀ n ∈ kRange, IsoBAt P t n (I n)) (hI0 : ∀ n, 0 ≤ I n) {i j : Fin k} (hij : i < j) :
    vsHeight P.z t * ‖∑ q, (aG P σ t H (avSlots P.S x) i j q - aM P σ x t i j q) *
        bMav P σ x t i j q‖ ≤
      d.Cwc * I (k - ((j : ℕ) - i) + 1) * (psiA ((j : ℕ) - i + 1) *
          P.lEta t ^ (-(lossBeta k - lossBeta ((j : ℕ) - i + 1)))) *
        (P.lEta t ^ lossBeta k * P.sAv x t) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  have hp : (j : ℕ) - i + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hr : k - ((j : ℕ) - i) + 1 ∈ kRange := mem_kRange (by omega) (by omega)
  have hη := c.height_pos
  have hL := c.lEta_pos
  have hU : ∀ a b, 0 ≤ P.ups t a b := fun a b => (c.pos a b).le
  set q0 : Fin N := x ⟨0, j.pos⟩
  set M := P.mChain (glueRotPat σ i j) (glueRot x i j q0) t
  set yA : Fin N → Fin ((j : ℕ) - i + 1) → Fin N :=
    fun a => update (segSites x i j) ⟨(j : ℕ) - i + 1 - 1, by omega⟩ a
  -- the conversion
  have hconv : ∑ q, (aG P σ t H (avSlots P.S x) i j q - aM P σ x t i j q) *
      bMav P σ x t i j q = ∑ a, M a * P.avErr (segPat σ i j) (yA a) t H := by
    have h1 : ∀ q, bMav P σ x t i j q = ∑ a, M a * (P.S q a : ℂ) := fun q => by
      rw [bMav_cyc P σ x t hC c.stoch c.z_im.ne' c.t_nonneg c.t_le_one hij q,
        mChain_glueRot_indep P σ x t hij q q0]
    simp_rw [h1, aG_sub_aM_av P σ x t H hij.le, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [avErr_update_last P t H (by omega) (segPat σ i j) (segSites x i j) a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [c.stoch.symm a q]
    ring
  rw [hconv]
  have hM : ∀ a, ‖M a‖ ≤ I (k - ((j : ℕ) - i) + 1) * Real.sqrt (P.lEta t) *
      P.sIso a a (glueRot x i j q0) t := fun a => hI _ hr _ _ a
  have hE : ∀ a, ‖P.avErr (segPat σ i j) (yA a) t H‖ ≤
      psiA ((j : ℕ) - i + 1) * P.lEta t ^ lossBeta ((j : ℕ) - i + 1) * P.sAv (yA a) t :=
    fun a => norm_avErr_le c hAP hp (segPat σ i j) (yA a)
  let w : Fin (((j : ℕ) - i) + (k - ((j : ℕ) - i))) → Fin N :=
    fun n => x ⟨((n : ℕ) + i) % k, Nat.mod_lt _ j.pos⟩
  have hw : P.sAv w t = P.sAv x t := sAv_rot P t (by omega) w x i (fun l hl => rfl)
  have hins := avInsertion_of P t hU hL c.schwarz (i := (j : ℕ) - i) (j := k - ((j : ℕ) - i))
    (by omega) (by omega) yA (glueRot x i j q0) w
    (fun a => by
      simp only [yA]
      rw [show (⟨(j : ℕ) - i, by omega⟩ : Fin ((j : ℕ) - i + 1)) =
        ⟨(j : ℕ) - i + 1 - 1, by omega⟩ from Fin.ext (by simp only; omega), update_self])
    (fun a n hn => by
      simp only [yA, w]
      rw [update_of_ne (by simp only [ne_eq, Fin.mk.injEq]; omega), segSites_apply x hij.le]
      congr 1
      exact Fin.ext (by simp only; rw [Nat.mod_eq_of_lt (by omega)]; omega))
    (fun n hn => by
      simp only [w]
      rw [glueRot_lt x hij q0 n hn]
      congr 1
      exact Fin.ext (by simp only; rw [show (j : ℕ) - i + n + i = n + j by omega]))
  rw [hw] at hins
  have hpa : 0 ≤ psiA ((j : ℕ) - i + 1) := by linarith [(hpsi1 ((j : ℕ) - i + 1)).2]
  have hcoef : 0 ≤ I (k - ((j : ℕ) - i) + 1) * Real.sqrt (P.lEta t) *
      (psiA ((j : ℕ) - i + 1) * P.lEta t ^ lossBeta ((j : ℕ) - i + 1)) :=
    mul_nonneg (mul_nonneg (hI0 _) (Real.sqrt_nonneg _)) (mul_nonneg hpa (lEta_rpow_pos c _).le)
  have e : P.lEta t ^ (-(lossBeta k - lossBeta ((j : ℕ) - i + 1))) *
      P.lEta t ^ lossBeta k * P.lEta t ^ (0 : ℝ) =
      P.lEta t ^ (1 / 2 : ℝ) * P.lEta t ^ lossBeta ((j : ℕ) - i + 1) *
        P.lEta t ^ (-(1 / 2 : ℝ)) := rpow_three hL (by ring)
  rw [Real.rpow_zero, mul_one] at e
  calc vsHeight P.z t * ‖∑ a, M a * P.avErr (segPat σ i j) (yA a) t H‖
      ≤ vsHeight P.z t * (I (k - ((j : ℕ) - i) + 1) * Real.sqrt (P.lEta t) *
          (psiA ((j : ℕ) - i + 1) * P.lEta t ^ lossBeta ((j : ℕ) - i + 1)) *
          ∑ a, P.sAv (yA a) t * P.sIso a a (glueRot x i j q0) t) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) hη.le
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul]
        calc ‖M a‖ * ‖P.avErr (segPat σ i j) (yA a) t H‖
            ≤ (I (k - ((j : ℕ) - i) + 1) * Real.sqrt (P.lEta t) *
                P.sIso a a (glueRot x i j q0) t) *
              (psiA ((j : ℕ) - i + 1) * P.lEta t ^ lossBeta ((j : ℕ) - i + 1) *
                P.sAv (yA a) t) :=
              mul_le_mul (hM a) (hE a) (norm_nonneg _)
                (mul_nonneg (mul_nonneg (hI0 _) (Real.sqrt_nonneg _)) (sIso_pos c _ _ _).le)
          _ = _ := by ring
    _ ≤ vsHeight P.z t * (I (k - ((j : ℕ) - i) + 1) * Real.sqrt (P.lEta t) *
          (psiA ((j : ℕ) - i + 1) * P.lEta t ^ lossBeta ((j : ℕ) - i + 1)) *
          (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv x t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hins hcoef) hη.le
    _ = d.Cwc * I (k - ((j : ℕ) - i) + 1) * psiA ((j : ℕ) - i + 1) *
          (P.lEta t ^ (1 / 2 : ℝ) * P.lEta t ^ lossBeta ((j : ℕ) - i + 1) *
            P.lEta t ^ (-(1 / 2 : ℝ))) * P.sAv x t := by
        rw [Real.sqrt_eq_rpow]
        field_simp
    _ = _ := by rw [← e]; ring

end Pair

end BlockBand.Native.ErdosRiabov.Forcing
