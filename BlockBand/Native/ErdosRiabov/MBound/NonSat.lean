module

public import BlockBand.Native.ErdosRiabov.MBound.Sat

/-!
# The non-saturated averaged `M`-bound

For patterns with a non-saturated factor, the averaged `M`-term is bounded by the Duhamel formula
with the good propagator.

* `mb_goodProp_apply`: the signed `propOp` form of the good-propagator bound at any
  non-saturated position;
* **`mbBounds_nonsat_av`**: for `k = n+3 ≥ 3`, `HasDesatFactor σ`, the induction
  hypothesis and `t ∈ [0,1]`: `|Tr[M^σ_t](x)| ≤ C_P^k (B₀ + Λ F_k) ℓ_tη_t s^av_{k,t}(x)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators

variable {N : ℕ}

/-- `A^ns_k = C_P^k (B₀ + Λ C_wc ΣIA)`. -/
def mbAns (d : VSData) (Λ : ℝ) (k : ℕ) (A I : ℕ → ℝ) (B₀ : ℝ) : ℝ :=
  kernelActionConst d ^ k * (B₀ + Λ * (d.Cwc * mbFPairSum k A I))

theorem mb_kernel_factor (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (a b : Bool) (t : ℝ) :
    vsKernel S (VS.patConj a (semicircleM z)) (VS.patConj b (semicircleM z)) t =
      vsKernel S ((propFactorOfBits a b).mu1 z) ((propFactorOfBits a b).mu2 z) t := by
  cases a <;> cases b <;>
    simp [VS.patConj, propFactorOfBits, PropFactor.mu1, PropFactor.mu2, vsKernel_swap]

/-- `Evol.aKer P σ j t = vsKernel S μ_j μ'_j t` with the factor `propFactorOf σ j`. -/
theorem aKer_eq_factor (P : PsiData N) {k : ℕ} (σ : Fin k → Bool) (j : Fin k) (t : ℝ) :
    aKer P σ j t = vsKernel P.S ((propFactorOf σ j).mu1 P.z) ((propFactorOf σ j).mu2 P.z) t := by
  have hj := j.isLt
  have h1 : patM P.z σ ((j : ℕ) + 1) = VS.patConj (σ j) (semicircleM P.z) :=
    patM_of_mem P.z σ j
  have h2 : patM P.z σ (nextIdx j) = VS.patConj (patNext σ j) (semicircleM P.z) := by
    unfold nextIdx patNext
    by_cases h : (j : ℕ) + 1 < k
    · rw [ite_eq_left h, dite_eq_left h, mb_patM_apply _ _ (by omega) (by omega)]
      congr 2
    · rw [ite_eq_right h, dite_eq_right h, mb_patM_apply _ _ le_rfl (by omega)]
  rw [aKer, h1, h2, mb_kernel_factor]
  rfl

theorem mbAvGen_eq_propOp (P : PsiData N) {k : ℕ} (σ : Fin k → Bool) (x : Fin k → Fin N)
    (t : ℝ) :
    mbAvGen P σ x t = propOp (vsTensorGen P.S (fun j => (propFactorOf σ j).mu1 P.z)
      (fun j => (propFactorOf σ j).mu2 P.z) t) (fun y => avM P σ y t) x := by
  rw [propOp_vsTensorGen_apply, mbAvGen]
  simp only [aKer_eq_factor]

section Bound

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

include hc in
/-- The signed `propOp` form of the good-propagator bound (any position `j` with a non-saturated
factor). -/
theorem mb_goodProp_apply {n : ℕ} (c : Fin (n + 2) → PropFactor) (j : Fin (n + 2))
    (hj : c j ≠ .sat) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) {φ : ℝ} (hφ : 0 ≤ φ)
    (g : (Fin (n + 2) → Fin (m * W)) → ℂ) (hg : ∀ y, ‖g y‖ ≤ φ * P.sAv y s)
    (x : Fin (n + 2) → Fin (m * W)) :
    ‖propOp (goodProp P.S P.z c s t) g x‖ ≤
      kernelActionConst d ^ (n + 2) * φ * (P.lEta t / P.lEta s) * P.sAv x t := by
  have h := goodProps_av_any d hc.hm hc.hW P hc.hPW hc.hPD hc.hz hs0 hst ht1 c j hj x
  rw [← hc.hPS] at h
  rw [propOp_apply]
  calc ‖∑ y, goodProp P.S P.z c s t x y * g y‖ ≤
        ∑ y, ‖goodProp P.S P.z c s t x y‖ * (φ * P.sAv y s) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hg y) (norm_nonneg _))
    _ = φ * ∑ y, ‖goodProp P.S P.z c s t x y‖ * P.sAv y s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ φ * (kernelActionConst d ^ (n + 2) * (P.lEta t / P.lEta s) * P.sAv x t) :=
        mul_le_mul_of_nonneg_left h hφ
    _ = _ := by ring

include hA hc in
theorem mb_hasDerivAt_X_gen {n : ℕ} (σ : Fin (n + 3) → Bool) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => fun x => avM P σ x r)
      (propOp (vsTensorGen P.S (fun j => (propFactorOf σ j).mu1 P.z)
        (fun j => (propFactorOf σ j).mu2 P.z) s) (fun x => avM P σ x s) +
          fun x => mbFM P σ x s) s := by
  rw [hasDerivAt_pi]
  intro x
  have h := hasDerivAt_avM P hA.deriv hc.zpos.ne' hc.stoch (by omega) σ x hs
  rw [mbAvM_evol P σ x s hc.stoch.symm (by omega), mbAvGen_eq_propOp] at h
  exact h.congr_deriv (by simp only [Pi.add_apply])

include hA hc in
theorem mb_contOn_F_gen {n : ℕ} (σ : Fin (n + 3) → Bool) :
    ContinuousOn (fun r => fun x => mbFM P σ x r) (Icc (0 : ℝ) 1) := by
  have hX : ContinuousOn (fun r => fun x => avM P σ x r) (Icc (0 : ℝ) 1) := fun _ hr =>
    (mb_hasDerivAt_X_gen hA hc σ hr).continuousAt.continuousWithinAt
  have hK : ∀ (j : Fin (n + 3)) (a b : Fin (m * W)),
      ContinuousOn (fun r => aKer P σ j r a b) (Icc (0 : ℝ) 1) := fun j a b r hr => by
    rw [show (fun r => aKer P σ j r a b) = fun r => vsKernel P.S ((propFactorOf σ j).mu1 P.z)
      ((propFactorOf σ j).mu2 P.z) r a b from funext fun r => by rw [aKer_eq_factor]]
    exact (hasDerivAt_vsKernel hc.stoch (norm_smul_lt_one (mb_norm_mu1_lt hc.zpos _)
      (mb_norm_mu2_lt hc.zpos _) hr.1 hr.2) a b).continuousAt.continuousWithinAt
  have he : (fun r => fun x => mbFM P σ x r) = fun r => fun x =>
      dMav P σ x r - mbAvGen P σ x r := by
    funext r x
    rw [mbAvM_evol P σ x r hc.stoch.symm (by omega)]
    ring
  rw [he]
  refine continuousOn_pi.2 fun x => ContinuousOn.sub
    (continuousOn_dMav P hc.zpos.ne' hc.stoch σ x) ?_
  unfold mbAvGen
  exact continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun q _ =>
    (hK j _ _).mul (mb_contOn_coord hX _)

include hA hc in

/-- **The averaged `M`-bounds for non-saturated patterns** (under `Split.DerivStatement` and
the initial bound `hInit`): for `k = n+3`, a pattern with a non-saturated factor, the
induction hypothesis and `t ∈ [0,1]`,
`|Tr[M^{(t)}_{[1,k]} S^{x_k}](x)| ≤ C_P^k (B₀ + Λ C_wc ΣIA) ℓ_tη_t s^av_{k,t}(x)`.
-/
theorem mbBounds_nonsat_av {n : ℕ} (σ : Fin (n + 3) → Bool) (hσ : HasDesatFactor σ)
    (A I : ℕ → ℝ) (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 3 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 3 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 3) → Fin (m * W)) :
    ‖avM P σ x t‖ ≤ mbAns d (mbLambda d (m * W)) (n + 3) A I B₀ * (P.lEta t * P.sAv x t) := by
  obtain ⟨j, hj⟩ := hσ
  have hjs : propFactorOf σ j ≠ .sat := (propFactorOf_ne_sat_iff σ j).mpr hj
  have hΛ0 : 0 ≤ mbLambda d (m * W) :=
    mbLambda_nonneg d (Nat.mul_pos (by have := hc.hm; omega) hc.hW)
  have hP := mbFPairSum_nonneg (k := n + 3) hA0 hI0
  have hCP := kernelActionConst_ge_one d
  have hCwc := d.one_le_Cwc
  have hFcont := mb_contOn_F_gen hA hc σ
  have hint : IntervalIntegrable (fun s => propOp (goodProp P.S P.z (propFactorOf σ) s t)
      (fun x => mbFM P σ x s)) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
    refine ContinuousOn.clm_apply (fun s hs => ?_) (hFcont.mono hsub)
    exact (hasDerivAt_propOp_vsTensorProp_left hc.stoch (fun _ => mb_norm_mu1_lt hc.zpos _)
      (fun _ => mb_norm_mu2_lt hc.zpos _) hs.1 (hs.2.trans ht.2) ht.1 ht.2
      ).continuousAt.continuousWithinAt
  have hdu := vsTensorProp_duhamel (X := fun r => fun x => avM P σ x r) hc.stoch
    (fun _ => mb_norm_mu1_lt hc.zpos _) (fun _ => mb_norm_mu2_lt hc.zpos _) le_rfl zero_le_one
    ht.1 ht.2 (fun s hs => by
      rw [uIcc_of_le ht.1] at hs
      exact mb_hasDerivAt_X_gen hA hc σ ⟨hs.1, hs.2.trans ht.2⟩) hint
  have hdux := congrFun hdu x
  have hL0 := (hc.inputs (t := 0) ⟨le_rfl, zero_le_one⟩).lEta_pos
  have h0 : ‖propOp (goodProp P.S P.z (propFactorOf σ) 0 t) (fun x => avM P σ x 0) x‖ ≤
      kernelActionConst d ^ (n + 3) * B₀ * (P.lEta t * P.sAv x t) := by
    refine (mb_goodProp_apply hc (n := n + 1) _ j hjs le_rfl ht.1 ht.2
      (mul_nonneg hB₀ hL0.le) _ (fun y => (hInit y).trans (le_of_eq (by ring))) x).trans
      (le_of_eq ?_)
    field_simp
  have hb : ∀ s ∈ Icc (0 : ℝ) t, ‖propOp (goodProp P.S P.z (propFactorOf σ) s t)
      (fun x => mbFM P σ x s) x‖ ≤
      (kernelActionConst d ^ (n + 3) * (d.Cwc * mbFPairSum (n + 3) A I) *
        (P.lEta t * P.sAv x t)) * (vsHeight P.z s)⁻¹ := by
    intro s hs
    have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    have hins := hc.inputs hs1
    have hηs := hins.height_pos
    have hLs := hins.lEta_pos
    have hF := mbFM_bound P hs1 hins A I hA0 hI0 (fun n' h3 h4 => hAv n' h3 h4) hIso σ
    have hφ : 0 ≤ d.Cwc / vsHeight P.z s * mbFPairSum (n + 3) A I * P.lEta s :=
      mul_nonneg (mul_nonneg (div_nonneg (by linarith) hηs.le) hP) hLs.le
    refine (mb_goodProp_apply hc (n := n + 1) _ j hjs hs.1 hs.2 ht.2 hφ _
      (fun y => (hF y).trans (le_of_eq (by ring))) x).trans (le_of_eq ?_)
    field_simp
  have hI := mb_norm_integral_le hc.zpos ht hint x hb
  have hΛ : ∫ s in (0 : ℝ)..t, (vsHeight P.z s)⁻¹ ≤ mbLambda d (m * W) :=
    (vsIntRules (Nat.mul_pos (by have := hc.hm; omega) hc.hW) hc.hW d.delta0_pos.le
      d.kappa_pos (by linarith [d.C0_ge_one]) hc.hz ht.1 ht.2 one_pos).1
  have hLx := mb_LsAv_pos_nonneg hc ht x
  have hc0 : 0 ≤ kernelActionConst d ^ (n + 3) * (d.Cwc * mbFPairSum (n + 3) A I) *
      (P.lEta t * P.sAv x t) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (by linarith) hP)) hLx
  rw [hdux, Pi.add_apply]
  calc _ ≤ kernelActionConst d ^ (n + 3) * B₀ * (P.lEta t * P.sAv x t) +
        kernelActionConst d ^ (n + 3) * (d.Cwc * mbFPairSum (n + 3) A I) *
          (P.lEta t * P.sAv x t) * ∫ s in (0 : ℝ)..t, (vsHeight P.z s)⁻¹ :=
      (norm_add_le _ _).trans (add_le_add h0 hI)
    _ ≤ kernelActionConst d ^ (n + 3) * B₀ * (P.lEta t * P.sAv x t) +
        kernelActionConst d ^ (n + 3) * (d.Cwc * mbFPairSum (n + 3) A I) *
          (P.lEta t * P.sAv x t) * mbLambda d (m * W) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hΛ hc0)
    _ = _ := by
      unfold mbAns
      ring

end Bound

end BlockBand.Native.ErdosRiabov.MBound
