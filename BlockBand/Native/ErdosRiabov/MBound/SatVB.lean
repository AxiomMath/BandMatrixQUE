module

public import BlockBand.Native.ErdosRiabov.MBound.SatV

/-!
# The bound on the linear term

The linear term `T̂^{(J)}_t X_t` of a saturated averaged `M`-term is bounded by
`V_k η_t⁻¹ L_t s^av_t`.

* `mbV_init_bound`: `|P̃_{0,t} T̂^{(J)}_t X_0| ≤ C_K C_wc C_P^k B₀ η_t⁻¹ L_t s^av_t`
  (the good-propagator bound and `mb_thetaAction`);
* `mbV_integrand_bound`: for `s ∈ [0,t]`, `|P̃_{s,t} T̂^{(J)}_t (T̂^{(J')}_s X_s + F_s)|
  ≤ (C_K C_wc C_P^k F_k + C_P^{k+1}(Z_k + R_k)) η_t⁻¹ L_t s^av_t · η_s⁻¹` (with the split
  `T̂_t = P̂_{s,t} T̂_s`, the good-propagator bound, `mb_P5Action`, `mb_thetaAction`,
  `mbFM_bound`, `mbZ_bound` and `mbRem_bound`);
* **`mbV_bound`**: `|T̂^{(J)}_t X_t(x)| ≤ V_k η_t⁻¹ L_t s^av_t(x)`.
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

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

theorem mb_vb_alg {a b c e Q Lt S ηs ηt : ℝ} (hs : ηs ≠ 0) (ht : ηt ≠ 0) :
    a * (ηs / ηt) * (Q * b / ηs ^ 2 * Lt) * S + c / ηt * (Q * e / ηs * Lt) * S =
      ((c * Q * e + Q * a * b) / ηt * (Lt * S)) * ηs⁻¹ := by
  field_simp
  ring

include hc in
theorem mbV_init_bound {n : ℕ} (σ : Fin (n + 4) → Bool) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 4) → Fin (m * W)) :
    ‖propOp (mbPropI P n 0 t) (mbSlot (mbTheta P t) (mbJ n) fun x => avM P σ x 0) x‖ ≤
      vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * B₀ / vsHeight P.z t *
        (P.lEta t * P.sAv x t) := by
  have hin0 := hc.inputs (t := 0) ⟨le_rfl, zero_le_one⟩
  have hL0 := hin0.lEta_pos
  have hint_t := hc.inputs ht
  have hCP := kernelActionConst_ge_one d
  rw [← mb_slotJ_propI_comm hc ht]
  have hg : ∀ y, ‖propOp (mbPropI P n 0 t) (fun x => avM P σ x 0) y‖ ≤
      (kernelActionConst d ^ (n + 4) * B₀ * P.lEta t) * P.sAv y t := by
    intro y
    refine (mb_propI_apply hc le_rfl ht.1 ht.2 (mul_nonneg hB₀ hL0.le) _
      (fun y => (hInit y).trans (le_of_eq (by ring))) y).trans (le_of_eq ?_)
    field_simp
  have hφ : 0 ≤ kernelActionConst d ^ (n + 4) * B₀ * P.lEta t :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) hB₀) hint_t.lEta_pos.le
  refine (mb_thetaAction P t hint_t (n := n + 2) _ (vsCK_pos d).le hφ (hc.theta_bound ht) _ hg
    _ x).trans (le_of_eq ?_)
  ring

include hA hc in
theorem mbV_integrand_bound {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ)
    (A I : ℕ → ℝ) (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {s t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) t) (x : Fin (n + 4) → Fin (m * W)) :
    ‖propOp (mbPropI P n s t) (mbSlot (mbTheta P t) (mbJ n) (mbGI P σ s)) x‖ ≤
      ((vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * mbFc d n A I +
          kernelActionConst d ^ (n + 5) * (mbZc d (mbLambda d (m * W)) n A I B₀ + mbRc d n A)) /
            vsHeight P.z t * (P.lEta t * P.sAv x t)) * (vsHeight P.z s)⁻¹ := by
  have hCP : 1 ≤ kernelActionConst d := kernelActionConst_ge_one d
  have hCK : 0 ≤ vsCK d := (vsCK_pos d).le
  have hΛ0 : 0 ≤ mbLambda d (m * W) :=
    mbLambda_nonneg d (Nat.mul_pos (by have := hc.hm; omega) hc.hW)
  obtain ⟨hFc, -, hRc, hZc, -⟩ := mb_consts_nonneg d hΛ0 n hA0 hI0 hB₀
  have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
  have hzi := hc.zpos
  have hint_t := hc.inputs ht
  have hηt := hint_t.height_pos
  have hLt := hint_t.lEta_pos
  have hins := hc.inputs hs1
  have hηs := hins.height_pos
  have hLs := hins.lEta_pos
  -- split the forcing
  have hsplit : mbSlot (mbTheta P t) (mbJ n) (mbGI P σ s) =
      mbSlot (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t) (mbJ n)
        (mbSlot (mbTheta P s) (mbJ' n) (mbSlot (mbTheta P s) (mbJ n) (fun x => avM P σ x s)))
        + mbSlot (mbTheta P t) (mbJ n) (fun x => mbFM P σ x s) := by
    rw [mbGI, mbSlot_add]
    congr 1
    have hKt : mbTheta P t = vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t *
        mbTheta P s := by
      unfold mbTheta
      exact vsKernel_eq_propagator_mul hc.stoch (mb_norm_mm_lt hzi hs1) (mb_norm_mm_lt hzi ht)
    rw [hKt, mbSlot_mul, mbSlot_slot_comm _ _ (mb_slots_distinct n).2.2.2.2.1]
  rw [hsplit, map_add, Pi.add_apply]
  -- the D-part
  have hD := mbD_bound hA hc σ hσ A I hA0 hI0 hAv hIso hB₀ hInit hs1
  have hφD : 0 ≤ (mbZc d (mbLambda d (m * W)) n A I B₀ + mbRc d n A) / vsHeight P.z s ^ 2 *
      P.lEta s :=
    mul_nonneg (div_nonneg (add_nonneg hZc hRc) (pow_nonneg hηs.le 2)) hLs.le
  have hDprop : ∀ y, ‖propOp (mbPropI P n s t) (mbSlot (mbTheta P s) (mbJ' n)
      (mbSlot (mbTheta P s) (mbJ n) (fun x => avM P σ x s))) y‖ ≤
      (kernelActionConst d ^ (n + 4) * (mbZc d (mbLambda d (m * W)) n A I B₀ + mbRc d n A) /
        vsHeight P.z s ^ 2 * P.lEta t) *
        P.sAv y t := by
    intro y
    refine (mb_propI_apply hc hs.1 hs.2 ht.2 hφD _ hD y).trans (le_of_eq ?_)
    field_simp
  have hφD' : 0 ≤ kernelActionConst d ^ (n + 4) *
      (mbZc d (mbLambda d (m * W)) n A I B₀ + mbRc d n A) / vsHeight P.z s ^ 2 *
      P.lEta t :=
    mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (add_nonneg hZc hRc))
      (pow_nonneg hηs.le 2)) hLt.le
  have hP5 := mb_P5Action P t hint_t (n := n + 2)
    (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t) hφD'
    (mb_P5_sat hc hs.1 hs.2 ht.2) _ hDprop (mbJ n) x
  have hJ : mbFacI n (mbJ n) = .sat := by
    simp only [mbFacI, ite_eq_right_iff]
    intro h
    exact absurd h (mb_slots_distinct n).2.2.2.2.1
  have hcomm : propOp (mbPropI P n s t)
      (mbSlot (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t) (mbJ n)
        (mbSlot (mbTheta P s) (mbJ' n) (mbSlot (mbTheta P s) (mbJ n)
          (fun x => avM P σ x s)))) =
      mbSlot (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t) (mbJ n)
        (propOp (mbPropI P n s t) (mbSlot (mbTheta P s) (mbJ' n)
          (mbSlot (mbTheta P s) (mbJ n) (fun x => avM P σ x s)))) := by
    refine (mbSlot_tensor_comm _ _ _ ?_ _).symm
    simp only [hJ, PropFactor.mu1, PropFactor.mu2]
    exact Commute.refl _
  -- the F-part
  have hF := mbFM_bound P hs1 hins A I hA0 hI0 (fun n' h3 h4 => hAv n' (by omega) h4) hIso σ
  have hφF : 0 ≤ kernelActionConst d ^ (n + 4) * mbFc d n A I / vsHeight P.z s * P.lEta t :=
    mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg (by linarith) _) hFc) hηs.le) hLt.le
  have hFprop : ∀ y, ‖propOp (mbPropI P n s t) (fun x => mbFM P σ x s) y‖ ≤
      (kernelActionConst d ^ (n + 4) * mbFc d n A I / vsHeight P.z s * P.lEta t) * P.sAv y t := by
    intro y
    refine (mb_propI_apply hc hs.1 hs.2 ht.2 (mul_nonneg (div_nonneg hFc hηs.le) hLs.le) _
      (fun y => (hF y).trans (le_of_eq (by unfold mbFc; ring))) y).trans (le_of_eq ?_)
    field_simp
  have hFθ := mb_thetaAction P t hint_t (n := n + 2) _ hCK hφF (hc.theta_bound ht) _ hFprop
    (mbJ n) x
  rw [hcomm, ← mb_slotJ_propI_comm hc ht]
  calc _ ≤ ‖mbSlot (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t) (mbJ n)
          (propOp (mbPropI P n s t) (mbSlot (mbTheta P s) (mbJ' n)
            (mbSlot (mbTheta P s) (mbJ n) (fun x => avM P σ x s)))) x‖ +
        ‖mbSlot (mbTheta P t) (mbJ n) (propOp (mbPropI P n s t)
          (fun x => mbFM P σ x s)) x‖ := norm_add_le _ _
    _ ≤ kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) *
          (kernelActionConst d ^ (n + 4) * (mbZc d (mbLambda d (m * W)) n A I B₀ + mbRc d n A) /
            vsHeight P.z s ^ 2 *
            P.lEta t) * P.sAv x t +
        vsCK d * d.Cwc / vsHeight P.z t *
          (kernelActionConst d ^ (n + 4) * mbFc d n A I / vsHeight P.z s *
          P.lEta t) * P.sAv x t := add_le_add hP5 hFθ
    _ = _ := by
      rw [pow_succ]
      exact mb_vb_alg (vsHeight_pos hzi hs1.2).ne' hηt.ne'

include hA hc in

/-- **The linear term of saturated chains** (slot `J = last`; under `MBAlg` and the
initial bound `hInit`):
`|T̂^{(J)}_t X_t(x)| ≤ V_k η_t⁻¹ L_t s^av_t(x)`.
-/
theorem mbV_bound {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 4) → Fin (m * W)) :
    ‖mbV P σ t x‖ ≤ mbVc d (mbLambda d (m * W)) n A I B₀ / vsHeight P.z t *
      (P.lEta t * P.sAv x t) := by
  have hΛ0 : 0 ≤ mbLambda d (m * W) :=
    mbLambda_nonneg d (Nat.mul_pos (by have := hc.hm; omega) hc.hW)
  obtain ⟨hFc, -, hRc, hZc, -⟩ := mb_consts_nonneg d hΛ0 n hA0 hI0 hB₀
  have hGc : ContinuousOn (fun s => mbSlot (mbTheta P t) (mbJ n) (mbGI P σ s)) (Icc (0 : ℝ) 1) :=
    mb_contOn_slot (T := fun _ => mbTheta P t) (X := fun s => mbGI P σ s)
      (fun _ _ => continuousOn_const) (mb_contOn_GI hA hc σ hσ) (mbJ n)
  have hint := mb_intervalIntegrable_propI hc ht hGc
  have hdu := congrFun (mbV_duhamel hA hc σ hσ ht) x
  have h0 := mbV_init_bound hc σ hB₀ hInit ht x
  have hI := mb_norm_integral_le hc.zpos ht hint x
    (fun s hs => mbV_integrand_bound hA hc σ hσ A I hA0 hI0 hAv hIso hB₀ hInit ht hs x)
  have hΛ : ∫ s in (0 : ℝ)..t, (vsHeight P.z s)⁻¹ ≤ mbLambda d (m * W) :=
    (vsIntRules (Nat.mul_pos (by have := hc.hm; omega) hc.hW) hc.hW d.delta0_pos.le
      d.kappa_pos (by linarith [d.C0_ge_one]) hc.hz ht.1 ht.2 one_pos).1
  have hLx := mb_LsAv_pos_nonneg hc ht x
  have hηt := (hc.inputs ht).height_pos
  have hCP := kernelActionConst_ge_one d
  have hCK := (vsCK_pos d).le
  obtain ⟨a, ha⟩ : ∃ a, a = vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * B₀ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * mbFc d n A I +
      kernelActionConst d ^ (n + 5) * (mbZc d (mbLambda d (m * W)) n A I B₀ + mbRc d n A) :=
    ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by
    rw [hb]
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg hCK (by linarith [d.one_le_Cwc]))
        (pow_nonneg (by linarith) _)) hFc
    · exact mul_nonneg (pow_nonneg (by linarith) _) (add_nonneg hZc hRc)
  have hV : mbVc d (mbLambda d (m * W)) n A I B₀ = a + mbLambda d (m * W) * b := by
    rw [ha, hb]
    unfold mbVc
    ring
  rw [← ha] at h0
  rw [← hb] at hI
  rw [hdu, Pi.add_apply, hV]
  have hcoef : 0 ≤ b / vsHeight P.z t * (P.lEta t * P.sAv x t) :=
    mul_nonneg (div_nonneg hb0 hηt.le) hLx
  calc _ ≤ a / vsHeight P.z t * (P.lEta t * P.sAv x t) +
        b / vsHeight P.z t * (P.lEta t * P.sAv x t) * ∫ s in (0 : ℝ)..t, (vsHeight P.z s)⁻¹ :=
      (norm_add_le _ _).trans (add_le_add h0 hI)
    _ ≤ a / vsHeight P.z t * (P.lEta t * P.sAv x t) +
        b / vsHeight P.z t * (P.lEta t * P.sAv x t) * mbLambda d (m * W) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hΛ hcoef)
    _ = _ := by ring

end BlockBand.Native.ErdosRiabov.MBound
