module

public import BlockBand.Native.ErdosRiabov.MBound.SatZ

/-!
# The linear term of the saturated chain

The Duhamel formula for the saturated averaged `M`-term with the slot `J'` treated as forcing,
and the constants of the bound on the linear term `T̂^{(J)}_t X_t`.

* `mbPropI P n s t`: the tensor propagator with the identity at slot `J' = n+1` and `P̂` elsewhere
  (`goodProp` with factors `ident`/`sat`), whose generator is `⊕_{i ≠ J'} T̂^{(i)}`;
* `mb_P5Action`: a kernel `K` with `Σ_a |K(u,a)| √(Υ(w,a)Υ(a,w')) ≤ C √(Υ(w,u)Υ(u,w'))` acts on
  `φ s^av_t` with the same constant `C`;
* the constants `F̃_k`, `R_k`, `Z_k`, `V_k` of the bound `mbV_bound`:
  `|T̂^{(J)}_t X_t(x)| ≤ V_k η_t⁻¹ L_t s^av_t(x)`.
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

/-!
## Generic actions
-/

/-- A kernel with `Σ_a|K(u,a)|√(Υ(w,a)Υ(a,w')) ≤ C√(Υ(w,u)Υ(u,w'))` acts on functions bounded
by `φ s^av_t` with the same constant (in any slot).
-/
theorem mb_P5Action (P : PsiData N) (t : ℝ) {d : VSData} (hin : ContrVSInputs d P t) {n : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) {C φ : ℝ} (hφ : 0 ≤ φ)
    (hK : ∀ u w w', ∑ a, ‖K u a‖ * Real.sqrt (P.ups t w a * P.ups t a w') ≤
      C * Real.sqrt (P.ups t w u * P.ups t u w'))
    (g : (Fin (n + 2) → Fin N) → ℂ) (hg : ∀ y, ‖g y‖ ≤ φ * P.sAv y t)
    (j : Fin (n + 2)) (x : Fin (n + 2) → Fin N) :
    ‖mbSlot K j g x‖ ≤ C * φ * P.sAv x t := by
  have hU := hin.nonneg
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = ∏ e : Fin n, P.ups t (mbRotTo j x e.castSucc.castSucc)
      (mbRotTo j x e.succ.castSucc) := ⟨_, rfl⟩
  have hQ : 0 ≤ Q := hQdef ▸ Finset.prod_nonneg fun _ _ => hU _ _
  obtain ⟨u, hu⟩ : ∃ u, u = mbRotTo j x (Fin.last n).castSucc := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = mbRotTo j x 0 := ⟨_, rfl⟩
  obtain ⟨c0, hc0def⟩ : ∃ c0, c0 = P.lEta t ^ (-((n + 2 : ℕ) : ℝ) / 2) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c0 := hc0def ▸ Real.rpow_nonneg hin.lEta_pos.le _
  have hupd : ∀ c, P.sAv (update x j c) t =
      c0 * Real.sqrt (Q * (P.ups t u c * P.ups t c w)) := by
    intro c
    rw [← mb_sAv_rotTo P t j, mbRotTo_update, mb_sAv_last]
    have h1 : ∀ e : Fin n, update (mbRotTo j x) (Fin.last (n + 1)) c e.castSucc.castSucc =
        mbRotTo j x e.castSucc.castSucc :=
      fun e => update_of_ne (by simp [Fin.ext_iff]; omega) _ _
    have h2 : ∀ e : Fin n, update (mbRotTo j x) (Fin.last (n + 1)) c e.succ.castSucc =
        mbRotTo j x e.succ.castSucc :=
      fun e => update_of_ne (by simp [Fin.ext_iff]; omega) _ _
    have h3 : update (mbRotTo j x) (Fin.last (n + 1)) c (Fin.last n).castSucc = u :=
      hu ▸ update_of_ne (by simp [Fin.ext_iff]) _ _
    have h4 : update (mbRotTo j x) (Fin.last (n + 1)) c 0 = w :=
      hw ▸ update_of_ne (by simp [Fin.ext_iff]) _ _
    simp only [h1, h2, h3, h4, update_self, hQdef, hc0def, mul_assoc]
  have hx : P.sAv x t = c0 * Real.sqrt (Q * (P.ups t u (x j) * P.ups t (x j) w)) := by
    have := hupd (x j)
    rwa [update_eq_self] at this
  calc ‖mbSlot K j g x‖ ≤ ∑ c, ‖K (x j) c‖ * ‖g (update x j c)‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
    _ ≤ ∑ c, ‖K (x j) c‖ * (φ * (c0 * Real.sqrt (Q * (P.ups t u c * P.ups t c w)))) :=
        Finset.sum_le_sum fun c _ => by
          rw [← hupd c]
          exact mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
    _ = φ * c0 * Real.sqrt Q * ∑ c, ‖K (x j) c‖ * Real.sqrt (P.ups t u c * P.ups t c w) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Real.sqrt_mul hQ]
        ring
    _ ≤ φ * c0 * Real.sqrt Q * (C * Real.sqrt (P.ups t u (x j) * P.ups t (x j) w)) :=
        mul_le_mul_of_nonneg_left (hK _ _ _)
          (mul_nonneg (mul_nonneg hφ hc0) (Real.sqrt_nonneg _))
    _ = C * φ * P.sAv x t := by
        rw [hx, Real.sqrt_mul hQ]
        ring

/-!
## The propagator with the identity at `J'`
-/

/-- The factors `ident` at `J' = n+1`, `sat` elsewhere. -/
def mbFacI (n : ℕ) : Fin (n + 4) → PropFactor := fun i => if i = mbJ' n then .ident else .sat

/-- `P̃_{s,t} = ⊗_i P̂_i` with the identity at `J'`. -/
def mbPropI (P : PsiData N) (n : ℕ) (s t : ℝ) :
    Matrix (Fin (n + 4) → Fin N) (Fin (n + 4) → Fin N) ℂ :=
  goodProp P.S P.z (mbFacI n) s t

/-- Its generator `⊕_{i ≠ J'} T̂^{(i)}_s`. -/
def mbGenI (P : PsiData N) (n : ℕ) (s : ℝ) :
    Matrix (Fin (n + 4) → Fin N) (Fin (n + 4) → Fin N) ℂ :=
  vsTensorGen P.S (fun j => (mbFacI n j).mu1 P.z) (fun j => (mbFacI n j).mu2 P.z) s

theorem mbGenI_apply (P : PsiData N) {n : ℕ} (s : ℝ) (f : (Fin (n + 4) → Fin N) → ℂ) :
    propOp (mbGenI P n s) f = mbOplus (mbTheta P s) f - mbSlot (mbTheta P s) (mbJ' n) f := by
  funext x
  rw [mbGenI, propOp_vsTensorGen_apply, Pi.sub_apply]
  unfold mbOplus
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (mbJ' n)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (mbJ' n))]
  have h0 : ∑ c, vsKernel P.S ((mbFacI n (mbJ' n)).mu1 P.z) ((mbFacI n (mbJ' n)).mu2 P.z) s
      (x (mbJ' n)) c * f (update x (mbJ' n) c) = 0 := by
    simp [mbFacI, PropFactor.mu1, PropFactor.mu2, vsKernel, vsY]
  rw [h0, zero_add, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≠ mbJ' n := Finset.ne_of_mem_erase hi
  simp only [mbSlot, mbFacI, hi', ite_false, PropFactor.mu1, PropFactor.mu2, mbTheta]

theorem mb_norm_mu1_lt {z : ℂ} (hz : 0 < z.im) (c : PropFactor) : ‖c.mu1 z‖ < 1 := by
  cases c <;> simp [PropFactor.mu1, mb_norm_m_lt hz]

theorem mb_norm_mu2_lt {z : ℂ} (hz : 0 < z.im) (c : PropFactor) : ‖c.mu2 z‖ < 1 := by
  cases c <;> simp [PropFactor.mu2, mb_norm_m_lt hz]

/-!
## The Duhamel formula for the linear term
-/

section Duhamel

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

include hc in
theorem mb_contOn_propI {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun s => propOp (mbPropI P n s t)) (Icc (0 : ℝ) 1) := fun _ hs =>
  (hasDerivAt_propOp_vsTensorProp_left hc.stoch (fun _ => mb_norm_mu1_lt hc.zpos _)
    (fun _ => mb_norm_mu2_lt hc.zpos _) hs.1 hs.2 ht.1 ht.2).continuousAt.continuousWithinAt

include hc in
theorem mb_intervalIntegrable_propI {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {G : ℝ → (Fin (n + 4) → Fin (m * W)) → ℂ} (hG : ContinuousOn G (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun s => propOp (mbPropI P n s t) (G s)) volume 0 t := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le ht.1]
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
  exact ((mb_contOn_propI hc ht).mono hsub).clm_apply (hG.mono hsub)

theorem mb_contOn_slot {k : ℕ} {T : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {X : ℝ → (Fin k → Fin N) → ℂ} {s : Set ℝ} (hT : ∀ a b, ContinuousOn (fun r => T r a b) s)
    (hX : ContinuousOn X s) (j : Fin k) : ContinuousOn (fun r => mbSlot (T r) j (X r)) s := by
  refine continuousOn_pi.2 fun x => ?_
  unfold mbSlot
  exact continuousOn_finsetSum _ fun c _ => (hT _ _).mul (mb_contOn_coord hX _)

/-- The forcing of the `P̃`-Duhamel form of `X`: `T̂^{(J')}_s X_s + F_s`. -/
def mbGI (P : PsiData N) {n : ℕ} (σ : Fin (n + 4) → Bool) (s : ℝ) :
    (Fin (n + 4) → Fin N) → ℂ :=
  mbSlot (mbTheta P s) (mbJ' n) (fun x => avM P σ x s) + fun x => mbFM P σ x s

include hA hc in
theorem mb_contOn_GI {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ContinuousOn (fun s => mbGI P σ s) (Icc (0 : ℝ) 1) :=
  (mb_contOn_slot (mb_contOn_theta hc) (mb_contOn_X hA hc (n := n + 1) σ hσ) _).add
    (mb_contOn_F hA hc (n := n + 1) σ hσ)

include hA hc in
/-- Duhamel for `X` with `P̃`: `X_t = P̃_{0,t} X_0 + ∫_0^t P̃_{s,t}(T̂^{(J')}_s X_s + F_s) ds`. -/
theorem mbX_duhamelI {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => avM P σ x t) = propOp (mbPropI P n 0 t) (fun x => avM P σ x 0) +
      ∫ s in (0 : ℝ)..t, propOp (mbPropI P n s t) (mbGI P σ s) := by
  refine vsTensorProp_duhamel (X := fun r => fun x => avM P σ x r) hc.stoch
    (fun _ => mb_norm_mu1_lt hc.zpos _) (fun _ => mb_norm_mu2_lt hc.zpos _) le_rfl zero_le_one
    ht.1 ht.2 (fun s hs => ?_) (mb_intervalIntegrable_propI hc ht (mb_contOn_GI hA hc σ hσ))
  rw [uIcc_of_le ht.1] at hs
  have h := mb_hasDerivAt_X hA hc (n := n + 1) σ hσ ⟨hs.1, hs.2.trans ht.2⟩
  refine h.congr_deriv ?_
  have hg : ∀ f : (Fin (n + 4) → Fin (m * W)) → ℂ,
      propOp (mbGenSat P (n + 4) s) f = mbOplus (mbTheta P s) f := fun f => by
    rw [mbTheta, mbOplus_eq_propOp]
    rfl
  show propOp (mbGenSat P (n + 4) s) _ + _ = propOp (mbGenI P n s) _ + mbGI P σ s
  rw [hg, mbGenI_apply, mbGI]
  abel

include hc in
theorem mb_slotJ_propI_comm {n : ℕ} {s t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (f : (Fin (n + 4) → Fin (m * W)) → ℂ) :
    mbSlot (mbTheta P t) (mbJ n) (propOp (mbPropI P n s t) f) =
      propOp (mbPropI P n s t) (mbSlot (mbTheta P t) (mbJ n) f) := by
  have hJ : mbFacI n (mbJ n) = .sat := by
    simp only [mbFacI, ite_eq_right_iff]
    intro h
    exact absurd h (mb_slots_distinct n).2.2.2.2.1
  refine mbSlot_tensor_comm _ _ _ ?_ f
  simp only [hJ, PropFactor.mu1, PropFactor.mu2]
  rw [vsPropagator_eq hc.stoch (mb_norm_mm_lt hc.zpos ht), mbTheta]
  exact (Commute.one_right _).add_right ((Commute.refl _).smul_right _)

/-- The linear term `V_t = T̂^{(J)}_t X_t`. -/
def mbV (P : PsiData N) {n : ℕ} (σ : Fin (n + 4) → Bool) (t : ℝ) :
    (Fin (n + 4) → Fin N) → ℂ :=
  mbSlot (mbTheta P t) (mbJ n) (fun x => avM P σ x t)

include hA hc in

/-- **Duhamel formula for the linear term**:
`V_t = P̃_{0,t}T̂^{(J)}_tX_0 + ∫_0^t P̃_{s,t}T̂^{(J)}_t(T̂^{(J')}_sX_s + F_s) ds`. -/
theorem mbV_duhamel {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    mbV P σ t = propOp (mbPropI P n 0 t) (mbSlot (mbTheta P t) (mbJ n) (fun x => avM P σ x 0)) +
      ∫ s in (0 : ℝ)..t, propOp (mbPropI P n s t) (mbSlot (mbTheta P t) (mbJ n) (mbGI P σ s)) := by
  have hint := mb_intervalIntegrable_propI hc ht (mb_contOn_GI hA hc σ hσ)
  have hS : ∀ f : (Fin (n + 4) → Fin (m * W)) → ℂ,
      mbSlot (mbTheta P t) (mbJ n) f = propOp (mbSlotMat (mbJ n) (mbTheta P t)) f :=
    fun f => mbSlot_eq_propOp _ _ f
  unfold mbV
  rw [mbX_duhamelI hA hc σ hσ ht, hS, map_add,
    ← (propOp (mbSlotMat (mbJ n) (mbTheta P t))).intervalIntegral_comp_comm hint, ← hS,
    mb_slotJ_propI_comm hc ht]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  show propOp _ (propOp _ _) = _
  rw [← hS, mb_slotJ_propI_comm hc ht]

end Duhamel

end BlockBand.Native.ErdosRiabov.MBound

/-!
## The bound on the linear term
-/

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators

variable {N : ℕ}

/-- Slot operators on different slots commute. -/
theorem mbSlot_slot_comm (K K' : Matrix (Fin N) (Fin N) ℂ) {k : ℕ} {i j : Fin k} (hij : i ≠ j)
    (f : (Fin k → Fin N) → ℂ) : mbSlot K i (mbSlot K' j f) = mbSlot K' j (mbSlot K i f) := by
  funext x
  simp only [mbSlot, update_of_ne hij, update_of_ne hij.symm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [update_comm hij]
  ring

/-- The constants of the saturated `M`-bound (`C_K = vsCK d`, `C_P = kernelActionConst d`,
`C_reg = onestepConst d`, `Λ` a parameter), for chain length `n+4`. -/
def mbFc (d : VSData) (n : ℕ) (A I : ℕ → ℝ) : ℝ := d.Cwc * mbFPairSum (n + 4) A I

/-- `F̃_k = 4 C_K √C₁'' A_{k-1}`. -/
def mbFtc (d : VSData) (n : ℕ) (A : ℕ → ℝ) : ℝ := 4 * vsCK d * Real.sqrt d.C1pp * A (n + 3)

/-- `R_k = 2 C_K² C_wc √C₁'' A_{k-1} + C_K² C₁'' A_{k-2}`. -/
def mbRc (d : VSData) (n : ℕ) (A : ℕ → ℝ) : ℝ :=
  2 * vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * A (n + 3) + vsCK d ^ 2 * d.C1pp * A (n + 2)

/-- `Z_k = C_reg² C_P^k (B₀ + Λ (F_k + F̃_k))`. -/
def mbZc (d : VSData) (Λ : ℝ) (n : ℕ) (A I : ℕ → ℝ) (B₀ : ℝ) : ℝ :=
  onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) * (B₀ + Λ * (mbFc d n A I + mbFtc d n A))

/-- `V_k = C_K C_wc C_P^k (B₀ + Λ F_k) + C_P^{k+1} Λ (Z_k + R_k)`. -/
def mbVc (d : VSData) (Λ : ℝ) (n : ℕ) (A I : ℕ → ℝ) (B₀ : ℝ) : ℝ :=
  vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * (B₀ + Λ * mbFc d n A I) +
    kernelActionConst d ^ (n + 5) * Λ * (mbZc d Λ n A I B₀ + mbRc d n A)

section Bound

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

include hc in
theorem mb_propI_apply {n : ℕ} {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) {φ : ℝ}
    (hφ : 0 ≤ φ) (g : (Fin (n + 4) → Fin (m * W)) → ℂ) (hg : ∀ y, ‖g y‖ ≤ φ * P.sAv y s)
    (x : Fin (n + 4) → Fin (m * W)) :
    ‖propOp (mbPropI P n s t) g x‖ ≤
      kernelActionConst d ^ (n + 4) * φ * (P.lEta t / P.lEta s) * P.sAv x t := by
  have hj : mbFacI n (mbJ' n) ≠ .sat := by simp [mbFacI]
  have h := goodProps_av_any d hc.hm hc.hW P hc.hPW hc.hPD hc.hz hs0 hst ht1 (n := n + 2)
    (mbFacI n) (mbJ' n) hj x
  have he : goodProp (shortRingProfile d.b m W) P.z (mbFacI n) s t = mbPropI P n s t := by
    rw [mbPropI, hc.hPS]
  rw [he] at h
  rw [propOp_apply]
  calc ‖∑ y, mbPropI P n s t x y * g y‖ ≤ ∑ y, ‖mbPropI P n s t x y‖ * (φ * P.sAv y s) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hg y) (norm_nonneg _))
    _ = φ * ∑ y, ‖mbPropI P n s t x y‖ * P.sAv y s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ φ * (kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) * P.sAv x t) :=
        mul_le_mul_of_nonneg_left h hφ
    _ = _ := by ring

include hc in
theorem mb_heights {s t : ℝ} (hst : s ≤ t) : vsHeight P.z t ≤ vsHeight P.z s := by
  have hy := semicircleM_im_pos hc.zpos
  rw [vsHeight_affine P.z t, vsHeight_affine P.z s]
  nlinarith

include hc in
theorem mb_P5_sat {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) (u w w' : Fin (m * W)) :
    ∑ a, ‖vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t u a‖ *
        Real.sqrt (P.ups t w a * P.ups t a w') ≤
      kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) *
        Real.sqrt (P.ups t w u * P.ups t u w') := by
  have h := goodProp_stepC_sat d hc.hm hc.hW hc.hz hs0 hst ht1 u w w'
  unfold PsiData.ups
  rw [hc.hPW, hc.hPD, hc.hPS]
  exact h

theorem onestepConst_nonneg (d : VSData) : 0 ≤ onestepConst d := by
  unfold onestepConst
  have h1 := (vsCK_pos d).le
  have h2 := d.one_le_C1pp
  have h3 := d.cm_pos
  have h4 : 0 ≤ vsCK d / d.cm := div_nonneg h1 h3.le
  have h5 : 0 ≤ d.C1pp ^ 3 * Real.sqrt d.C1pp :=
    mul_nonneg (pow_nonneg (by linarith) 3) (Real.sqrt_nonneg _)
  exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_two h1) h5) (by linarith)

theorem mbLambda_nonneg (d : VSData) {N : ℕ} (hN : 0 < N) : 0 ≤ mbLambda d N := by
  unfold mbLambda
  refine mul_nonneg (inv_nonneg.mpr d.cm_pos.le) (Real.log_nonneg ?_)
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [d.C0_ge_one]

theorem mbFPairSum_nonneg {k : ℕ} {A I : ℕ → ℝ} (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n) :
    0 ≤ mbFPairSum k A I := by
  unfold mbFPairSum
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact mul_nonneg (hI0 _) (hA0 _)
  · exact le_rfl

theorem mb_consts_nonneg (d : VSData) {Λ : ℝ} (hΛ : 0 ≤ Λ) (n : ℕ) {A I : ℕ → ℝ}
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n) {B₀ : ℝ} (hB₀ : 0 ≤ B₀) :
    0 ≤ mbFc d n A I ∧ 0 ≤ mbFtc d n A ∧ 0 ≤ mbRc d n A ∧ 0 ≤ mbZc d Λ n A I B₀ ∧
      0 ≤ mbVc d Λ n A I B₀ := by
  have hCwc := d.one_le_Cwc
  have hC1 := d.one_le_C1pp
  have hCK := (vsCK_pos d).le
  have hCP := kernelActionConst_ge_one d
  have hP := mbFPairSum_nonneg (k := n + 4) hA0 hI0
  have hFc : 0 ≤ mbFc d n A I := mul_nonneg (by linarith) hP
  have hFt : 0 ≤ mbFtc d n A :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCK) (Real.sqrt_nonneg _)) (hA0 _)
  have hRc : 0 ≤ mbRc d n A := by
    unfold mbRc
    have := hA0 (n + 3)
    have := hA0 (n + 2)
    have := Real.sqrt_nonneg d.C1pp
    positivity
  have hCPp : ∀ j : ℕ, 0 ≤ kernelActionConst d ^ j := fun j => pow_nonneg (by linarith) j
  have hZc : 0 ≤ mbZc d Λ n A I B₀ :=
    mul_nonneg (mul_nonneg (pow_nonneg (onestepConst_nonneg d) 2) (hCPp _))
      (add_nonneg hB₀ (mul_nonneg hΛ (add_nonneg hFc hFt)))
  refine ⟨hFc, hFt, hRc, hZc, ?_⟩
  unfold mbVc
  exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCK (by linarith)) (hCPp _))
    (add_nonneg hB₀ (mul_nonneg hΛ hFc))) (mul_nonneg (mul_nonneg (hCPp _) hΛ)
      (add_nonneg hZc hRc))

include hA hc in

/-- The doubly hit term satisfies `|T̂^{(J')}_sT̂^{(J)}_sX_s| ≤ (Z_k+R_k)η_s⁻²L_s s^av_s` for
`s ∈ [0,1]`.
-/
theorem mbD_bound {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (y : Fin (n + 4) → Fin (m * W)) :
    ‖mbSlot (mbTheta P s) (mbJ' n) (mbSlot (mbTheta P s) (mbJ n) (fun x => avM P σ x s)) y‖ ≤
      ((mbZc d (mbLambda d (m * W)) n A I B₀ + mbRc d n A) / vsHeight P.z s ^ 2 * P.lEta s) *
        P.sAv y s := by
  have hins := hc.inputs hs
  have hηs := hins.height_pos
  have hCK := (vsCK_pos d).le
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mb_slots_distinct n
  rw [mbRingDecomp (mbTheta P s) (J := mbJ n) (A := mbA n) (A' := mbA' n) (Ne.symm h5)
    (Ne.symm h3) (fun x => avM P σ x s), Pi.add_apply]
  have hZ := mbZ_bound hA hc σ hσ A I hA0 hI0 hAv hIso hB₀ hInit hs y
  obtain ⟨hwL, hwM, hwLM⟩ := mbWard_bounds P hc.profile hc.zpos hs hA.cyclic hA.ward σ hσ
    (hAv (n + 3) (by omega) (by omega)) (hAv (n + 2) (by omega) (by omega)) hηs
  have hR := mbRem_bound P s hins (mbTheta P s) hCK (hc.theta_bound hs) (fun x => avM P σ x s)
    (div_nonneg (hA0 _) hηs.le) (div_nonneg (hA0 _) (pow_nonneg hηs.le 2)) hwL hwM hwLM y
  have hZ' : ‖mbZ P σ s y‖ ≤ mbZc d (mbLambda d (m * W)) n A I B₀ / vsHeight P.z s ^ 2 *
      (P.lEta s * P.sAv y s) := by
    refine hZ.trans (le_of_eq ?_)
    unfold mbZc mbFc mbFtc
    ring
  have hR' : ‖mbRem (mbTheta P s) (fun x => avM P σ x s) y‖ ≤
      mbRc d n A / vsHeight P.z s ^ 2 * (P.lEta s * P.sAv y s) := by
    refine hR.trans (le_of_eq ?_)
    unfold mbRc
    field_simp
  calc _ ≤ ‖mbZ P σ s y‖ + ‖mbRem (mbTheta P s) (fun x => avM P σ x s) y‖ := norm_add_le _ _
    _ ≤ mbZc d (mbLambda d (m * W)) n A I B₀ / vsHeight P.z s ^ 2 * (P.lEta s * P.sAv y s) +
        mbRc d n A / vsHeight P.z s ^ 2 * (P.lEta s * P.sAv y s) := add_le_add hZ' hR'
    _ = _ := by ring

end Bound

end BlockBand.Native.ErdosRiabov.MBound
