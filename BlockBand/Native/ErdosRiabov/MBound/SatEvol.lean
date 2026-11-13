module

public import BlockBand.Native.ErdosRiabov.MBound.Rotate

/-!
# The saturated evolution and the Duhamel formula for the doubly regularized term

Setting `MBCtx d P`: VS data `d`, `m ≥ 4`, `W ≥ 1`, `P.S = shortRingProfile d.b m W`,
`P.W = W`, `P.D = d.D`, `P.z ∈ 𝒟`. For a saturated pattern `σ` of length `n+4`:
`X_s = Tr[M^σ_s(·)]`, `F_s = F_M`, `F̃_s = mbFt T̂_s X_s`, `Y_s = 𝒟'𝒟 X_s` (`𝒟 = mbReg J A`,
`𝒟' = mbReg J' A'`).

* `mb_hasDerivAt_X`: `Ẋ_s = (⊕ T̂_s) X_s + F_s` (any `k ≥ 3`, saturated);
* `mb_hasDerivAt_Y` (by `mbRegCommutator_double`): `Ẏ_s = (⊕ T̂_s) Y_s + 𝒟'𝒟(F_s + F̃_s)`;
* the Duhamel formulas for `Y` and for the doubly regularized term
  `Z_t = Θ̊^{(J')}_t Θ̊^{(J)}_t X_t`.
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

/-- The `M`-term algebra used by the `M`-bounds (`Split.DerivStatement`,
`Split.CyclicStatement`, `Split.WardStatement`), carried as an explicit hypothesis; it is proved
as `Discharge.mbAlg_holds`. -/
structure MBAlg : Prop where
  deriv : Split.DerivStatement
  cyclic : Split.CyclicStatement
  ward : Split.WardStatement

/-- The VS context of the `M`-bounds. -/
structure MBCtx (d : VSData) {m W : ℕ} (P : PsiData (m * W)) : Prop where
  hm : 4 ≤ m
  hW : 0 < W
  hPS : P.S = shortRingProfile d.b m W
  hPW : P.W = W
  hPD : P.D = d.D
  hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z

namespace MBCtx

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)
include hc

theorem stoch : StochasticSymm P.S := by
  rw [hc.hPS]
  exact shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (by have := hc.hm; omega) hc.hW

theorem profile : Split.ProfileHyp P.S := stochasticSymm_iff_profileHyp.mp hc.stoch

theorem zpos : 0 < P.z.im := hc.hz.im_pos (Nat.mul_pos (by have := hc.hm; omega) hc.hW)

theorem inputs {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ContrVSInputs d P t :=
  contrVSInputs_of d hc.hm hc.hW P hc.hPW hc.hPD hc.hz ht.1 ht.2

theorem theta_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (a b : Fin (m * W)) :
    ‖mbTheta P t a b‖ ≤ vsCK d * P.ups t a b :=
  mbTheta_bound d hc.hm hc.hW P hc.hPS hc.hPW hc.hPD hc.hz ht a b

end MBCtx

/-!
## The regularization as a continuous linear map
-/

section RegCLM

variable {k : ℕ}

/-- `𝒟^{(j)}` as an `ℝ`-linear map. -/
def mbRegLin (j a : Fin k) : ((Fin k → Fin N) → ℂ) →ₗ[ℝ] ((Fin k → Fin N) → ℂ) where
  toFun := mbReg j a
  map_add' := mbReg_add j a
  map_smul' c f := by
    funext x
    simp only [mbReg, mbTr, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [smul_sub, Finset.mul_sum]

/-- `𝒟^{(j)}` as a continuous linear map. -/
def mbRegCLM (j a : Fin k) : ((Fin k → Fin N) → ℂ) →L[ℝ] ((Fin k → Fin N) → ℂ) :=
  LinearMap.toContinuousLinearMap (mbRegLin j a)

theorem mbRegCLM_apply (j a : Fin k) (f : (Fin k → Fin N) → ℂ) : mbRegCLM j a f = mbReg j a f :=
  rfl

theorem mb_hasDerivAt_reg {j a : Fin k} {X : ℝ → (Fin k → Fin N) → ℂ}
    {X' : (Fin k → Fin N) → ℂ} {s : ℝ} (hX : HasDerivAt X X' s) :
    HasDerivAt (fun r => mbReg j a (X r)) (mbReg j a X') s :=
  (mbRegCLM j a).hasFDerivAt.comp_hasDerivAt s hX

end RegCLM

/-!
## The evolution of `X` and `Y`
-/

/-- The saturated generator `⊕_j T̂^{(j)}_s` as a tensor matrix. -/
def mbGenSat (P : PsiData N) (k : ℕ) (s : ℝ) : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s

/-- The saturated tensor propagator `P̂^{⊗k}_{s,t}`. -/
def mbPropSat (P : PsiData N) (k : ℕ) (s t : ℝ) : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  vsTensorProp P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s t

section Evol

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

include hA hc in

/-- `Ẋ_s = (⊕ T̂_s) X_s + F_s` for a saturated pattern of length `k ≥ 3`, `s ∈ [0,1]`
(under `Split.DerivStatement`, through `MBAlg`).
-/
theorem mb_hasDerivAt_X {n : ℕ} (σ : Fin (n + 3) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => fun x => avM P σ x r)
      (propOp (mbGenSat P (n + 3) s) (fun x => avM P σ x s) + fun x => mbFM P σ x s) s := by
  rw [hasDerivAt_pi]
  intro x
  have h := hasDerivAt_avM P hA.deriv hc.zpos.ne' hc.stoch (by omega) σ x hs
  rw [mbAvM_evol P σ x s hc.stoch.symm (by omega), mbAvGen_eq_oplus P hσ, mbTheta,
    mbOplus_eq_propOp] at h
  exact h.congr_deriv (by simp only [Pi.add_apply]; rfl)

/-- The regularized chain `Y_s = 𝒟'𝒟 X_s`. -/
def mbY (P : PsiData N) {n : ℕ} (σ : Fin (n + 4) → Bool) (s : ℝ) :
    (Fin (n + 4) → Fin N) → ℂ :=
  mbReg (mbJ' n) (mbA' n) (mbReg (mbJ n) (mbA n) (fun x => avM P σ x s))

/-- The extra forcing `F̃_s = G^{(J)} X_s + G^{(J')} X_s` with the kernel `T̂_s`. -/
def mbFtX (P : PsiData N) {n : ℕ} (σ : Fin (n + 4) → Bool) (s : ℝ) :
    (Fin (n + 4) → Fin N) → ℂ :=
  mbFt (mbTheta P s) (fun x => avM P σ x s)

/-- The forcing of `Y`: `𝒟'𝒟 (F_s + F̃_s)`. -/
def mbGY (P : PsiData N) {n : ℕ} (σ : Fin (n + 4) → Bool) (s : ℝ) :
    (Fin (n + 4) → Fin N) → ℂ :=
  mbReg (mbJ' n) (mbA' n) (mbReg (mbJ n) (mbA n) ((fun x => mbFM P σ x s) + mbFtX P σ s))

theorem mb_slots_distinct (n : ℕ) :
    mbA n ≠ mbJ n ∧ mbA n ≠ mbA' n ∧ mbA n ≠ mbJ' n ∧ mbJ n ≠ mbA' n ∧ mbJ n ≠ mbJ' n ∧
      mbA' n ≠ mbJ' n := by
  simp only [mbA, mbJ, mbA', mbJ', ne_eq, Fin.ext_iff, Fin.val_last]
  omega

include hA hc in

/-- `Ẏ_s = (⊕ T̂_s) Y_s + 𝒟'𝒟(F_s + F̃_s)` (from `mbRegCommutator_double`). -/
theorem mb_hasDerivAt_Y {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => mbY P σ r) (propOp (mbGenSat P (n + 4) s) (mbY P σ s) + mbGY P σ s) s := by
  have hX := mb_hasDerivAt_X hA hc (n := n + 1) σ hσ hs
  have h := mb_hasDerivAt_reg (j := mbJ' n) (a := mbA' n)
    (mb_hasDerivAt_reg (j := mbJ n) (a := mbA n) hX)
  refine h.congr_deriv ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mb_slots_distinct n
  have hsym := mbTheta_symm d hc.hm hc.hW P hc.hPS hc.zpos hs
  have hrow := mbTheta_rowSum d hc.hm hc.hW P hc.hPS hc.zpos hs
  have hcol := mbTheta_colSum d hc.hm hc.hW P hc.hPS hc.zpos hs
  have hcomm := mbRegCommutator_double (mbTheta P s) hsym hrow hcol h1 h2 h3 h4 h5 h6
    (fun x => avM P σ x s)
  have hgen : ∀ f : (Fin (n + 4) → Fin (m * W)) → ℂ,
      propOp (mbGenSat P (n + 4) s) f = mbOplus (mbTheta P s) f := fun f => by
    rw [mbTheta, mbOplus_eq_propOp]
    rfl
  rw [mbReg_add, mbReg_add, hgen, hcomm, hgen]
  unfold mbGY mbFtX mbFt mbY
  simp only [mbReg_add]
  abel

end Evol

/-!
## Continuity
-/

section Cont

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

include hc in
theorem mb_contOn_theta (a b : Fin (m * W)) :
    ContinuousOn (fun r => mbTheta P r a b) (Icc (0 : ℝ) 1) := fun _ hr =>
  (hasDerivAt_vsKernel hc.stoch (mb_norm_mm_lt hc.zpos hr) a b).continuousAt.continuousWithinAt

include hA hc in
theorem mb_contOn_X {n : ℕ} (σ : Fin (n + 3) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ContinuousOn (fun r => fun x => avM P σ x r) (Icc (0 : ℝ) 1) := fun _ hr =>
  (mb_hasDerivAt_X hA hc σ hσ hr).continuousAt.continuousWithinAt

theorem mb_contOn_coord {k : ℕ} {X : ℝ → (Fin k → Fin N) → ℂ} {s : Set ℝ}
    (hX : ContinuousOn X s) (y : Fin k → Fin N) : ContinuousOn (fun r => X r y) s :=
  (continuous_apply y).comp_continuousOn hX

theorem mb_contOn_oplus {k : ℕ} {T : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {X : ℝ → (Fin k → Fin N) → ℂ} {s : Set ℝ} (hT : ∀ a b, ContinuousOn (fun r => T r a b) s)
    (hX : ContinuousOn X s) : ContinuousOn (fun r => mbOplus (T r) (X r)) s := by
  refine continuousOn_pi.2 fun x => ?_
  unfold mbOplus mbSlot
  exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun c _ =>
    (hT _ _).mul (mb_contOn_coord hX _)

theorem mb_contOn_G {k : ℕ} {T : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {X : ℝ → (Fin k → Fin N) → ℂ} {s : Set ℝ} (hT : ∀ a b, ContinuousOn (fun r => T r a b) s)
    (hX : ContinuousOn X s) (j a : Fin k) : ContinuousOn (fun r => mbG (T r) j a (X r)) s := by
  refine continuousOn_pi.2 fun x => ?_
  unfold mbG mbTr
  exact (hT _ _).mul ((continuousOn_finsetSum _ fun c _ => mb_contOn_coord hX _).add
    (continuousOn_finsetSum _ fun c _ => mb_contOn_coord hX _))

include hA hc in
theorem mb_contOn_F {n : ℕ} (σ : Fin (n + 3) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ContinuousOn (fun r => fun x => mbFM P σ x r) (Icc (0 : ℝ) 1) := by
  have he : ∀ r, (fun x => mbFM P σ x r) =
      (fun x => dMav P σ x r) - mbOplus (mbTheta P r) (fun x => avM P σ x r) := by
    intro r
    funext x
    rw [Pi.sub_apply, mbAvM_evol P σ x r hc.stoch.symm (by omega), mbAvGen_eq_oplus P hσ]
    ring
  rw [show (fun r => fun x => mbFM P σ x r) = fun r =>
    (fun x => dMav P σ x r) - mbOplus (mbTheta P r) (fun x => avM P σ x r) from funext he]
  refine ContinuousOn.sub (continuousOn_pi.2 fun x => ?_)
    (mb_contOn_oplus (mb_contOn_theta hc) (mb_contOn_X hA hc σ hσ))
  exact continuousOn_dMav P hc.zpos.ne' hc.stoch σ x

include hA hc in
theorem mb_contOn_GY {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ContinuousOn (fun r => mbGY P σ r) (Icc (0 : ℝ) 1) := by
  unfold mbGY mbFtX mbFt
  have hX := mb_contOn_X hA hc (n := n + 1) σ hσ
  have hF := mb_contOn_F hA hc (n := n + 1) σ hσ
  have h := (hF.add ((mb_contOn_G (mb_contOn_theta hc) hX (mbJ n) (mbA n)).add
    (mb_contOn_G (mb_contOn_theta hc) hX (mbJ' n) (mbA' n))))
  exact ((mbRegCLM (mbJ' n) (mbA' n)).continuous.comp_continuousOn
    ((mbRegCLM (mbJ n) (mbA n)).continuous.comp_continuousOn h))

end Cont

/-!
## The Duhamel formula for `Y` and for the doubly regularized term
-/

section Duhamel

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

theorem mb_norm_m_lt {z : ℂ} (hz : 0 < z.im) : ‖semicircleM z‖ < 1 :=
  norm_semicircleM_lt_one hz.ne'

theorem mb_norm_mconj_lt {z : ℂ} (hz : 0 < z.im) : ‖conj (semicircleM z)‖ < 1 := by
  rw [Complex.norm_conj]
  exact norm_semicircleM_lt_one hz.ne'

include hc in
theorem mb_contOn_prop {k : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun s => propOp (mbPropSat P k s t)) (Icc (0 : ℝ) 1) := fun _ hs =>
  (hasDerivAt_propOp_vsTensorProp_left hc.stoch (fun _ => mb_norm_m_lt hc.zpos)
    (fun _ => mb_norm_mconj_lt hc.zpos) hs.1 hs.2 ht.1 ht.2).continuousAt.continuousWithinAt

include hc in
theorem mb_intervalIntegrable_prop {k : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {G : ℝ → (Fin k → Fin (m * W)) → ℂ} (hG : ContinuousOn G (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun s => propOp (mbPropSat P k s t) (G s)) volume 0 t := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le ht.1]
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
  exact ((mb_contOn_prop hc ht).mono hsub).clm_apply (hG.mono hsub)

include hA hc in
/-- Duhamel for `Y`: `Y_t = P̂^{⊗}_{0,t} Y_0 + ∫_0^t P̂^{⊗}_{s,t} 𝒟'𝒟(F_s + F̃_s) ds`. -/
theorem mbY_duhamel {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    mbY P σ t = propOp (mbPropSat P (n + 4) 0 t) (mbY P σ 0) +
      ∫ s in (0 : ℝ)..t, propOp (mbPropSat P (n + 4) s t) (mbGY P σ s) := by
  refine vsTensorProp_duhamel hc.stoch (fun _ => mb_norm_m_lt hc.zpos)
    (fun _ => mb_norm_mconj_lt hc.zpos) le_rfl zero_le_one ht.1 ht.2 (fun s hs => ?_)
    (mb_intervalIntegrable_prop hc ht (mb_contOn_GY hA hc σ hσ))
  rw [uIcc_of_le ht.1] at hs
  exact mb_hasDerivAt_Y hA hc σ hσ ⟨hs.1, hs.2.trans ht.2⟩

/-- The two slot operators `T̂^{(J')}_t T̂^{(J)}_t` as one matrix. -/
def mbSS (K : Matrix (Fin N) (Fin N) ℂ) (n : ℕ) :
    Matrix (Fin (n + 4) → Fin N) (Fin (n + 4) → Fin N) ℂ :=
  mbSlotMat (mbJ' n) K * mbSlotMat (mbJ n) K

theorem mbSS_apply (K : Matrix (Fin N) (Fin N) ℂ) {n : ℕ} (f : (Fin (n + 4) → Fin N) → ℂ) :
    propOp (mbSS K n) f = mbSlot K (mbJ' n) (mbSlot K (mbJ n) f) := by
  rw [mbSS, propOp_mul, ContinuousLinearMap.comp_apply, ← mbSlot_eq_propOp,
    ← mbSlot_eq_propOp]

/-- `Θ̊^{(J')}Θ̊^{(J)} f = T̂^{(J')}T̂^{(J)} 𝒟'𝒟 f`. -/
theorem mb_ringring_eq (K : Matrix (Fin N) (Fin N) ℂ) {n : ℕ} (f : (Fin (n + 4) → Fin N) → ℂ) :
    mbRing K (mbJ' n) (mbA' n) (mbRing K (mbJ n) (mbA n) f) =
      mbSlot K (mbJ' n) (mbSlot K (mbJ n) (mbReg (mbJ' n) (mbA' n) (mbReg (mbJ n) (mbA n) f))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mb_slots_distinct n
  rw [mbRing_eq_slot_reg K h6, mbRing_eq_slot_reg K h1, mbReg_slot_comm K h5 h4]

include hc in
theorem mbSS_prop_comm {n : ℕ} {s t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (f : (Fin (n + 4) → Fin (m * W)) → ℂ) :
    propOp (mbSS (mbTheta P t) n) (propOp (mbPropSat P (n + 4) s t) f) =
      propOp (mbPropSat P (n + 4) s t) (propOp (mbSS (mbTheta P t) n) f) := by
  have hcomm : Commute (mbTheta P t)
      (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t) := by
    rw [vsPropagator_eq hc.stoch (mb_norm_mm_lt hc.zpos ht), mbTheta]
    exact (Commute.one_right _).add_right ((Commute.refl _).smul_right _)
  rw [mbSS_apply, mbSS_apply]
  unfold mbPropSat vsTensorProp
  rw [mbSlot_tensor_comm _ _ _ hcomm, mbSlot_tensor_comm _ _ _ hcomm]

/-- The doubly regularized term `Z_t = Θ̊^{(J')}_t Θ̊^{(J)}_t X_t`. -/
def mbZ (P : PsiData N) {n : ℕ} (σ : Fin (n + 4) → Bool) (t : ℝ) :
    (Fin (n + 4) → Fin N) → ℂ :=
  mbRing (mbTheta P t) (mbJ' n) (mbA' n) (mbRing (mbTheta P t) (mbJ n) (mbA n)
    (fun x => avM P σ x t))

include hA hc in

/-- **Duhamel formula for `Z`**: for a saturated pattern of length
`n+4` and `t ∈ [0,1]`,
`Z_t = P̂^{⊗}_{0,t} Θ̊_tΘ̊_t X_0 + ∫_0^t P̂^{⊗}_{s,t} Θ̊_tΘ̊_t (F_s + F̃_s) ds` (rings at `t`).
-/
theorem mbZ_duhamel {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    mbZ P σ t = propOp (mbPropSat P (n + 4) 0 t)
        (mbRing (mbTheta P t) (mbJ' n) (mbA' n) (mbRing (mbTheta P t) (mbJ n) (mbA n)
          (fun x => avM P σ x 0))) +
      ∫ s in (0 : ℝ)..t, propOp (mbPropSat P (n + 4) s t)
        (mbRing (mbTheta P t) (mbJ' n) (mbA' n) (mbRing (mbTheta P t) (mbJ n) (mbA n)
          ((fun x => mbFM P σ x s) + mbFtX P σ s))) := by
  have hint := mb_intervalIntegrable_prop hc ht (mb_contOn_GY hA hc σ hσ)
  have h := congrArg (propOp (mbSS (mbTheta P t) n)) (mbY_duhamel hA hc σ hσ ht)
  rw [map_add, ← (propOp (mbSS (mbTheta P t) n)).intervalIntegral_comp_comm hint,
    mbSS_prop_comm hc ht] at h
  simp_rw [mbSS_prop_comm hc ht, mbSS_apply] at h
  unfold mbY at h
  rw [mbZ, mb_ringring_eq, h, mb_ringring_eq]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [mbGY]
  rw [mb_ringring_eq]

end Duhamel

end BlockBand.Native.ErdosRiabov.MBound
