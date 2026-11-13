module

public import BlockBand.Native.ErdosRiabov.Circ.BoundLong

/-!
# The linear term of long regularized chains

The Duhamel tail bound of the linear term `T̂^{(k)}_T[𝒳_T]` for long chains `k = n+4`.

* `circ_slotMat_eq`: a one-coordinate action as the one-slot tensor matrix.
* `circ_linPi_first` (the first-line weight): `Σ_α |(P̃_{s,t} T̂^{(k)}_t)(u,α)| s^av_s(α) ≤
  C_K (C_w/η_t) C_P^k (L_t/L_s) s^av_t(u)`.
* `circ_sAv_stepC`: `Σ_b |P̂_{s,t}(u_k, b)| s^av_t(u[k ↦ b]) ≤ C_P (η_s/η_t) s^av_t(u)`.
* `circ_linPi_second` (the second-line weight, with the lifting `circ_linLift`):
  `Σ_α |(P̃_{s,t} P̂^{(k)}_{s,t})(u,α)| s^av_s(α) ≤ C_P^{k+1} (L_t/L_s) (η_s/η_t) s^av_t(u)`.
* **`linTerm_long`**: if a.s., for `s ∈ (0, T]` with `s ≤ τ` and all `y`,
  (F) `η_s |𝓕^av_s(y)| ≤ B₁ L_s^β s^av_s(y)` and (LL) `η_s² |T̂^{(k-2)}_s T̂^{(k)}_s[𝒳_s](y)| ≤
  B₂ L_s^β s^av_s(y)` (the two-ring bound plus the remainder, uniformly in `s`), then
  `P(T ≤ τ, (C_K C_w C_P^k B₁ + C_P^{k+1} B₂) η_T⁻¹ L_T Λ_{1-β}(T) s^av_T(u) + λ ≤
  |T̂^{(k)}_T[𝒳_T](u)|) ≤ 4 exp(-λ²/(4 A y))`, `A y` of `QV.martingaleEstimate_longLinear`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open MeasureTheory Set Function Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open BlockBand.Native.CEH.Flow
open scoped NNReal ENNReal ComplexConjugate

/-!
### Matrices and weights
-/

section Mat

variable {N : ℕ}

/-- A one-coordinate action is the one-slot tensor matrix. -/
theorem circ_slotMat_eq {k : ℕ} (j : Fin k) (A : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.toMatrix' (circSlot j A) =
      tensorMat (Function.update (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) j A) := by
  ext y α
  rw [tensorMat_update_one_apply, LinearMap.toMatrix'_apply, circSlot_apply,
    Finset.sum_eq_single (α j)]
  · rw [Pi.single_apply]
    by_cases h : α = Function.update y j (α j)
    · rw [ite_eq_left h.symm, ite_eq_left h, mul_one]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero]
  · intro c _ hc
    have hne : ¬ α = Function.update y j c := by
      intro h
      apply hc
      rw [h, Function.update_self]
    rw [Pi.single_apply, ite_eq_right (fun h => hne h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem circ_propOp_slot {k : ℕ} (j : Fin k) (A : Matrix (Fin N) (Fin N) ℂ) (f : CircFun N k) :
    propOp (tensorMat (Function.update (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) j A)) f =
      circSlot j A f := by
  rw [← circ_slotMat_eq, circ_propOp_toMatrix']

/-- `‖(V f)(u)‖ ≤ φ Σ_α |V(u,α)| g(α)` when `|f| ≤ φ g`. -/
theorem circ_propOp_le_of_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ)
    (f : ι → ℂ) (g : ι → ℝ) {φ : ℝ} (hf : ∀ y, ‖f y‖ ≤ φ * g y) (u : ι) :
    ‖propOp V f u‖ ≤ φ * ∑ α, ‖V u α‖ * g α := by
  rw [propOp_apply, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  rw [norm_mul]
  calc ‖V u α‖ * ‖f α‖ ≤ ‖V u α‖ * (φ * g α) := mul_le_mul_of_nonneg_left (hf α) (norm_nonneg _)
    _ = φ * (‖V u α‖ * g α) := by ring

/-- A matrix commuting with `S_ℂ` commutes with every propagator. -/
theorem circ_commute_vsPropagator {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : Commute M (cMat S)) {μ μ' : ℂ} (s : ℝ) {t : ℝ}
    (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) : Commute M (vsPropagator S μ μ' s t) := by
  unfold vsPropagator
  refine Commute.mul_right ?_ (commute_inv_of_commute_cMat hS hM ht)
  refine (Commute.one_right M).sub_right ?_
  unfold vsY
  exact (hM.smul_right _).smul_right _

theorem circ_vsPropagator_commute_cMat {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {μ μ' : ℂ} (s : ℝ) {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    Commute (vsPropagator S μ μ' s t) (cMat S) := by
  unfold vsPropagator
  exact (commute_one_sub_vsY_cMat _ _ s).mul_left
    (commute_inv_of_commute_cMat hS (Commute.refl (cMat S)) ht).symm

/-- `P̃_{s,t}` commutes with `P̂^{(k)}_{s,t}` (a one-slot propagator on the last coordinate). -/
theorem circ_goodProp_slotProp_comm {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {z : ℂ} (hz : z.im ≠ 0) {n : ℕ} (s : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (cf : Fin (n + 2 + 2) → PropFactor) :
    (goodProp S z cf s t : Matrix (Fin (n + 2 + 2) → Fin N) (Fin (n + 2 + 2) → Fin N) ℂ) *
        tensorMat (Function.update (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ))
          (Fin.last (n + 2 + 1)) (vsPropagator S (semicircleM z) (conj (semicircleM z)) s t)) =
      tensorMat (Function.update (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ))
          (Fin.last (n + 2 + 1)) (vsPropagator S (semicircleM z) (conj (semicircleM z)) s t)) *
        goodProp S z cf s t := by
  unfold goodProp vsTensorProp
  rw [← tensorMat_mul, ← tensorMat_mul]
  congr 1
  funext j
  by_cases hj : j = Fin.last (n + 2 + 1)
  · subst hj
    rw [Function.update_self]
    have hμ := circ_norm_mu1_lt_one hz (cf (Fin.last (n + 2 + 1)))
    have hμ' := circ_norm_mu2_lt_one hz (cf (Fin.last (n + 2 + 1)))
    have hT := norm_smul_lt_one hμ hμ' ht.1 ht.2
    have hP := circ_vsPropagator_commute_cMat hS (μ := (cf (Fin.last (n + 2 + 1))).mu1 z)
      (μ' := (cf (Fin.last (n + 2 + 1))).mu2 z) s hT
    exact (circ_commute_vsPropagator hS hP s (circ_norm_smul_lt_one hz ht)).eq
  · rw [Function.update_of_ne hj, Matrix.mul_one, Matrix.one_mul]

end Mat

/-!
### The two weights
-/

section Pi

variable {p : BlockBand.Parameters} (d : VSData) {P : PsiData (p.n * p.W)} (hb : d.b = p.b)
  (hPS : P.S = shortRingProfile p.b p.n p.W) (hPW : P.W = p.W) (hPD : P.D = d.D)
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2)
include hb hPS hPW hPD hz hP6

/-- **The first-line weight of the linear term**:
`Σ_α |(P̃_{s,t} T̂^{(k)}_t)(u,α)| s^av_s(α) ≤ C_K (C_w/η_t) C_P^k (L_t/L_s) s^av_t(u)`. -/
theorem circ_linPi_first {n : ℕ} {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (ht1 : t ≤ 1)
    (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) :
    ∑ α, ‖((goodProp P.S P.z (linFactor n) s t * circLinMat P.S P.z t :
        Matrix (Fin (n + 2 + 2) → Fin (p.n * p.W)) (Fin (n + 2 + 2) → Fin (p.n * p.W)) ℂ)) u α‖ *
        P.sAv α s ≤
      vsCK d * (d.Cwc / vsHeight P.z t) * kernelActionConst d ^ (n + 4) *
        (P.lEta t / P.lEta s) * P.sAv u t := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hs1 : s ≤ 1 := hst.trans ht1
  have hS : StochasticSymm (shortRingProfile d.b p.n p.W) :=
    shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (m := p.n) (by have := p.n_ge_four; omega)
      p.W_pos
  have hF := QV.qvFlow_of d hb hPS hPW hPD hz hP6 ht1
  have hinT := hF.inputs t ⟨(hs0.le.trans hst), le_rfl⟩
  have hLs := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hη hs1
  have hg : ∀ y : Fin (n + 2 + 2) → Fin (p.n * p.W), 0 ≤ P.sAv y s := fun y =>
    (QV.qv_sAv_pos P (QV.qv_ups_pos d hPW hz hs1) hLs y).le
  rw [evol_PS_eq d P hb hPS]
  have hcomm := QV.qv_goodProp_circLin_comm hS hη.ne' s ⟨hs0.le.trans hst, ht1⟩ (linFactor n)
  rw [hcomm]
  refine (QV.qv_mulMat_pi _ _ _ hg u).trans ?_
  have hG : ∀ y, ∑ α, ‖goodProp (shortRingProfile d.b p.n p.W) P.z (linFactor n) s t y α‖ *
      P.sAv α s ≤ kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) * P.sAv y t :=
    fun y => goodProps_av_any d p.n_ge_four p.W_pos P hPW hPD hz hs0.le hst ht1
      (linFactor n) ⟨n + 1, by omega⟩ (by simp [linFactor]) y
  have hK : ∀ x y, ‖vsKernel (shortRingProfile d.b p.n p.W) (semicircleM P.z)
      (conj (semicircleM P.z)) t x y‖ ≤ vsCK d * P.ups t x y := by
    intro x y
    have h := (lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos d.C0_ge_one
      d.D_ge_six p.n_ge_four p.W_pos hz (hs0.le.trans hst) ht1).1 x y
    unfold PsiData.ups
    rw [hPW, hPD]
    exact h
  have hC10 := QV.qv_thetaSAv d hinT _ (vsCK_pos d).le hK (n := n + 2) u
  have hRatio : 0 ≤ kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) :=
    mul_nonneg (pow_nonneg (by linarith [kernelActionConst_ge_one d]) _)
      (div_nonneg hinT.lEta_pos.le hLs.le)
  calc _ ≤ ∑ y, ‖circLinMat (shortRingProfile d.b p.n p.W) P.z t u y‖ *
        (kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) * P.sAv y t) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hG y) (norm_nonneg _)
    _ = kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) *
        ∑ y, ‖circLinMat (shortRingProfile d.b p.n p.W) P.z t u y‖ * P.sAv y t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) *
        ∑ b, ‖vsKernel (shortRingProfile d.b p.n p.W) (semicircleM P.z) (conj (semicircleM P.z))
          t (u (Fin.last (n + 2 + 1))) b‖ *
            P.sAv (Function.update u (Fin.last (n + 2 + 1)) b) t := by
        rw [QV.qv_circLinMat_eq, QV.qv_slot_pi]
    _ ≤ kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) *
        (vsCK d * (d.Cwc / vsHeight P.z t) * P.sAv u t) :=
        mul_le_mul_of_nonneg_left hC10 hRatio
    _ = _ := by ring

/-- **The propagator bound on the last site of `s^av`**:
`Σ_b |P̂_{s,t}(u_k, b)| s^av_t(u[k ↦ b]) ≤ C_P (η_s/η_t) s^av_t(u)` (`k = n+4`). -/
theorem circ_sAv_stepC {n : ℕ} {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1)
    (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) :
    ∑ b, ‖vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t
        (u (Fin.last (n + 2 + 1))) b‖ * P.sAv (Function.update u (Fin.last (n + 2 + 1)) b) t ≤
      kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) * P.sAv u t := by
  have _ := hP6
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hLt := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) (hz.im_pos hN) ht1
  set U := P.ups t
  set l := Fin.last (n + 2 + 1)
  set w := u (Fin.last (n + 2)).castSucc
  set R := ∏ e : Fin (n + 2), U (u e.castSucc.castSucc) (u e.castSucc.succ) with hR
  have hcyc : ∀ y : Fin (n + 2 + 2) → Fin (p.n * p.W),
      (∀ e : Fin (n + 2), y e.castSucc.castSucc = u e.castSucc.castSucc ∧
        y e.castSucc.succ = u e.castSucc.succ) → y (Fin.last (n + 2)).castSucc = w →
      y 0 = u 0 → ∏ e : Fin (n + 2 + 2), U (y e) (y (finRotate (n + 2 + 2) e)) =
        R * (U w (y l) * U (y l) (u 0)) := by
    intro y hy hw h0
    rw [circ_cyc_eq, Fin.prod_univ_castSucc, h0]
    have hRy : ∏ e : Fin (n + 2), U (y e.castSucc.castSucc) (y e.castSucc.succ) = R := by
      rw [hR]
      exact Finset.prod_congr rfl fun e _ => by rw [(hy e).1, (hy e).2]
    rw [hRy, show (Fin.last (n + 2)).succ = l from rfl, hw]
    ring
  have hsAv : ∀ y : Fin (n + 2 + 2) → Fin (p.n * p.W),
      (∀ e : Fin (n + 2), y e.castSucc.castSucc = u e.castSucc.castSucc ∧
        y e.castSucc.succ = u e.castSucc.succ) → y (Fin.last (n + 2)).castSucc = w →
      y 0 = u 0 → P.sAv y t = P.lEta t ^ (-((n + 2 + 2 : ℕ) : ℝ) / 2) *
        (Real.sqrt R * Real.sqrt (U w (y l) * U (y l) (u 0))) := by
    intro y hy hw h0
    unfold PsiData.sAv
    rw [ite_eq_right (by omega), hcyc y hy hw h0,
      Real.sqrt_mul (Finset.prod_nonneg fun e _ => ?_)]
    exact (QV.qv_ups_pos d hPW hz ht1 _ _).le
  have hne : ∀ e : Fin (n + 2), e.castSucc.castSucc ≠ l ∧ e.castSucc.succ ≠ l := by
    intro e
    have he := e.isLt
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h' := congrArg Fin.val h
      simp only [Fin.val_castSucc, l, Fin.val_last] at h'
      omega
    · have h' := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc, l, Fin.val_last] at h'
      omega
  have hupd : ∀ b, P.sAv (Function.update u l b) t = P.lEta t ^ (-((n + 2 + 2 : ℕ) : ℝ) / 2) *
      (Real.sqrt R * Real.sqrt (U w b * U b (u 0))) := by
    intro b
    have h := hsAv (Function.update u l b) (fun e => ⟨update_of_ne (hne e).1 _ _,
      update_of_ne (hne e).2 _ _⟩) (update_of_ne (by
        intro h; have := congrArg Fin.val h; simp [l] at this) _ _)
      (update_of_ne (by intro h; have := congrArg Fin.val h; simp [l] at this) _ _)
    rwa [update_self] at h
  have hu : P.sAv u t = P.lEta t ^ (-((n + 2 + 2 : ℕ) : ℝ) / 2) *
      (Real.sqrt R * Real.sqrt (U w (u l) * U (u l) (u 0))) :=
    hsAv u (fun e => ⟨rfl, rfl⟩) rfl rfl
  have hstep := goodProp_stepC_sat d p.n_ge_four p.W_pos hz hs0 hst ht1 (u l) w (u 0)
  have hUe : ∀ x y, polynomialControl (p.n * p.W) p.W d.D (vsHeight P.z t) x y = U x y := by
    intro x y
    simp only [U, PsiData.ups, hPW, hPD]
  simp only [hUe] at hstep
  have hPf : ∀ a, goodPropFactor (shortRingProfile d.b p.n p.W) P.z .sat s t (u l) a =
      vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t (u l) a := by
    intro a
    rw [evol_PS_eq d P hb hPS]
    rfl
  simp only [hPf] at hstep
  simp only [hupd, hu]
  have hc : 0 ≤ P.lEta t ^ (-((n + 2 + 2 : ℕ) : ℝ) / 2) * Real.sqrt R :=
    mul_nonneg (Real.rpow_nonneg hLt.le _) (Real.sqrt_nonneg _)
  calc ∑ b, ‖vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t (u l) b‖ *
        (P.lEta t ^ (-((n + 2 + 2 : ℕ) : ℝ) / 2) * (Real.sqrt R * Real.sqrt (U w b * U b (u 0))))
      = P.lEta t ^ (-((n + 2 + 2 : ℕ) : ℝ) / 2) * Real.sqrt R *
          ∑ b, ‖vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t (u l) b‖ *
            Real.sqrt (U w b * U b (u 0)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
    _ ≤ P.lEta t ^ (-((n + 2 + 2 : ℕ) : ℝ) / 2) * Real.sqrt R *
          (kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) *
            Real.sqrt (U w (u l) * U (u l) (u 0))) := mul_le_mul_of_nonneg_left hstep hc
    _ = _ := by ring

/-- **The second-line weight of the linear term**:
`Σ_α |(P̃_{s,t} P̂^{(k)}_{s,t})(u,α)| s^av_s(α) ≤ C_P^{k+1} (L_t/L_s) (η_s/η_t) s^av_t(u)`. -/
theorem circ_linPi_second {n : ℕ} {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (ht1 : t ≤ 1)
    (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) :
    ∑ α, ‖((goodProp P.S P.z (linFactor n) s t *
        tensorMat (Function.update (fun _ => (1 : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ))
          (Fin.last (n + 2 + 1))
            (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t)) :
        Matrix (Fin (n + 2 + 2) → Fin (p.n * p.W)) (Fin (n + 2 + 2) → Fin (p.n * p.W)) ℂ)) u α‖ *
        P.sAv α s ≤
      kernelActionConst d ^ (n + 4) * (P.lEta t / P.lEta s) *
        (kernelActionConst d * (vsHeight P.z s / vsHeight P.z t)) * P.sAv u t := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hs1 : s ≤ 1 := hst.trans ht1
  have hLs := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hη hs1
  have hLt := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hη ht1
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hg : ∀ y : Fin (n + 2 + 2) → Fin (p.n * p.W), 0 ≤ P.sAv y s := fun y =>
    (QV.qv_sAv_pos P (QV.qv_ups_pos d hPW hz hs1) hLs y).le
  rw [circ_goodProp_slotProp_comm hS hη.ne' s ⟨hs0.le.trans hst, ht1⟩ (linFactor n)]
  refine (QV.qv_mulMat_pi _ _ _ hg u).trans ?_
  have hG : ∀ y, ∑ α, ‖goodProp P.S P.z (linFactor n) s t y α‖ * P.sAv α s ≤
      kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) * P.sAv y t := by
    intro y
    rw [evol_PS_eq d P hb hPS]
    exact goodProps_av_any d p.n_ge_four p.W_pos P hPW hPD hz hs0.le hst ht1
      (linFactor n) ⟨n + 1, by omega⟩ (by simp [linFactor]) y
  have hRatio : 0 ≤ kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) :=
    mul_nonneg (pow_nonneg (by linarith [kernelActionConst_ge_one d]) _)
      (div_nonneg hLt.le hLs.le)
  calc _ ≤ ∑ y, ‖tensorMat (Function.update (fun _ => (1 : Matrix (Fin (p.n * p.W))
          (Fin (p.n * p.W)) ℂ)) (Fin.last (n + 2 + 1))
            (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t)) u y‖ *
        (kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) * P.sAv y t) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hG y) (norm_nonneg _)
    _ = kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) *
        ∑ y, ‖tensorMat (Function.update (fun _ => (1 : Matrix (Fin (p.n * p.W))
          (Fin (p.n * p.W)) ℂ)) (Fin.last (n + 2 + 1))
            (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t)) u y‖ *
          P.sAv y t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) *
        ∑ b, ‖vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s t
          (u (Fin.last (n + 2 + 1))) b‖ *
            P.sAv (Function.update u (Fin.last (n + 2 + 1)) b) t := by
        rw [QV.qv_slot_pi]
    _ ≤ kernelActionConst d ^ (n + 2 + 2) * (P.lEta t / P.lEta s) *
        (kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) * P.sAv u t) :=
        mul_le_mul_of_nonneg_left (circ_sAv_stepC d hb hPS hPW hPD hz hP6 hs0.le hst ht1 u)
          hRatio
    _ = _ := by ring

end Pi

section LinBound

variable {p : BlockBand.Parameters} (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (d : VSData)
  {P : PsiData (p.n * p.W)} (hb : d.b = p.b) (hPS : P.S = shortRingProfile p.b p.n p.W)
  (hPW : P.W = p.W) (hPD : P.D = d.D) (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2)
  {psiI psiA : ℕ → ℝ} {LamM : ℝ} (hLam : 1 ≤ LamM) (hI : ∀ j, 1 ≤ psiI j)
  (hAv : ∀ j, 0 ≤ psiA j) {τ : RingSample p → WithTop ℝ≥0}
  (hτ : IsStoppingTime (driverAugmented (κ := Fin (ringDim p)) μ) τ) (T : ℝ≥0)
  (hT1 : (T : ℝ) ≤ 1)
  (hAP : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
    ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → QV.APriori P psiI psiA LamM s (Evol.pathH p x s))
include hb hPS hPW hPD hz hP6 hLam hI hAv hτ hT1 hAP

/-- D3 M7).
If a.s., for `s ∈ (0, T]` with `s ≤ τ` and all `y`,
`η_s |𝓕^av_s(y)| ≤ B₁ L_s^β s^av_s(y)` and
`η_s² |T̂^{(k-2)}_s T̂^{(k)}_s[𝒳_s](y)| ≤ B₂ L_s^β s^av_s(y)` (`β = β_k`, `B₁, B₂ ≥ 0`), then for
`λ ≥ 0`:
`P(T ≤ τ, (C_K C_w C_P^k B₁ + C_P^k C_P B₂) η_T⁻¹ L_T Λ_{1-β}(T) s^av_T(u) + λ ≤
|T̂^{(k)}_T[𝒳_T](u)|) ≤ 4 exp(-λ²/(4 A y))`, `A y` of `QV.martingaleEstimate_longLinear`.
-/
theorem linTerm_long {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hF : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖forcingAv P σ y s (pathH p x s)‖ ≤ B₁ * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    (hLL : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s ^ 2 *
        ‖circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
            (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
          B₂ * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧
        (vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * B₁ +
            kernelActionConst d ^ (n + 4) * kernelActionConst d * B₂) / vsHeight P.z T *
          P.lEta T * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T * P.sAv u T + lam ≤
        ‖circSlot (Fin.last (n + 2 + 1))
          (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) T)
          (fun y => P.avErr σ y T (pathH p x T)) u‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (QV.qvMartGen d P psiI psiA LamM T
        (vsCK d * (d.Cwc / vsHeight P.z T) * kernelActionConst d ^ (n + 4)) 1 u *
          QV.qvIntRule d P (2 - 2 * Expo.lossBeta (n + 4)) T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hzi := hz.im_pos hN
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hγ : 0 ≤ 1 - Expo.lossBeta (n + 4) := by linarith [QV.qv_beta_le_one (k := n + 4) hn]
  refine le_trans (measure_mono_ae ?_)
    (QV.martingaleEstimate_longLinear μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP hn σ u
      hlam)
  filter_upwards [Discharge.linTerm_evol_combMg_uncond μ hzi hPS σ hσ, hF, hLL]
    with x h1 h2 h3
  intro hx
  obtain ⟨hτx, hge⟩ := hx
  refine ⟨T, le_rfl, hτx, ?_⟩
  have hid := h1 T hT1 u
  have hηT := vsHeight_pos hzi hT1
  have hLT := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hzi hT1
  have hCP := kernelActionConst_ge_one d
  have hCK := vsCK_pos d
  have hCw : 0 ≤ d.Cwc := le_trans zero_le_one d.one_le_Cwc
  obtain ⟨Bp, hBp⟩ : ∃ Bp : ℝ, Bp = vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * B₁ +
      kernelActionConst d ^ (n + 4) * kernelActionConst d * B₂ := ⟨_, rfl⟩
  have hBp0 : 0 ≤ Bp := by rw [hBp]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = P.lEta T * P.sAv u T / vsHeight P.z T := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := (QV.qv_sAv_pos P (QV.qv_ups_pos d hPW hz hT1) hLT u).le
    positivity
  have hint : ‖(∫ s in (0 : ℝ)..T, propOp (goodProp P.S P.z (linFactor n) s T)
      (circSlot (Fin.last (n + 2 + 1))
        (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) T)
        ((fun x' => forcingAv P σ x' s (pathH p x s)) +
          circSlot ⟨n + 1, by omega⟩
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
            (fun y => P.avErr σ y s (pathH p x s))))) u‖ ≤
      ∫ s in (0 : ℝ)..T, K * (Bp * P.lEta s ^ (-(1 - Expo.lossBeta (n + 4))) *
        (vsHeight P.z s)⁻¹) := by
    refine circ_norm_integral_apply_le _ u (NNReal.coe_nonneg T)
      ((circ_rate_intervalIntegrable d P hPW hz _ Bp (NNReal.coe_nonneg T) hT1).const_mul K)
      (fun s hs => ?_) (fun s hs => ?_)
    · have := vsHeight_pos hzi (hs.2.trans hT1)
      have := Real.rpow_nonneg (P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hzi
        (hs.2.trans hT1)).le (-(1 - Expo.lossBeta (n + 4)))
      positivity
    · have hs1 : s ≤ 1 := hs.2.trans hT1
      have hηs := vsHeight_pos hzi hs1
      have hLs := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hzi hs1
      have hsτ := circ_toNNReal_le hs.2 hτx
      have hLb : 0 ≤ P.lEta s ^ Expo.lossBeta (n + 4) := Real.rpow_nonneg hLs.le _
      -- the two lines
      have hsplit : propOp (goodProp P.S P.z (linFactor n) s T)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) T)
            ((fun x' => forcingAv P σ x' s (pathH p x s)) +
              circSlot ⟨n + 1, by omega⟩
                (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
                (fun y => P.avErr σ y s (pathH p x s)))) =
          propOp (goodProp P.S P.z (linFactor n) s T * circLinMat P.S P.z T)
              (fun x' => forcingAv P σ x' s (pathH p x s)) +
            propOp (goodProp P.S P.z (linFactor n) s T *
              tensorMat (Function.update (fun _ => (1 : Matrix (Fin (p.n * p.W))
                (Fin (p.n * p.W)) ℂ)) (Fin.last (n + 2 + 1))
                  (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s T)))
              (circSlot ⟨n + 1, by omega⟩
                (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
                (circSlot (Fin.last (n + 2 + 1))
                  (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
                  (fun y => P.avErr σ y s (pathH p x s)))) := by
        rw [map_add, map_add, circ_linLift hS hzi.ne' ⟨hs.1.le, hs1⟩ ⟨NNReal.coe_nonneg T, hT1⟩,
          propOp_mul, propOp_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          propOp_circLinMat, circ_propOp_slot]
      rw [hsplit, Pi.add_apply]
      have hf1 : ∀ y, ‖forcingAv P σ y s (pathH p x s)‖ ≤
          B₁ * P.lEta s ^ Expo.lossBeta (n + 4) / vsHeight P.z s * P.sAv y s := by
        intro y
        have h := h2 s hs hsτ y
        rw [div_mul_eq_mul_div, le_div_iff₀ hηs]
        linarith
      have hf2 : ∀ y, ‖circSlot ⟨n + 1, by omega⟩
          (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
            (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
          B₂ * P.lEta s ^ Expo.lossBeta (n + 4) / vsHeight P.z s ^ 2 * P.sAv y s := by
        intro y
        have h := h3 s hs hsτ y
        rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hηs 2)]
        linarith
      have e1 := circ_propOp_le_of_pi
        (goodProp P.S P.z (linFactor n) s T * circLinMat P.S P.z T) _ _ hf1 u
      have e2 := circ_propOp_le_of_pi (goodProp P.S P.z (linFactor n) s T *
        tensorMat (Function.update (fun _ => (1 : Matrix (Fin (p.n * p.W))
          (Fin (p.n * p.W)) ℂ)) (Fin.last (n + 2 + 1))
            (vsPropagator P.S (semicircleM P.z) (conj (semicircleM P.z)) s T))) _ _ hf2 u
      have p1 := circ_linPi_first d hb hPS hPW hPD hz hP6 hs.1 hs.2 hT1 (n := n) u
      have p2 := circ_linPi_second d hb hPS hPW hPD hz hP6 hs.1 hs.2 hT1 (n := n) u
      have hφ1 : 0 ≤ B₁ * P.lEta s ^ Expo.lossBeta (n + 4) / vsHeight P.z s := by positivity
      have hφ2 : 0 ≤ B₂ * P.lEta s ^ Expo.lossBeta (n + 4) / vsHeight P.z s ^ 2 := by
        positivity
      have q1 := mul_le_mul_of_nonneg_left p1 hφ1
      have q2 := mul_le_mul_of_nonneg_left p2 hφ2
      refine (norm_add_le _ _).trans ((add_le_add (e1.trans q1) (e2.trans q2)).trans
        (le_of_eq ?_))
      have hr : P.lEta s ^ (-(1 - Expo.lossBeta (n + 4))) =
          P.lEta s ^ Expo.lossBeta (n + 4) / P.lEta s := by
        rw [neg_sub, Real.rpow_sub hLs, Real.rpow_one]
      rw [hr, hK, hBp]
      field_simp
  have hrule := circ_intRule d P hPW hz (γ := 1 - Expo.lossBeta (n + 4)) (A := Bp) hγ hBp0
    (NNReal.coe_nonneg T) hT1
  rw [intervalIntegral.integral_const_mul] at hint
  have hint' := hint.trans (mul_le_mul_of_nonneg_left hrule hK0)
  have htri : ‖circSlot (Fin.last (n + 2 + 1))
      (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) T)
      (fun y => P.avErr σ y T (pathH p x T)) u‖ ≤
      K * (Bp * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T) +
        ‖combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
          (fun α s => ((goodProp P.S P.z (linFactor n) s T * circLinMat P.S P.z T :
            Matrix (Sites p (n + 2 + 2)) (Sites p (n + 2 + 2)) ℂ)) u α) T x‖ := by
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add hint' le_rfl)
  have hKe : (vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * B₁ +
      kernelActionConst d ^ (n + 4) * kernelActionConst d * B₂) / vsHeight P.z T *
        P.lEta T * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T * P.sAv u T =
        K * (Bp * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T) := by
    rw [hK, hBp]; ring
  rw [hKe] at hge
  linarith

end LinBound

end BlockBand.Native.ErdosRiabov.Circ
