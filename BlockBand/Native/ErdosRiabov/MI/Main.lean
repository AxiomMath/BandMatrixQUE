module

public import BlockBand.Native.ErdosRiabov.MI.Noise

/-!
# The master inequalities: the general-`r` forms

Tail bounds for the normalized averaged and isotropic chain fluctuations at a fixed time `T`
before the stopping time, for an arbitrary level `r`.

Setting: VS data (`hb hPS hPW hPD hz hP6`), thresholds `ψ ≥ 1`, the stopping time
`τ = Psi.tau p P ψ ψ^av` (at the thresholds `ψ`), a deterministic `T ∈ [0,1]`,
`Λ_M = Apriori.aprLamM d N` (`N = n W`), `r ≥ 0`. **No a priori or `M`-bound hypothesis**:
the a priori bounds are `Apriori.qvAPriori_of_le_tau`/`qvAPriori_ae`, the isotropic `M`-bound
comes from them, and the extra `M`-bound is `Apriori.mbounds_extra_uncond` with
`e = MI.eMI d N k`. For each family:
`P(T ≤ τ, C_F Φ^f_k(ψ, L_T, Y_T) + r C_M φ^{qv}_k(ψ, L_T) ≤ R_T) ≤ 4 e^{-r²/4}`,
`R_T = |𝒳^k_T(u)|/(L_T^{β_k} s^av_T(u))` resp. `|𝒴^k_T(a,u,b)|/(L_T^{α_k} s^iso_T(a,u,b))`:
* `masterIneq_av_gen` (averaged, non-saturated, `k = n+2`): `C_F = fAvC`, `C_M = mAvC`;
* `masterIneq_iso_gen` (isotropic, `k = n+2`): `C_F = fIsoC`, `C_M = mIsoC`;
* `masterIneq_iso_one_gen` (isotropic, `k = 1`): `C_F = fIsoOneC`, `C_M = mIsoOneC`.
Proof: the Duhamel form at `t = T` for every sample (`Discharge.duhamel_*_uncond`), the zero
initial state, the forcing integrals (`MI.forcingInt_*`) on `{T ≤ τ}` (where the a priori bounds
hold at every
`s ∈ (0,T]`), the a.s. noise identity (`Evol.propagatedNoise_eq_combMg`), the event inclusion
`MI.mi_event_le`, and `QV.martingaleEstimate_*` with `λ = r C_M φ^{qv} L_T^{β/α} s_T`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MI

open MeasureTheory Set Finset
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Forcing
open BlockBand.Native.ErdosRiabov.QV
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open BlockBand.SourceProcess.FiniteDriverIntegration
open Expo (lossAlpha lossBeta)
open scoped NNReal ENNReal

variable {p : BlockBand.Parameters}

section Main

variable (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (d : VSData)
  {P : PsiData (p.n * p.W)} (hb : d.b = p.b) (hPS : P.S = shortRingProfile p.b p.n p.W)
  (hPW : P.W = p.W) (hPD : P.D = d.D) (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2)
  {psiI psiA : ℕ → ℝ} (hpsi : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) (T : ℝ≥0) (hT1 : (T : ℝ) ≤ 1)
include hb hPS hPW hPD hz hP6 hpsi hT1

omit hP6 hT1 in
/-- The a priori input along a sample on `{T ≤ τ}`: `QV.APriori` at every `s ∈ (0, T]`. -/
theorem mi_ap_path (x : RingSample p)
    (hTτ : (T : WithTop ℝ≥0) ≤ tau p P psiI psiA x) :
    ∀ s ∈ Ioc (0 : ℝ) T, QV.APriori P psiI psiA (Apriori.aprLamM d (p.n * p.W)) s
      (pathH p x s) := by
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  intro s hs
  exact Apriori.qvAPriori_of_le_tau d hc (fun k _ => by linarith [(hpsi k).1])
    (fun k _ => by linarith [(hpsi k).2]) x hs.1.le (le_tau_of_le hTτ hs.2)

/-- **The master inequality, non-saturated averaged chains** (general-`r` form): for
`k = n+2 ≤ 8`, a pattern with a non-saturated factor and sites `u`,
`P(T ≤ τ, fAvC Φ^{av,f}_k(ψ, L_T, Y_T) + r mAvC φ^{av,qv}_k(ψ, L_T) ≤ |𝒳^k_T(u)|/(L_T^{β_k}
s^av_T(u))) ≤ 4 e^{-r²/4}`, `τ = tau p P ψ ψ^av`, `Λ_M = aprLamM d N`, `e = eMI d N k`.
-/
theorem masterIneq_av_gen {n : ℕ} (hn : n + 2 ≤ 8) (σ : Fin (n + 2) → Bool)
    (hσ : HasDesatFactor σ) (u : Fin (n + 2) → Fin (p.n * p.W)) {r : ℝ} (hr : 0 ≤ r) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
        fAvC d P (Apriori.aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 2)) n T *
            phiAvF psiI psiA (P.lEta T) (yScale P T) (n + 2) +
          r * (mAvC d P (Apriori.aprLamM d (p.n * p.W)) n T *
            qvPhiAv psiI psiA (n + 2) (P.lEta T)) ≤
        ‖P.avErr σ u T (pathH p x T)‖ / (P.lEta T ^ lossBeta (n + 2) * P.sAv u T)} ≤
      4 * ENNReal.ofReal (Real.exp (-(r ^ 2 / 4))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  set Λ := Apriori.aprLamM d (p.n * p.W)
  set e := eMI d (p.n * p.W) (n + 2)
  have he0 : 0 ≤ e := eMI_nonneg d hN _
  have hτ := tau_isStoppingTime μ hN hW hzi hS psiI psiA
  have hI : ∀ j, 1 ≤ psiI j := fun j => (hpsi j).1
  have hAv : ∀ j, 0 ≤ psiA j := fun j => by linarith [(hpsi j).2]
  have hAPae := Apriori.qvAPriori_ae μ d hc (psiI := psiI) (psiA := psiA)
    (fun k _ => by linarith [(hpsi k).1])
    (fun k _ => by linarith [(hpsi k).2]) T
  have hLT := P.lEta_pos hN hW hzi hT1
  set β := lossBeta (n + 2)
  set den := P.lEta T ^ β * P.sAv u T
  have hden : 0 < den := mul_pos (Real.rpow_pos_of_pos hLT _) (P.sAv_pos hN hW hzi hT1 u)
  set φq := qvPhiAv psiI psiA (n + 2) (P.lEta T)
  have hφq : 0 < φq := qvPhiAv_pos hI hAv (n + 2) hLT
  set M := mAvC d P Λ n T
  have hγM : 0 ≤ 2 - 2 * β := by linarith [qv_beta_le_one (k := n + 2) hn]
  have hQI := qvC_mul_intF_pos d P hPW hz hT1 hγM hLam
  have hM : 0 < M := by
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h2 : 0 < kernelActionConst d := by linarith [kernelActionConst_ge_one d]
    exact mul_pos (mul_pos h1 (pow_pos h2 _)) (Real.sqrt_pos.mpr hQI)
  set lam := r * (M * φq * den)
  have hlam : 0 ≤ lam := mul_nonneg hr (by positivity)
  -- the variance identity `A y = (M φ den)²`
  have hAy : qvMartAv d P psiI psiA Λ T u * qvIntRule d P (2 - 2 * β) T = (M * φq * den) ^ 2 := by
    have h := sq_noise (K := ((n : ℝ) + 2) * kernelActionConst d ^ (n + 2))
      (Q := qvC d * Λ ^ 3) (φ := φq) (Lp := P.lEta T ^ 2) (s := P.sAv u T)
      (y := qvIntRule d P (2 - 2 * β) T) (I := intF d P (2 - 2 * β) T)
      (Lb := P.lEta T ^ β) (by have := hQI; positivity)
      (lp_y d P hPW hz hT1 2 (by push_cast; ring))
    calc _ = (((n : ℝ) + 2) * kernelActionConst d ^ (n + 2)) ^ 2 * (qvC d * Λ ^ 3) * φq ^ 2 *
          P.lEta T ^ 2 * P.sAv u T ^ 2 * qvIntRule d P (2 - 2 * β) T := by
          unfold qvMartAv; ring
      _ = _ := by rw [h]; unfold M mAvC; ring
  have hmart := martingaleEstimate_av μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAPae hn σ
    hσ u hlam
  have hexp : lam ^ 2 / (4 * (M * φq * den) ^ 2) = r ^ 2 / 4 := by
    have : 0 < M * φq * den := by positivity
    simp only [lam]
    field_simp
  rw [hAy, hexp] at hmart
  refine le_trans (mi_event_le _ _ T (fun x => ‖P.avErr σ u T (pathH p x T)‖)
    (fun t x => ‖combMg 0 (Evol.zfam P.z σ) (fun y => avSlots P.S y) (fun _ => 1)
      (fun α s => vsTensorProp P.S (Evol.muAv P σ) (Evol.muNext P σ) s T u α) t x‖)
    (F := fAvC d P Λ e n T * phiAvF psiI psiA (P.lEta T) (yScale P T) (n + 2)) (lam := lam)
    hden (le_of_eq ?_) ?_) hmart
  · rw [show lam / den = r * (M * φq) by simp only [lam]; field_simp]
  · filter_upwards [Evol.propagatedNoise_eq_combMg μ hzi hPS σ (fun y => avSlots P.S y)
      (fun _ => 1) (Evol.norm_muAv hzi.ne' σ) (Evol.norm_muNext hzi.ne' σ)] with x hx hTτ
    have hD := congrFun (Discharge.duhamel_av_uncond (t := (T : ℝ)) hzi hPS (by omega) σ x
      ⟨T.coe_nonneg, hT1⟩) u
    rw [Discharge.circ_avErr_pathH_zero_uncond (by omega) σ x, map_zero] at hD
    simp only [Pi.add_apply, zero_add] at hD
    rw [hx T hT1 u] at hD
    have hFi := forcingInt_av d hb hPS hPW hPD hz hP6 T.2 hT1 hpsi hLam (pathH p x)
      (mi_ap_path d hb hPS hPW hPD hz hpsi T x hTτ) hn he0
      (fun h2 _ s hs => Apriori.mbounds_extra_uncond hc hs.1.le (hs.2.trans hT1) h2) σ hσ u
    rw [hD]
    exact (norm_add_le _ _).trans (add_le_add (hFi.trans (le_of_eq rfl)) le_rfl)

/-- **The master inequality, averaged `k = 1`** (general-`r` form; every one-letter pattern is
non-saturated): `P(T ≤ τ, fAvOneC Φ^{av,f}_1 + r mAvOneC φ^{av,qv}_1 ≤ |𝒳^1_T(u)|/(L_T^{β_1}
s^av_T(u))) ≤ 4 e^{-r²/4}`. The martingale estimate is `QV.martingaleEstimate_avOfPi` at
`n = 0`, `B = C_7`, `j = 1`.
-/
theorem masterIneq_av_one_gen (σ : Fin 1 → Bool) (u : Fin 1 → Fin (p.n * p.W)) {r : ℝ}
    (hr : 0 ≤ r) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
        fAvOneC d P (Apriori.aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) 1) T *
            phiAvF psiI psiA (P.lEta T) (yScale P T) 1 +
          r * (mAvOneC d P (Apriori.aprLamM d (p.n * p.W)) T *
            qvPhiAv psiI psiA 1 (P.lEta T)) ≤
        ‖P.avErr σ u T (pathH p x T)‖ / (P.lEta T ^ lossBeta 1 * P.sAv u T)} ≤
      4 * ENNReal.ofReal (Real.exp (-(r ^ 2 / 4))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  set Λ := Apriori.aprLamM d (p.n * p.W)
  set e := eMI d (p.n * p.W) 1
  have he0 : 0 ≤ e := eMI_nonneg d hN _
  have hτ := tau_isStoppingTime μ hN hW hzi hS psiI psiA
  have hI : ∀ j, 1 ≤ psiI j := fun j => (hpsi j).1
  have hAv : ∀ j, 0 ≤ psiA j := fun j => by linarith [(hpsi j).2]
  have hAPae := Apriori.qvAPriori_ae μ d hc (psiI := psiI) (psiA := psiA)
    (fun k _ => by linarith [(hpsi k).1]) (fun k _ => by linarith [(hpsi k).2]) T
  have hLT := P.lEta_pos hN hW hzi hT1
  set β := lossBeta 1
  set den := P.lEta T ^ β * P.sAv u T
  have hden : 0 < den := mul_pos (Real.rpow_pos_of_pos hLT _) (P.sAv_pos hN hW hzi hT1 u)
  set φq := qvPhiAv psiI psiA 1 (P.lEta T)
  have hφq : 0 < φq := qvPhiAv_pos hI hAv 1 hLT
  set Bc := 1 + vsCK d * d.C1pp / d.cm
  have hBc : 0 < Bc := by
    have h1 := vsCK_pos d
    have h2 := d.cm_pos
    have h3 : 0 < d.C1pp := lt_of_lt_of_le one_pos d.one_le_C1pp
    positivity
  set M := mAvOneC d P Λ T
  have hγM : 0 ≤ 2 - 2 * β := by linarith [qv_beta_le_one (k := 1) (by norm_num)]
  have hQI := qvC_mul_intF_pos d P hPW hz hT1 hγM hLam
  have hM : 0 < M := mul_pos (mul_pos (by norm_num) hBc) (Real.sqrt_pos.mpr hQI)
  set lam := r * (M * φq * den)
  have hlam : 0 ≤ lam := mul_nonneg hr (by positivity)
  have hAy : qvMartGen d P psiI psiA Λ T Bc 1 u * qvIntRule d P (2 - 2 * β) T =
      (M * φq * den) ^ 2 := by
    have h := sq_noise (K := ((0 : ℝ) + 1) * Bc) (Q := qvC d * Λ ^ 3) (φ := φq)
      (Lp := P.lEta T ^ 2) (s := P.sAv u T) (y := qvIntRule d P (2 - 2 * β) T)
      (I := intF d P (2 - 2 * β) T) (Lb := P.lEta T ^ β) (by have := hQI; positivity)
      (lp_y d P hPW hz hT1 2 (by push_cast; ring))
    calc _ = (((0 : ℝ) + 1) * Bc) ^ 2 * (qvC d * Λ ^ 3) * φq ^ 2 *
          P.lEta T ^ 2 * P.sAv u T ^ 2 * qvIntRule d P (2 - 2 * β) T := by
          unfold qvMartGen; push_cast; ring
      _ = _ := by rw [h]; unfold M mAvOneC; ring
  have hmart := martingaleEstimate_avOfPi μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAPae
    (n := 0) (by norm_num) σ u _
    (fun α => by
      have h : ContDiff ℝ 2 _ := contDiff_tensorCoef (S := P.S) (Evol.muAv P σ)
        (Evol.muNext P σ) (T : ℝ) 1 u α
      simpa only [Matrix.mul_one] using h)
    hBc 1 hγM (by norm_num [β])
    (fun s hs => by
      simpa only [pow_one] using
        evol_goodProps_av_one d P hb hPS hPW hz hs.1.le hs.2 hT1 σ u) hlam
  have hexp : lam ^ 2 / (4 * (M * φq * den) ^ 2) = r ^ 2 / 4 := by
    have : 0 < M * φq * den := by positivity
    simp only [lam]
    field_simp
  rw [hAy, hexp] at hmart
  refine le_trans (mi_event_le _ _ T (fun x => ‖P.avErr σ u T (pathH p x T)‖)
    (fun t x => ‖combMg 0 (Evol.zfam P.z σ) (fun y => avSlots P.S y) (fun _ => 1)
      (fun α s => vsTensorProp P.S (Evol.muAv P σ) (Evol.muNext P σ) s T u α) t x‖)
    (F := fAvOneC d P Λ e T * phiAvF psiI psiA (P.lEta T) (yScale P T) 1) (lam := lam)
    hden (le_of_eq ?_) ?_) hmart
  · rw [show lam / den = r * (M * φq) by simp only [lam]; field_simp]
  · filter_upwards [Evol.propagatedNoise_eq_combMg μ hzi hPS σ (fun y => avSlots P.S y)
      (fun _ => 1) (Evol.norm_muAv hzi.ne' σ) (Evol.norm_muNext hzi.ne' σ)] with x hx hTτ
    have hD := congrFun (Discharge.duhamel_av_uncond (t := (T : ℝ)) hzi hPS le_rfl σ x
      ⟨T.coe_nonneg, hT1⟩) u
    rw [Discharge.circ_avErr_pathH_zero_uncond le_rfl σ x, map_zero] at hD
    simp only [Pi.add_apply, zero_add] at hD
    rw [hx T hT1 u] at hD
    have hFi := forcingInt_av_one d hb hPS hPW hPD hz hP6 T.2 hT1 hpsi hLam (pathH p x)
      (mi_ap_path d hb hPS hPW hPD hz hpsi T x hTτ) he0 σ u
    rw [hD]
    exact (norm_add_le _ _).trans (add_le_add (hFi.trans (le_of_eq rfl)) le_rfl)

/-- **The master inequality, isotropic chains `k = n+2`** (general-`r` form): for every pattern
and sites `a, u, b`, `P(T ≤ τ, fIsoC Φ^{iso,f}_k + r mIsoC φ^{iso,qv}_k ≤
|𝒴^k_T(a,u,b)|/(L_T^{α_k} s^iso_T(a,u,b))) ≤ 4 e^{-r²/4}` (martingale part by
`Discharge.martingaleEstimate_iso_uncond`).
-/
theorem masterIneq_iso_gen {n : ℕ} (hn : n + 2 ≤ 8) (σ : Fin (n + 2) → Bool)
    (a b : Fin (p.n * p.W)) (u : Fin (n + 2) → Fin (p.n * p.W)) {r : ℝ} (hr : 0 ≤ r) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
        fIsoC d P (Apriori.aprLamM d (p.n * p.W)) n T *
            phiIsoF psiI psiA (P.lEta T) (yScale P T) (n + 2) +
          r * (mIsoC d P (Apriori.aprLamM d (p.n * p.W)) n T *
            qvPhiIso psiI psiA (n + 2) (P.lEta T)) ≤
        ‖P.isoErr σ a b u T (pathH p x T)‖ / (P.lEta T ^ lossAlpha (n + 2) * P.sIso a b u T)} ≤
      4 * ENNReal.ofReal (Real.exp (-(r ^ 2 / 4))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  set Λ := Apriori.aprLamM d (p.n * p.W)
  have hτ := tau_isStoppingTime μ hN hW hzi hS psiI psiA
  have hI : ∀ j, 1 ≤ psiI j := fun j => (hpsi j).1
  have hAv : ∀ j, 0 ≤ psiA j := fun j => by linarith [(hpsi j).2]
  have hAPae := Apriori.qvAPriori_ae μ d hc (psiI := psiI) (psiA := psiA)
    (fun k _ => by linarith [(hpsi k).1]) (fun k _ => by linarith [(hpsi k).2]) T
  have hLT := P.lEta_pos hN hW hzi hT1
  set α := lossAlpha (n + 2)
  set den := P.lEta T ^ α * P.sIso a b u T
  have hden : 0 < den :=
    mul_pos (Real.rpow_pos_of_pos hLT _) (P.sIso_pos hN hW hzi hT1 a b u)
  set φq := qvPhiIso psiI psiA (n + 2) (P.lEta T)
  have hφq : 0 < φq := qvPhiIso_pos (psiA := psiA) hI (n + 2) hLT
  set M := mIsoC d P Λ n T
  have hγM : 0 ≤ 1 - 2 * α := by linarith [qv_alpha_le_half (k := n + 2) hn]
  have hQI := qvC_mul_intF_pos d P hPW hz hT1 hγM hLam
  have hM : 0 < M := by
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h2 : 0 < kernelActionConst d := by linarith [kernelActionConst_ge_one d]
    exact mul_pos (mul_pos h1 (pow_pos h2 _)) (Real.sqrt_pos.mpr hQI)
  set lam := r * (M * φq * den)
  have hlam : 0 ≤ lam := mul_nonneg hr (by positivity)
  have hAy : qvMartIso d P psiI psiA Λ T a b u * qvIntRule d P (1 - 2 * α) T =
      (M * φq * den) ^ 2 := by
    have h := sq_noise (K := ((n : ℝ) + 2) * kernelActionConst d ^ (n + 1))
      (Q := qvC d * Λ ^ 3) (φ := φq) (Lp := P.lEta T ^ 1) (s := P.sIso a b u T)
      (y := qvIntRule d P (1 - 2 * α) T) (I := intF d P (1 - 2 * α) T)
      (Lb := P.lEta T ^ α) (by have := hQI; positivity)
      (lp_y d P hPW hz hT1 1 (by push_cast; ring))
    calc _ = (((n : ℝ) + 2) * kernelActionConst d ^ (n + 1)) ^ 2 * (qvC d * Λ ^ 3) * φq ^ 2 *
          P.lEta T ^ 1 * P.sIso a b u T ^ 2 * qvIntRule d P (1 - 2 * α) T := by
          unfold qvMartIso; ring
      _ = _ := by rw [h]; unfold M mIsoC; ring
  have hmart := Discharge.martingaleEstimate_iso_uncond μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ
    T hT1 hAPae hn σ a b u hlam
  have hexp : lam ^ 2 / (4 * (M * φq * den) ^ 2) = r ^ 2 / 4 := by
    have : 0 < M * φq * den := by positivity
    simp only [lam]
    field_simp
  rw [hAy, hexp] at hmart
  refine le_trans (mi_event_le _ _ T (fun x => ‖P.isoErr σ a b u T (pathH p x T)‖)
    (fun t x => ‖combMg 0 (Evol.zfam P.z σ) (fun y => isoSlots P.S y)
      (fun _ => Matrix.single b a 1)
      (fun α s => vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α) t x‖)
    (F := fIsoC d P Λ n T * phiIsoF psiI psiA (P.lEta T) (yScale P T) (n + 2)) (lam := lam)
    hden (le_of_eq ?_) ?_) hmart
  · rw [show lam / den = r * (M * φq) by simp only [lam]; field_simp]
  · filter_upwards [Evol.propagatedNoise_eq_combMg μ hzi hPS σ (fun y => isoSlots P.S y)
      (fun _ => Matrix.single b a 1) (Evol.norm_muIso hzi.ne' σ) (Evol.norm_muNext hzi.ne' σ)]
      with x hx hTτ
    have hD := congrFun (Discharge.duhamel_iso_uncond (t := (T : ℝ)) hzi hPS (by omega) σ a b x
      ⟨T.coe_nonneg, hT1⟩) u
    rw [isoErr_pathH_zero (by omega) σ a b x, map_zero] at hD
    simp only [Pi.add_apply, zero_add] at hD
    rw [hx T hT1 u] at hD
    have hFi := forcingInt_iso d hb hPS hPW hPD hz hP6 T.2 hT1 hpsi hLam (pathH p x)
      (mi_ap_path d hb hPS hPW hPD hz hpsi T x hTτ) hn σ a b u
    rw [hD]
    exact (norm_add_le _ _).trans (add_le_add (hFi.trans (le_of_eq rfl)) le_rfl)

/-- **The master inequality, isotropic `k = 1`** (general-`r` form; `U = I`): `P(T ≤ τ,
fIsoOneC Φ^{iso,f}_1 + r mIsoOneC φ^{iso,qv}_1 ≤ |𝒴^1_T(a,u,b)|/(L_T^{α_1} s^iso_T(a,u,b))) ≤
4 e^{-r²/4}` (martingale part by `Discharge.martingaleEstimate_iso_one_uncond`).
-/
theorem masterIneq_iso_one_gen (σ : Fin 1 → Bool) (a b : Fin (p.n * p.W))
    (u : Fin 1 → Fin (p.n * p.W)) {r : ℝ} (hr : 0 ≤ r) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
        fIsoOneC d P (Apriori.aprLamM d (p.n * p.W)) T *
            phiIsoF psiI psiA (P.lEta T) (yScale P T) 1 +
          r * (mIsoOneC d P (Apriori.aprLamM d (p.n * p.W)) T *
            qvPhiIso psiI psiA 1 (P.lEta T)) ≤
        ‖P.isoErr σ a b u T (pathH p x T)‖ / (P.lEta T ^ lossAlpha 1 * P.sIso a b u T)} ≤
      4 * ENNReal.ofReal (Real.exp (-(r ^ 2 / 4))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  set Λ := Apriori.aprLamM d (p.n * p.W)
  have hτ := tau_isStoppingTime μ hN hW hzi hS psiI psiA
  have hI : ∀ j, 1 ≤ psiI j := fun j => (hpsi j).1
  have hAv : ∀ j, 0 ≤ psiA j := fun j => by linarith [(hpsi j).2]
  have hAPae := Apriori.qvAPriori_ae μ d hc (psiI := psiI) (psiA := psiA)
    (fun k _ => by linarith [(hpsi k).1]) (fun k _ => by linarith [(hpsi k).2]) T
  have hLT := P.lEta_pos hN hW hzi hT1
  have hα : lossAlpha 1 = 0 := qv_alpha_of_le_four (by norm_num)
  set den := P.lEta T ^ lossAlpha 1 * P.sIso a b u T
  have hden : 0 < den :=
    mul_pos (Real.rpow_pos_of_pos hLT _) (P.sIso_pos hN hW hzi hT1 a b u)
  set φq := qvPhiIso psiI psiA 1 (P.lEta T)
  have hφq : 0 < φq := qvPhiIso_pos (psiA := psiA) hI 1 hLT
  set M := mIsoOneC d P Λ T
  have hQI := qvC_mul_intF_pos d P hPW hz hT1 (γ := 0) le_rfl hLam
  have hM : 0 < M := mul_pos one_pos (Real.sqrt_pos.mpr hQI)
  set lam := r * (M * φq * den)
  have hlam : 0 ≤ lam := mul_nonneg hr (by positivity)
  have hAy : qvMartIsoOne d P psiI psiA Λ T a b u * qvIntRule d P 0 T = (M * φq * den) ^ 2 := by
    have h := sq_noise (K := 1) (Q := qvC d * Λ ^ 3) (φ := φq) (Lp := P.lEta T ^ 0)
      (s := P.sIso a b u T) (y := qvIntRule d P 0 T) (I := intF d P 0 T)
      (Lb := P.lEta T ^ lossAlpha 1) (by have := hQI; positivity)
      (lp_y d P hPW hz hT1 0 (by rw [hα]; push_cast; ring))
    calc _ = 1 ^ 2 * (qvC d * Λ ^ 3) * φq ^ 2 *
          P.lEta T ^ 0 * P.sIso a b u T ^ 2 * qvIntRule d P 0 T := by
          unfold qvMartIsoOne; ring
      _ = _ := by rw [h]; unfold M mIsoOneC; ring
  have hmart := Discharge.martingaleEstimate_iso_one_uncond μ d hb hPS hPW hPD hz hP6 hLam hI hAv
    hτ T hT1 hAPae σ a b u hlam
  have hexp : lam ^ 2 / (4 * (M * φq * den) ^ 2) = r ^ 2 / 4 := by
    have : 0 < M * φq * den := by positivity
    simp only [lam]
    field_simp
  rw [hAy, hexp] at hmart
  refine le_trans (mi_event_le _ _ T (fun x => ‖P.isoErr σ a b u T (pathH p x T)‖)
    (fun t x => ‖combMg 0 (Evol.zfam P.z σ) (fun y => isoSlots P.S y)
      (fun _ => Matrix.single b a 1)
      (fun α s => vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α) t x‖)
    (F := fIsoOneC d P Λ T * phiIsoF psiI psiA (P.lEta T) (yScale P T) 1) (lam := lam)
    hden (le_of_eq ?_) ?_) hmart
  · rw [show lam / den = r * (M * φq) by simp only [lam]; field_simp]
  · filter_upwards [Evol.propagatedNoise_eq_combMg μ hzi hPS σ (fun y => isoSlots P.S y)
      (fun _ => Matrix.single b a 1) (Evol.norm_muIso hzi.ne' σ) (Evol.norm_muNext hzi.ne' σ)]
      with x hx hTτ
    have hD := congrFun (Discharge.duhamel_iso_uncond (t := (T : ℝ)) hzi hPS le_rfl σ a b x
      ⟨T.coe_nonneg, hT1⟩) u
    rw [isoErr_pathH_zero le_rfl σ a b x, map_zero] at hD
    simp only [Pi.add_apply, zero_add] at hD
    rw [hx T hT1 u] at hD
    have hFi := forcingInt_iso_one d hb hPS hPW hPD hz hP6 T.2 hT1 hpsi hLam (pathH p x)
      (mi_ap_path d hb hPS hPW hPD hz hpsi T x hTτ) σ a b u
    rw [hD]
    exact (norm_add_le _ _).trans (add_le_add (hFi.trans (le_of_eq rfl)) le_rfl)

end Main

end BlockBand.Native.ErdosRiabov.MI
