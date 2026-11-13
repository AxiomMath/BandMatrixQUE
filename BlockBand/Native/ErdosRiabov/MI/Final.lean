module

public import BlockBand.Native.ErdosRiabov.MI.Sat

/-!
# The master inequalities at the thresholds, `N^{ε'}` form

The averaged and isotropic master inequalities at the zig-step thresholds.

At the thresholds `ψ = Apriori.aprPsiI d N = thrIso N ξ`, `ψ^av = aprPsiA d N = thrAv N ξ`
(`ξ = d.xi`), `τ = tau p P ψ ψ^av`, `Λ_M = aprLamM d N`, `ε' = d.epsP`, the
forcing and quadratic-variation control parameters are `≤` the control parameters
`φ^{av/iso}_{k,T} = phiAv/phiIso N ξ L_T Y_T k` (`Forcing.phiAvF_le_phiAv`,
`phiIsoF_le_phiIso`, `MI.qvPhiAv_le_phiAv`, `MI.qvPhiIso_le_phiIso`). With `r = N^{ε'/2}`:
* `masterIneq_av`, `masterIneq_av_one`, `masterIneq_iso`, `masterIneq_iso_one`, under the
  **absorption inequality** `Absorb C_F C_M N ε'` (`C_F + N^{ε'/2} C_M ≤ N^{ε'}`, an `N ≥ N₀`
  condition):
  `P(T ≤ τ, N^{ε'} φ_{k,T} < R_T) ≤ 4 e^{-N^{ε'}/4}` (i.e. with very high probability
  `𝟙_{T≤τ} R_T ≤ N^{ε'} φ_{k,T}`);
* `masterIneq_sat` (saturated, under `SatLinBound … B q`): the same with `+ q`, under
  `B iF + (C_av iF + N^{ε'/2} C_M) φ ≤ N^{ε'} φ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MI

open MeasureTheory Set Finset
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Forcing
open BlockBand.Native.ErdosRiabov.QV
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Apriori (aprPsiI aprPsiA aprLamM)
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

variable {p : BlockBand.Parameters}

/-- **The absorption inequality** (an `N ≥ N₀` condition): `C_F + N^{ε/2} C_M ≤ N^ε`. -/
def Absorb (F M : ℝ) (N : ℕ) (ε : ℝ) : Prop :=
  F + (N : ℝ) ^ (ε / 2) * M ≤ (N : ℝ) ^ ε

/-- The thresholds are `thrIso`, `thrAv`. -/
theorem aprPsi_eq (d : VSData) (N : ℕ) :
    aprPsiI d N = thrIso N d.xi ∧ aprPsiA d N = thrAv N d.xi :=
  ⟨funext fun k => (psi_eq_thr d N k).1, funext fun k => (psi_eq_thr d N k).2⟩

/-- `F Φ + r (M φ_q) ≤ E φ` from `Φ, φ_q ≤ φ` and `F + r M ≤ E` (`F, M, r ≥ 0`). -/
theorem bound_le {F M Φ φq φ r E : ℝ} (hF : 0 ≤ F) (hM : 0 ≤ M) (hr : 0 ≤ r) (hΦ : Φ ≤ φ)
    (hq : φq ≤ φ) (hφ : 0 ≤ φ) (hA : F + r * M ≤ E) : F * Φ + r * (M * φq) ≤ E * φ := by
  have h1 : F * Φ ≤ F * φ := mul_le_mul_of_nonneg_left hΦ hF
  have h2 : r * (M * φq) ≤ r * (M * φ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hM) hr
  have h3 : (F + r * M) * φ ≤ E * φ := mul_le_mul_of_nonneg_right hA hφ
  nlinarith

/-- `(N^{ε/2})² / 4 = N^ε / 4`. -/
theorem rpow_half_sq (N : ℕ) (ε : ℝ) : ((N : ℝ) ^ (ε / 2)) ^ 2 / 4 = (N : ℝ) ^ ε / 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  push_cast
  ring_nf

theorem mi_N_pos (p : BlockBand.Parameters) : 0 < p.n * p.W :=
  Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos

theorem mi_psi_ge (d : VSData) (p : BlockBand.Parameters) :
    ∀ n, 1 ≤ aprPsiI d (p.n * p.W) n ∧ 1 ≤ aprPsiA d (p.n * p.W) n := fun n =>
  ⟨Apriori.one_le_aprPsiI d (mi_N_pos p) n, Apriori.one_le_aprPsiA d (mi_N_pos p) n⟩

section Final

variable (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (d : VSData)
  {P : PsiData (p.n * p.W)} (hb : d.b = p.b) (hPS : P.S = shortRingProfile p.b p.n p.W)
  (hPW : P.W = p.W) (hPD : P.D = d.D) (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2) (T : ℝ≥0) (hT1 : (T : ℝ) ≤ 1)
include hb hPS hPW hPD hz hP6 hT1

/-- The scalars at `T`: `0 < N`, `0 < L_T`, `0 < Y_T`. -/
theorem mi_scalars : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) ∧ 0 < P.lEta T ∧ 0 < yScale P T := by
  have cT := mi_atT d hb hPS hPW hPD hz hP6 T.2 hT1
  exact ⟨by exact_mod_cast mi_N_pos p, cT.lEta_pos, yScale_pos cT⟩

/-- **The master inequality** (non-saturated averaged chains `k = n+2 ≤ 8`, at the thresholds, fixed
time `T ≤ 1`, from `t_in = 0`): under the absorption inequality `Absorb (fAvC …) (mAvC …) N ε'`,
`P(T ≤ τ, N^{ε'} φ^{av}_{k,T} < |𝒳^k_T(u)|/(L_T^{β_k} s^av_T(u))) ≤ 4 e^{-N^{ε'}/4}`.
-/
theorem masterIneq_av {n : ℕ} (hn : n + 2 ≤ 8) (σ : Fin (n + 2) → Bool)
    (hσ : HasDesatFactor σ) (u : Fin (n + 2) → Fin (p.n * p.W))
    (hAbs : Absorb (fAvC d P (aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 2)) n T)
      (mAvC d P (aprLamM d (p.n * p.W)) n T) (p.n * p.W) d.epsP) :
    driverLaw (κ := Fin (ringDim p)) μ {x |
        (T : WithTop ℝ≥0) ≤ tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) x ∧
        ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
            phiAv ((p.n * p.W : ℕ) : ℝ) d.xi (P.lEta T) (yScale P T) (n + 2) <
          ‖P.avErr σ u T (pathH p x T)‖ / (P.lEta T ^ lossBeta (n + 2) * P.sAv u T)} ≤
      4 * ENNReal.ofReal (Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ d.epsP / 4))) := by
  obtain ⟨hN, hX, hY⟩ := mi_scalars d hb hPS hPW hPD hz hP6 T hT1
  have hpsi := mi_psi_ge d p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  have hr : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 2) := Real.rpow_nonneg hN.le _
  have h := masterIneq_av_gen μ d hb hPS hPW hPD hz hP6 hpsi T hT1 hn σ hσ u hr
  rw [rpow_half_sq] at h
  refine le_trans (measure_mono ?_) h
  intro x hx
  refine ⟨hx.1, le_trans ?_ hx.2.le⟩
  obtain ⟨e1, e2⟩ := aprPsi_eq d (p.n * p.W)
  have hF : 0 ≤ fAvC d P (aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 2)) n T :=
    mul_nonneg (mul_nonneg (avConst_nonneg d (by linarith) (eMI_nonneg d (by exact_mod_cast hN) _)
      _) (pow_nonneg (by linarith [kernelActionConst_ge_one d]) _))
      (intF_nonneg d P hPW hz hT1 (by linarith [qv_beta_le_one (k := n + 2) hn]))
  have hM : 0 ≤ mAvC d P (aprLamM d (p.n * p.W)) n T :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by
      linarith [kernelActionConst_ge_one d]) _)) (Real.sqrt_nonneg _)
  rw [e1, e2]
  exact bound_le hF hM hr (phiAvF_le_phiAv hN hX hY (by omega) hn)
    (qvPhiAv_le_phiAv hN hX hY (by omega) hn) ((phiAvF_nonneg (fun k => ⟨Real.rpow_nonneg
      hN.le _, Real.rpow_nonneg hN.le _⟩) hX.le hY.le _).trans
        (phiAvF_le_phiAv hN hX hY (by omega) hn)) hAbs

/-- **The master inequality** (averaged `k = 1`, at the thresholds): under
`Absorb (fAvOneC …) (mAvOneC …) N ε'`,
`P(T ≤ τ, N^{ε'} φ^{av}_{1,T} < |𝒳^1_T(u)|/(L_T^{β_1} s^av_T(u))) ≤ 4 e^{-N^{ε'}/4}`.
-/
theorem masterIneq_av_one (σ : Fin 1 → Bool) (u : Fin 1 → Fin (p.n * p.W))
    (hAbs : Absorb (fAvOneC d P (aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) 1) T)
      (mAvOneC d P (aprLamM d (p.n * p.W)) T) (p.n * p.W) d.epsP) :
    driverLaw (κ := Fin (ringDim p)) μ {x |
        (T : WithTop ℝ≥0) ≤ tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) x ∧
        ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
            phiAv ((p.n * p.W : ℕ) : ℝ) d.xi (P.lEta T) (yScale P T) 1 <
          ‖P.avErr σ u T (pathH p x T)‖ / (P.lEta T ^ lossBeta 1 * P.sAv u T)} ≤
      4 * ENNReal.ofReal (Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ d.epsP / 4))) := by
  obtain ⟨hN, hX, hY⟩ := mi_scalars d hb hPS hPW hPD hz hP6 T hT1
  have hpsi := mi_psi_ge d p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  have hr : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 2) := Real.rpow_nonneg hN.le _
  have h := masterIneq_av_one_gen μ d hb hPS hPW hPD hz hP6 hpsi T hT1 σ u hr
  rw [rpow_half_sq] at h
  refine le_trans (measure_mono ?_) h
  intro x hx
  refine ⟨hx.1, le_trans ?_ hx.2.le⟩
  obtain ⟨e1, e2⟩ := aprPsi_eq d (p.n * p.W)
  have hC7 : 0 ≤ 1 + vsCK d * d.C1pp / d.cm := by
    have := (vsCK_pos d).le; have := d.one_le_C1pp; have := d.cm_pos; positivity
  have hF : 0 ≤ fAvOneC d P (aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) 1) T :=
    mul_nonneg (mul_nonneg (avConst_nonneg d (by linarith) (eMI_nonneg d (by exact_mod_cast hN) _)
      _) hC7) (intF_nonneg d P hPW hz hT1 (by linarith [qv_beta_le_one (k := 1) (by norm_num)]))
  have hM : 0 ≤ mAvOneC d P (aprLamM d (p.n * p.W)) T :=
    mul_nonneg (mul_nonneg (by norm_num) hC7) (Real.sqrt_nonneg _)
  rw [e1, e2]
  exact bound_le hF hM hr (phiAvF_le_phiAv hN hX hY le_rfl (by norm_num))
    (qvPhiAv_le_phiAv hN hX hY le_rfl (by norm_num)) ((phiAvF_nonneg (fun k => ⟨Real.rpow_nonneg
      hN.le _, Real.rpow_nonneg hN.le _⟩) hX.le hY.le _).trans
        (phiAvF_le_phiAv hN hX hY le_rfl (by norm_num))) hAbs

/-- **The master inequality** (isotropic chains `k = n+2 ≤ 8`, at the thresholds):
under
`Absorb (fIsoC …) (mIsoC …) N ε'`,
`P(T ≤ τ, N^{ε'} φ^{iso}_{k,T} < |𝒴^k_T(a,u,b)|/(L_T^{α_k} s^iso_T(a,u,b))) ≤ 4 e^{-N^{ε'}/4}`.
-/
theorem masterIneq_iso {n : ℕ} (hn : n + 2 ≤ 8) (σ : Fin (n + 2) → Bool)
    (a b : Fin (p.n * p.W)) (u : Fin (n + 2) → Fin (p.n * p.W))
    (hAbs : Absorb (fIsoC d P (aprLamM d (p.n * p.W)) n T) (mIsoC d P (aprLamM d (p.n * p.W)) n T)
      (p.n * p.W) d.epsP) :
    driverLaw (κ := Fin (ringDim p)) μ {x |
        (T : WithTop ℝ≥0) ≤ tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) x ∧
        ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
            phiIso ((p.n * p.W : ℕ) : ℝ) d.xi (P.lEta T) (yScale P T) (n + 2) <
          ‖P.isoErr σ a b u T (pathH p x T)‖ / (P.lEta T ^ lossAlpha (n + 2) * P.sIso a b u T)} ≤
      4 * ENNReal.ofReal (Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ d.epsP / 4))) := by
  obtain ⟨hN, hX, hY⟩ := mi_scalars d hb hPS hPW hPD hz hP6 T hT1
  have hpsi := mi_psi_ge d p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  have hr : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 2) := Real.rpow_nonneg hN.le _
  have h := masterIneq_iso_gen μ d hb hPS hPW hPD hz hP6 hpsi T hT1 hn σ a b u hr
  rw [rpow_half_sq] at h
  refine le_trans (measure_mono ?_) h
  intro x hx
  refine ⟨hx.1, le_trans ?_ hx.2.le⟩
  obtain ⟨e1, e2⟩ := aprPsi_eq d (p.n * p.W)
  have hF : 0 ≤ fIsoC d P (aprLamM d (p.n * p.W)) n T :=
    mul_nonneg (mul_nonneg (isoConst_nonneg d (by linarith) _)
      (pow_nonneg (by linarith [kernelActionConst_ge_one d]) _))
      (intF_nonneg d P hPW hz hT1 (by linarith [qv_alpha_le_half (k := n + 2) hn]))
  have hM : 0 ≤ mIsoC d P (aprLamM d (p.n * p.W)) n T :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by
      linarith [kernelActionConst_ge_one d]) _)) (Real.sqrt_nonneg _)
  rw [e1, e2]
  exact bound_le hF hM hr (phiIsoF_le_phiIso hN hX hY (by omega) hn)
    (qvPhiIso_le_phiIso hN hX hY (by omega) hn) ((phiIsoF_nonneg (fun k => ⟨Real.rpow_nonneg
      hN.le _, Real.rpow_nonneg hN.le _⟩) hX.le hY.le _).trans
        (phiIsoF_le_phiIso hN hX hY (by omega) hn)) hAbs

/-- **The master inequality** (isotropic `k = 1`, at the thresholds): under
`Absorb (fIsoOneC …) (mIsoOneC …) N ε'`,
`P(T ≤ τ, N^{ε'} φ^{iso}_{1,T} < |𝒴^1_T(a,u,b)|/(L_T^{α_1} s^iso_T(a,u,b))) ≤ 4 e^{-N^{ε'}/4}`.
-/
theorem masterIneq_iso_one (σ : Fin 1 → Bool) (a b : Fin (p.n * p.W))
    (u : Fin 1 → Fin (p.n * p.W))
    (hAbs : Absorb (fIsoOneC d P (aprLamM d (p.n * p.W)) T) (mIsoOneC d P (aprLamM d (p.n * p.W)) T)
      (p.n * p.W) d.epsP) :
    driverLaw (κ := Fin (ringDim p)) μ {x |
        (T : WithTop ℝ≥0) ≤ tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) x ∧
        ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
            phiIso ((p.n * p.W : ℕ) : ℝ) d.xi (P.lEta T) (yScale P T) 1 <
          ‖P.isoErr σ a b u T (pathH p x T)‖ / (P.lEta T ^ lossAlpha 1 * P.sIso a b u T)} ≤
      4 * ENNReal.ofReal (Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ d.epsP / 4))) := by
  obtain ⟨hN, hX, hY⟩ := mi_scalars d hb hPS hPW hPD hz hP6 T hT1
  have hpsi := mi_psi_ge d p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  have hr : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 2) := Real.rpow_nonneg hN.le _
  have h := masterIneq_iso_one_gen μ d hb hPS hPW hPD hz hP6 hpsi T hT1 σ a b u hr
  rw [rpow_half_sq] at h
  refine le_trans (measure_mono ?_) h
  intro x hx
  refine ⟨hx.1, le_trans ?_ hx.2.le⟩
  obtain ⟨e1, e2⟩ := aprPsi_eq d (p.n * p.W)
  have hF : 0 ≤ fIsoOneC d P (aprLamM d (p.n * p.W)) T :=
    mul_nonneg (mul_nonneg (isoConst_nonneg d (by linarith) _) zero_le_one)
      (intF_nonneg d P hPW hz hT1 (by rw [qv_alpha_of_le_four (by norm_num)]; norm_num))
  have hM : 0 ≤ mIsoOneC d P (aprLamM d (p.n * p.W)) T :=
    mul_nonneg zero_le_one (Real.sqrt_nonneg _)
  rw [e1, e2]
  exact bound_le hF hM hr (phiIsoF_le_phiIso hN hX hY le_rfl (by norm_num))
    (qvPhiIso_le_phiIso hN hX hY le_rfl (by norm_num)) ((phiIsoF_nonneg (fun k => ⟨Real.rpow_nonneg
      hN.le _, Real.rpow_nonneg hN.le _⟩) hX.le hY.le _).trans
        (phiIsoF_le_phiIso hN hX hY le_rfl (by norm_num))) hAbs

/-- **The master inequality** (saturated averaged chains `k = n+1 ≤ 8`, at the thresholds): under
`SatLinBound μ P ψ ψ^av σ u T B q` and the absorption inequality
`B iF + (C_av iF + N^{ε'/2} mSatC) φ^{av}_{k,T} ≤ N^{ε'} φ^{av}_{k,T}`,
`P(T ≤ τ, N^{ε'} φ^{av}_{k,T} < |𝒳^k_T(u)|/(L_T^{β_k} s^av_T(u))) ≤ 4 e^{-N^{ε'}/4} + q`.
-/
theorem masterIneq_sat {n : ℕ} (hn : n + 1 ≤ 8) (σ : Fin (n + 1) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 1) → Fin (p.n * p.W)) {B q : ℝ} (hB : 0 ≤ B)
    (hlin : SatLinBound μ P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) σ u T B q)
    (hAbs : B * intF d P (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) T +
        (avConst d (fun _ => aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 1)) (n + 1) *
            intF d P (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) T +
          ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 2) * mSatC d P (aprLamM d (p.n * p.W)) n T) *
          phiAv ((p.n * p.W : ℕ) : ℝ) d.xi (P.lEta T) (yScale P T) (n + 1) ≤
        ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
          phiAv ((p.n * p.W : ℕ) : ℝ) d.xi (P.lEta T) (yScale P T) (n + 1)) :
    driverLaw (κ := Fin (ringDim p)) μ {x |
        (T : WithTop ℝ≥0) ≤ tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) x ∧
        ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
            phiAv ((p.n * p.W : ℕ) : ℝ) d.xi (P.lEta T) (yScale P T) (n + 1) <
          ‖P.avErr σ u T (pathH p x T)‖ / (P.lEta T ^ lossBeta (n + 1) * P.sAv u T)} ≤
      4 * ENNReal.ofReal (Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ d.epsP / 4))) +
        ENNReal.ofReal q := by
  obtain ⟨hN, hX, hY⟩ := mi_scalars d hb hPS hPW hPD hz hP6 T hT1
  have hpsi := mi_psi_ge d p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  have hr : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 2) := Real.rpow_nonneg hN.le _
  have h := masterIneq_sat_gen μ d hb hPS hPW hPD hz hP6 hpsi T hT1 hn σ hσ u hB hlin hr
  rw [rpow_half_sq] at h
  refine le_trans (measure_mono ?_) h
  intro x hx
  refine ⟨hx.1, le_trans ?_ hx.2.le⟩
  obtain ⟨e1, e2⟩ := aprPsi_eq d (p.n * p.W)
  have hγ : 0 ≤ ((n : ℝ) + 1) / 2 - lossBeta (n + 1) := by
    by_cases h0 : n = 0
    · subst h0
      rw [lossBeta_eq (by norm_num), qv_alpha_of_le_four (by norm_num)]
      norm_num
    · have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      linarith [qv_beta_le_one (k := n + 1) hn]
  have hI := intF_nonneg d P hPW hz hT1 hγ
  have hC := avConst_nonneg d (by linarith) (eMI_nonneg d (by exact_mod_cast hN) (n + 1)) (n + 1)
    (LamM := aprLamM d (p.n * p.W))
  have hM : 0 ≤ mSatC d P (aprLamM d (p.n * p.W)) n T :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  rw [e1, e2]
  have hΦ := phiAvF_le_phiAv hN hX hY (ξ := d.xi) (by omega : 1 ≤ n + 1) hn
  have hq := qvPhiAv_le_phiAv hN hX hY (ξ := d.xi) (by omega : 1 ≤ n + 1) hn
  refine le_trans ?_ hAbs
  have h1 := mul_le_mul_of_nonneg_left hΦ (mul_nonneg hC hI)
  have h2 := mul_le_mul_of_nonneg_left hq (mul_nonneg hr hM)
  nlinarith

end Final

end BlockBand.Native.ErdosRiabov.MI
