module

public import BlockBand.Native.ErdosRiabov.Circ.BoundShort

/-!
# The two-ring bound for long regularized chains

The tail bound of the doubly regularized chain `𝒵_T` for long chains `k = n+4`.

`𝒵_T = Θ̊^{(k-2)}_T Θ̊^{(k)}_T[𝒳_T]` (`ringOp … ⟨n+1⟩ ⟨n⟩ ∘ ringOp … (Fin.last (n+3)) ⟨n+2⟩`),
`β = β_k`, `C_reg² C_P^k = onestepConst d ² · kernelActionConst d ^ (n+4)`.

* `circ_integrand_long` (deterministic, one time `s`; from `Discharge.forcing_av_uncond` and
  `Discharge.extraForcing_long_uncond`):
  `η_s |(𝓕^av_s + F̃_s)(x)| ≤`
  `(avConst · Φ^{av,f}_k + 4 C_K √C₁'' ψ^A_{k-1}) L_s^{β_k} s^av_{k,s}(x)`
  (`L_s ≥ 1`, `β_{k-1} ≤ β_k`).
* **`circBound_long`**: if a.s. `η_s |(𝓕^av_s + F̃_s)(x)| ≤ B L_s^{β_k} s^av_{k,s}(x)` for
  `s ≤ τ`, `s ∈ (0, T]`, then for `λ ≥ 0`
  `P(T ≤ τ, C_reg² C_P^k B η_T⁻² L_T Λ_{1-β_k}(T) s^av_{k,T}(u) + λ ≤ |𝒵_T(u)|)`
  `≤ 4 exp(-λ²/(4 A y))`,
  `Λ_γ(T) = QV.qvIntRule d P γ T` (`= 2/(γ c_m) L_T^{-γ}` for `γ > 0`), `A y` of
  `QV.martingaleEstimate_twoRings`. With `L_T Λ_{1-β}(T) = 2/((1-β) c_m) L_T^{β}`
  this is the two-ring bound of Erdős–Riabov at the fixed time `T`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open MeasureTheory Set Function
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
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open BlockBand.Native.CEH.Flow
open scoped NNReal ENNReal ComplexConjugate

variable {p : BlockBand.Parameters}

theorem circ_lossBeta_pred_le {n : ℕ} (hn : n + 4 ≤ 8) :
    Expo.lossBeta (n + 3) ≤ Expo.lossBeta (n + 4) := by
  rw [Forcing.lossBeta_eq (by omega)]
  rcases Nat.lt_or_ge (n + 4) 8 with h | h
  · rw [Forcing.lossBeta_eq (by omega)]
    exact Forcing.lossAlpha_mono (by omega)
  · rw [show n + 4 = 8 by omega, Forcing.lossBeta_eight]
    rw [Forcing.lossAlpha_eight]
    norm_num

/-- **The Duhamel integrand of long chains at one time**: under the hypotheses of
`circ_integrand_short` (with the extra `M`-bound `ExtraBAt` at `k = n+4 ≤ 7`) and `n + 4 ≤ 8`:
`η_s |(𝓕^av_s + F̃_s)(x)| ≤ (avConst · Φ^{av,f}_k + 4 C_K √C₁'' ψ^A_{k-1}) L_s^{β_k} s^av_{k,s}(x)`.
-/
theorem circ_integrand_long (d : VSData) (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
    (hPD : P.D = d.D) (hPS : P.S = shortRingProfile d.b p.n p.W)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (c : Forcing.FCtx d P s) {H : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ}
    (hH : H.IsHermitian) {psiI psiA : ℕ → ℝ} (hAP : Forcing.APriori P s H psiI psiA)
    (hpsi1 : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) {I : ℕ → ℝ}
    (hI : ∀ n ∈ kRange, Forcing.IsoBAt P s n (I n)) (hI0 : ∀ n, 0 ≤ I n) {e : ℝ}
    (he0 : 0 ≤ e) {n : ℕ} (hn : n + 4 ≤ 8)
    (hE : n + 4 ≤ 7 → Forcing.ExtraBAt P s (n + 4) e) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (x : Fin (n + 2 + 2) → Fin (p.n * p.W)) :
    vsHeight P.z s * ‖((fun y => forcingAv P σ y s H) +
        extraForcingLong (n := n) P.S P.z s (fun y => P.avErr σ y s H)) x‖ ≤
      (Forcing.avConst d I e (n + 4) *
          Forcing.phiAvF psiI psiA (P.lEta s) (Forcing.yScale P s) (n + 4) +
        4 * vsCK d * Real.sqrt d.C1pp * psiA (n + 3)) * P.lEta s ^ Expo.lossBeta (n + 4) *
          P.sAv x s := by
  have hF := Discharge.forcing_av_uncond c hAP hpsi1 hI hI0 he0 (fun _ h => hE h) (by omega)
    hn σ x
  have hX := Discharge.extraForcing_long_uncond d p.n_ge_four p.W_pos P hPW hPD hPS hz σ hσ hs hH x
  have hΨ : P.bigPsiAv (n + 3) s H ≤ psiA (n + 3) :=
    (hAP (n + 3) (Finset.mem_Icc.mpr ⟨by omega, by norm_num [vsK]; omega⟩)).2
  have hL := c.lEta_pos
  have hs0 := (Forcing.sAv_pos c x).le
  have hLb : P.lEta s ^ Expo.lossBeta (n + 3) ≤ P.lEta s ^ Expo.lossBeta (n + 4) :=
    Real.rpow_le_rpow_of_exponent_le c.one_le_lEta (circ_lossBeta_pred_le hn)
  have hLb0 : 0 ≤ P.lEta s ^ Expo.lossBeta (n + 3) := Real.rpow_nonneg hL.le _
  have hCK := (vsCK_pos d).le
  have hC := Real.sqrt_nonneg d.C1pp
  have hX' : vsHeight P.z s * ‖extraForcingLong (n := n) P.S P.z s (fun y => P.avErr σ y s H) x‖
      ≤ 4 * vsCK d * Real.sqrt d.C1pp * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 4) *
        P.sAv x s := by
    refine hX.trans ?_
    have hA0 : 0 ≤ 4 * vsCK d * Real.sqrt d.C1pp := by positivity
    have hP0 := P.bigPsiAv_nonneg (k := n + 3) s H
    have := mul_le_mul (mul_le_mul_of_nonneg_left hΨ hA0) hLb hLb0
      (mul_nonneg hA0 (hP0.trans hΨ))
    nlinarith [this]
  have hη := c.height_pos
  calc vsHeight P.z s * ‖((fun y => forcingAv P σ y s H) +
        extraForcingLong (n := n) P.S P.z s (fun y => P.avErr σ y s H)) x‖
      ≤ vsHeight P.z s * ‖forcingAv P σ x s H‖ + vsHeight P.z s *
          ‖extraForcingLong (n := n) P.S P.z s (fun y => P.avErr σ y s H) x‖ := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hη.le
    _ ≤ _ := by nlinarith [hF, hX']

section Bound

variable (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (d : VSData)
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

/-- **Bound on the circular term of long chains** (`k = n+4 ≤ 8`, at a fixed time). If a.s., for
`s ∈ (0, T]` with `s ≤ τ` and all `y`, `η_s |(𝓕^av_s + F̃_s)(y)| ≤ B L_s^{β_k} s^av_{k,s}(y)`
(`B ≥ 0`), then for `λ ≥ 0`:
`P(T ≤ τ, C_reg² C_P^k B η_T⁻² L_T Λ_{1-β_k}(T) s^av_{k,T}(u) + λ ≤ |𝒵_T(u)|) ≤ 4 exp(-λ²/(4 A y))`.
-/
theorem circBound_long {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            B * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧
        onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z T ^ 2 * P.lEta T * B *
          QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T * P.sAv u T + lam ≤
        ‖ringOp P.S P.z T ⟨n + 1, by omega⟩ ⟨n, by omega⟩
          (ringOp P.S P.z T (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
            (fun y => P.avErr σ y T (pathH p x T))) u‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (QV.qvMartGen d P psiI psiA LamM T
        (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z T ^ 2) 1 u *
          QV.qvIntRule d P (2 - 2 * Expo.lossBeta (n + 4)) T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hzi := hz.im_pos hN
  have hPS' : P.S = shortRingProfile d.b p.n p.W := evol_PS_eq d P hb hPS
  have hγ : 0 ≤ 1 - Expo.lossBeta (n + 4) := by linarith [QV.qv_beta_le_one (k := n + 4) hn]
  refine le_trans (measure_mono_ae ?_)
    (QV.martingaleEstimate_twoRings μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP hn σ u
      hlam)
  filter_upwards [Discharge.circEvol_long_combMg_uncond μ hzi hPS σ hσ, hFB] with x h1 h2
  intro hx
  obtain ⟨hτx, hge⟩ := hx
  refine ⟨T, le_rfl, hτx, ?_⟩
  have hid := h1 T hT1 u
  have hLT := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hzi hT1
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) /
      vsHeight P.z T ^ 2 * P.lEta T * P.sAv u T := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := QV.qv_onestepConst_pos d
    have := kernelActionConst_ge_one d
    have := (QV.qv_sAv_pos P (QV.qv_ups_pos d hPW hz hT1) hLT u).le
    positivity
  have hint : ‖(∫ s in (0 : ℝ)..T, propOp (goodProp P.S P.z (fun _ => .sat) s T)
      (ringOp P.S P.z T ⟨n + 1, by omega⟩ ⟨n, by omega⟩
        (ringOp P.S P.z T (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
          ((fun x' => forcingAv P σ x' s (pathH p x s)) +
            extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s)))))) u‖ ≤
      ∫ s in (0 : ℝ)..T, K * (B * P.lEta s ^ (-(1 - Expo.lossBeta (n + 4))) *
        (vsHeight P.z s)⁻¹) := by
    refine circ_norm_integral_apply_le _ u (NNReal.coe_nonneg T)
      ((circ_rate_intervalIntegrable d P hPW hz _ B (NNReal.coe_nonneg T) hT1).const_mul K)
      (fun s hs => ?_) (fun s hs => ?_)
    · have := vsHeight_pos hzi (hs.2.trans hT1)
      have := Real.rpow_nonneg (P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hzi
        (hs.2.trans hT1)).le (-(1 - Expo.lossBeta (n + 4)))
      positivity
    · have hs1 : s ≤ 1 := hs.2.trans hT1
      have hηs := vsHeight_pos hzi hs1
      have hLs := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hzi hs1
      have hf : ∀ y, ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            B * P.lEta s ^ Expo.lossBeta (n + 4) / vsHeight P.z s * P.sAv y s := by
        intro y
        have h := h2 s hs (circ_toNNReal_le hs.2 hτx) y
        rw [div_mul_eq_mul_div, le_div_iff₀ hηs]
        linarith
      have hφ : 0 ≤ B * P.lEta s ^ Expo.lossBeta (n + 4) / vsHeight P.z s :=
        div_nonneg (mul_nonneg hB (Real.rpow_nonneg hLs.le _)) hηs.le
      have hreg := regProps_twoRings_apply d p.n_ge_four p.W_pos P hPW hPD hz hs.1.le hs.2 hT1
        (n := n) hφ _ hf u
      rw [← hPS'] at hreg
      refine hreg.trans (le_of_eq ?_)
      have hr : P.lEta s ^ (-(1 - Expo.lossBeta (n + 4))) =
          P.lEta s ^ Expo.lossBeta (n + 4) / P.lEta s := by
        rw [neg_sub, Real.rpow_sub hLs, Real.rpow_one]
      rw [hr, hK]
      field_simp
  have hrule := circ_intRule d P hPW hz (γ := 1 - Expo.lossBeta (n + 4)) (A := B) hγ hB
    (NNReal.coe_nonneg T) hT1
  rw [intervalIntegral.integral_const_mul] at hint
  have hint' := hint.trans (mul_le_mul_of_nonneg_left hrule hK0)
  have htri : ‖ringOp P.S P.z T ⟨n + 1, by omega⟩ ⟨n, by omega⟩
      (ringOp P.S P.z T (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
        (fun y => P.avErr σ y T (pathH p x T))) u‖ ≤
      K * (B * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T) +
        ‖combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
          (fun α s => ((goodProp P.S P.z (fun _ => .sat) s T * circLongMat P.S P.z T :
            Matrix (Sites p (n + 2 + 2)) (Sites p (n + 2 + 2)) ℂ)) u α) T x‖ := by
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add hint' le_rfl)
  have hKe : onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z T ^ 2 *
      P.lEta T * B * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T * P.sAv u T =
        K * (B * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T) := by
    rw [hK]; ring
  rw [hKe] at hge
  linarith

end Bound

end BlockBand.Native.ErdosRiabov.Circ
