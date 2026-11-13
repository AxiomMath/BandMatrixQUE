module

public import BlockBand.Native.ErdosRiabov.LLGrid.P7

/-!
# Gain-keeping variants of the (LL) remainder and of the long Duhamel integrand

Throughout, `k = n + 4 ≤ 8` and `β = β_k`.

`Circ.circ_LL_pointwise` and `Circ.circ_integrand_long` bound `L^{β_{k-1}}` and `L^{β_{k-2}}` by
`L^{β_k}` and so lose the gains `L^{-(β_k-β_{k-j})}`. Here the per-term bounds
`Circ.circ_rem*_bound`, `Discharge.extraForcing_long_uncond` are used as they are, and the gains
are moved to a fixed `0 < L' ≤ L_s` (`L' = L_T` along the flow, `L_T ≤ L_s`):

* `rpow_le_mul_gain`: `L^a ≤ L^b L'^{-(b-a)}` for `0 < L' ≤ L`, `a ≤ b`;
* `llR0Gain d ψ^av n L' = 2 C_K² C_w √C₁'' ψ^av_{k-1} L'^{-(β_k-β_{k-1})} +`
  `C_K² C₁'' ψ^av_{k-2} L'^{-(β_k-β_{k-2})}` (the remainder with its gains);
* **`circ_LL_pointwise_gain`**: `η² |T̂^{(k-2)} T̂^{(k)}[𝒳](y)| ≤ η² |Θ̊^{(k-2)} Θ̊^{(k)}[𝒳](y)| +`
  `(2 C_K² C_w √C₁'' ψ^av_{k-1} L^{β_{k-1}} + C_K² C₁'' ψ^av_{k-2} L^{β_{k-2}}) s^av(y)`, and
  `circ_LL_pointwise_gain_le`: the same with `R₀ L^{β}` replaced by `llR0Gain(L') L^{β}`;
* **`circLL_tail_gain`**: `Circ.circLL_tail` with `R₀` replaced by `llR0Gain(L')`, `L' ≤ L_T`;
* **`circ_integrand_long_gain`**: `η_s |(𝓕^av_s + F̃_s)(x)| ≤`
  `C_av Φ^{av,f}_k L_s^{β_k} s^av + 4 C_K √C₁'' ψ^av_{k-1} L_s^{β_{k-1}} s^av`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.LLGrid

open MeasureTheory Set Function Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Circ
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open scoped NNReal ENNReal ComplexConjugate

/-- `L^a ≤ L^b L'^{-(b-a)}` for `0 < L' ≤ L`, `a ≤ b`. -/
theorem rpow_le_mul_gain {L L' a b : ℝ} (hL' : 0 < L') (hLL : L' ≤ L) (hab : a ≤ b) :
    L ^ a ≤ L ^ b * L' ^ (-(b - a)) := by
  have hL : 0 < L := hL'.trans_le hLL
  have e : L ^ a = L ^ b * L ^ (-(b - a)) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hL' hLL (by linarith))
    (Real.rpow_nonneg hL.le _)

/-- **The remainder constant with its gains** at the level `L'`:
`2 C_K² C_w √C₁'' ψ^av_{k-1} L'^{-(β_k-β_{k-1})} + C_K² C₁'' ψ^av_{k-2} L'^{-(β_k-β_{k-2})}`. -/
def llR0Gain (d : VSData) (psiA : ℕ → ℝ) (n : ℕ) (L : ℝ) : ℝ :=
  2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3)) *
      L ^ (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 3))) +
    vsCK d ^ 2 * d.C1pp * psiA (n + 2) * L ^ (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 2)))

/-- `0 ≤ llR0Gain` for `ψ^av ≥ 0`, `L > 0`. -/
theorem llR0Gain_nonneg (d : VSData) {psiA : ℕ → ℝ} (hA : ∀ j, 0 ≤ psiA j) (n : ℕ) {L : ℝ}
    (hL : 0 < L) : 0 ≤ llR0Gain d psiA n L := by
  have hCw : 0 ≤ d.Cwc := le_trans zero_le_one d.one_le_Cwc
  have hC1 : 0 ≤ d.C1pp := le_trans zero_le_one d.one_le_C1pp
  have h3 := hA (n + 3)
  have h2 := hA (n + 2)
  have r3 := Real.rpow_nonneg hL.le (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 3)))
  have r2 := Real.rpow_nonneg hL.le (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 2)))
  unfold llR0Gain
  positivity

/-- **(LL) pointwise, keeping the gains** (deterministic; `Circ.circ_LL_pointwise` without the
upgrades `L^{β_{k-j}} ≤ L^{β_k}`). -/
theorem circ_LL_pointwise_gain (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W)
    (P : PsiData (m * W)) (hPW : P.W = W) (hPD : P.D = d.D)
    (hPS : P.S = shortRingProfile d.b m W) (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
    {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian)
    {psiI psiA : ℕ → ℝ} (hAP : Forcing.APriori P s H psiI psiA)
    (y : Fin (n + 2 + 2) → Fin (m * W)) :
    vsHeight P.z s ^ 2 *
        ‖circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
            (fun y => P.avErr σ y s H)) y‖ ≤
      vsHeight P.z s ^ 2 * ‖ringOp P.S P.z s ⟨n + 1, by omega⟩ ⟨n, by omega⟩
        (ringOp P.S P.z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
          (fun y => P.avErr σ y s H)) y‖ +
      (2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3)) *
          P.lEta s ^ Expo.lossBeta (n + 3) +
        vsCK d ^ 2 * d.C1pp * psiA (n + 2) * P.lEta s ^ Expo.lossBeta (n + 2)) * P.sAv y s := by
  have hS : StochasticSymm P.S := hPS ▸ shortRingProfile_stochasticSymm d.b_pos d.b_lt_half
    (by omega : 3 ≤ m) hW
  have hzi : 0 < P.z.im := hz.im_pos (Nat.mul_pos (by omega) hW)
  have hdec := congrFun (circ_twoSlot_decomp hS hzi.ne' hs (fun y => P.avErr σ y s H)) y
  simp only [Pi.add_apply, Pi.sub_apply] at hdec
  rw [hdec]
  have h1 := circ_remOne_bound d hm hW P hPW hPD hPS hz hn σ hσ hs hH hAP y
  have h2 := circ_remTwo_bound d hm hW P hPW hPD hPS hz hn σ hσ hs hH hAP y
  have h3 := circ_remThree_bound d hm hW P hPW hPD hPS hz hn σ hσ hs hH hAP y
  set A := ringOp P.S P.z s ⟨n + 1, by omega⟩ ⟨n, by omega⟩
    (ringOp P.S P.z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩ (fun y => P.avErr σ y s H)) y
  set B := circRemOne P.S P.z s (fun y => P.avErr σ y s H) y
  set C := circRemTwo P.S P.z s (fun y => P.avErr σ y s H) y
  set D := circRemThree P.S P.z s (fun y => P.avErr σ y s H) y
  have htri : ‖A + B + C - D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
    have a1 := norm_sub_le (A + B + C) D
    have a2 := norm_add_le (A + B) C
    have a3 := norm_add_le A B
    linarith
  have hη2 : 0 ≤ vsHeight P.z s ^ 2 := sq_nonneg _
  have hm1 := mul_le_mul_of_nonneg_left htri hη2
  have e : vsHeight P.z s ^ 2 * (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) = vsHeight P.z s ^ 2 * ‖A‖ +
      vsHeight P.z s ^ 2 * ‖B‖ + vsHeight P.z s ^ 2 * ‖C‖ + vsHeight P.z s ^ 2 * ‖D‖ := by ring
  rw [e] at hm1
  have e2 : (2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3)) *
        P.lEta s ^ Expo.lossBeta (n + 3) +
      vsCK d ^ 2 * d.C1pp * psiA (n + 2) * P.lEta s ^ Expo.lossBeta (n + 2)) * P.sAv y s =
      vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3) *
        P.sAv y s +
      vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3) *
        P.sAv y s +
      vsCK d ^ 2 * d.C1pp * psiA (n + 2) * P.lEta s ^ Expo.lossBeta (n + 2) * P.sAv y s := by
    ring
  rw [e2]
  linarith

/-- The gained remainder of `circ_LL_pointwise_gain` at a level `0 < L' ≤ L`:
`(2 C ψ^av_{k-1} L^{β_{k-1}} + C' ψ^av_{k-2} L^{β_{k-2}}) ≤ llR0Gain(L') L^{β_k}`. -/
theorem rem_gain_le (d : VSData) {psiA : ℕ → ℝ} (hA : ∀ j, 0 ≤ psiA j) {n : ℕ} (hn : n + 4 ≤ 8)
    {L L' : ℝ} (hL' : 0 < L') (hLL : L' ≤ L) :
    2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3)) *
        L ^ Expo.lossBeta (n + 3) +
      vsCK d ^ 2 * d.C1pp * psiA (n + 2) * L ^ Expo.lossBeta (n + 2) ≤
      llR0Gain d psiA n L' * L ^ Expo.lossBeta (n + 4) := by
  have hCw : 0 ≤ d.Cwc := le_trans zero_le_one d.one_le_Cwc
  have hC1 : 0 ≤ d.C1pp := le_trans zero_le_one d.one_le_C1pp
  have h3 := hA (n + 3)
  have h2 := hA (n + 2)
  have c3 : 0 ≤ 2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3)) := by positivity
  have c2 : 0 ≤ vsCK d ^ 2 * d.C1pp * psiA (n + 2) := by positivity
  have g3 := rpow_le_mul_gain hL' hLL (MI.lossBeta_mono (j := n + 3) (by omega) hn)
  have g2 := rpow_le_mul_gain hL' hLL (MI.lossBeta_mono (j := n + 2) (by omega) hn)
  have m3 := mul_le_mul_of_nonneg_left g3 c3
  have m2 := mul_le_mul_of_nonneg_left g2 c2
  unfold llR0Gain
  calc _ ≤ 2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3)) *
        (L ^ Expo.lossBeta (n + 4) * L' ^ (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 3)))) +
      vsCK d ^ 2 * d.C1pp * psiA (n + 2) *
        (L ^ Expo.lossBeta (n + 4) * L' ^ (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 2)))) :=
        add_le_add m3 m2
    _ = _ := by ring

/-- **(LL) pointwise with the gained remainder at the level `L'`**: for `0 < L' ≤ L_s`,
`η² |T̂T̂𝒳(y)| ≤ η² |Θ̊Θ̊𝒳(y)| + llR0Gain(L') L_s^{β_k} s^av(y)`. -/
theorem circ_LL_pointwise_gain_le (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W)
    (P : PsiData (m * W)) (hPW : P.W = W) (hPD : P.D = d.D)
    (hPS : P.S = shortRingProfile d.b m W) (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
    {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian)
    {psiI psiA : ℕ → ℝ} (hA : ∀ j, 0 ≤ psiA j) (hAP : Forcing.APriori P s H psiI psiA) {L' : ℝ}
    (hL' : 0 < L') (hLL : L' ≤ P.lEta s) (y : Fin (n + 2 + 2) → Fin (m * W)) :
    vsHeight P.z s ^ 2 *
        ‖circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
            (fun y => P.avErr σ y s H)) y‖ ≤
      vsHeight P.z s ^ 2 * ‖ringOp P.S P.z s ⟨n + 1, by omega⟩ ⟨n, by omega⟩
        (ringOp P.S P.z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
          (fun y => P.avErr σ y s H)) y‖ +
      llR0Gain d psiA n L' * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hPW' : 0 < P.W := by rw [hPW]; exact hW
  have hsy := (P.sAv_pos hN hPW' (hz.im_pos hN) hs.2 y).le
  have h := circ_LL_pointwise_gain d hm hW P hPW hPD hPS hz hn σ hσ hs hH hAP y
  have hg := mul_le_mul_of_nonneg_right (rem_gain_le d hA hn hL' hLL) hsy
  linarith

section Tail

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

/-- **The fixed-time (LL) tail keeping the gains** (`Circ.circLL_tail` with `R₀` replaced by
`llR0Gain(L')`, `0 < L' ≤ L_T`). -/
theorem circLL_tail_gain {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            B * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    (hAPF : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, (T : WithTop ℝ≥0) ≤ τ x →
      Forcing.APriori P T (pathH p x T) psiI psiA)
    {L' : ℝ} (hL' : 0 < L') (hLT : L' ≤ P.lEta T) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧
        vsHeight P.z T ^ 2 * (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) /
          vsHeight P.z T ^ 2 * P.lEta T * B * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T *
            P.sAv u T + lam) +
          llR0Gain d psiA n L' * P.lEta T ^ Expo.lossBeta (n + 4) * P.sAv u T ≤
        vsHeight P.z T ^ 2 *
          ‖circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) T)
            (circSlot (Fin.last (n + 2 + 1))
              (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) T)
              (fun y => P.avErr σ y T (pathH p x T))) u‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (QV.qvMartGen d P psiI psiA LamM T
        (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z T ^ 2) 1 u *
          QV.qvIntRule d P (2 - 2 * Expo.lossBeta (n + 4)) T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hzi := hz.im_pos hN
  have hPS' : P.S = shortRingProfile d.b p.n p.W := evol_PS_eq d P hb hPS
  have hηT := vsHeight_pos hzi hT1
  refine le_trans (measure_mono_ae ?_)
    (circBound_long μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP hn σ hσ u hB hFB hlam)
  filter_upwards [hAPF] with x hx
  intro hxs
  obtain ⟨hτx, hge⟩ := hxs
  refine ⟨hτx, ?_⟩
  have hpt := circ_LL_pointwise_gain_le d p.n_ge_four p.W_pos P hPW hPD hPS' hz hn σ hσ
    ⟨NNReal.coe_nonneg T, hT1⟩ (H := pathH p x T) (vsBandFin_isHermitian _ _) hAv (hx hτx) hL'
    hLT u
  have h2 : 0 < vsHeight P.z T ^ 2 := pow_pos hηT 2
  have := le_trans hge hpt
  have h3 : vsHeight P.z T ^ 2 * (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) /
      vsHeight P.z T ^ 2 * P.lEta T * B * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T *
        P.sAv u T + lam) ≤
      vsHeight P.z T ^ 2 * ‖ringOp P.S P.z T ⟨n + 1, by omega⟩ ⟨n, by omega⟩
        (ringOp P.S P.z T (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
          (fun y => P.avErr σ y T (pathH p x T))) u‖ := by linarith
  exact le_of_mul_le_mul_left h3 h2

end Tail

/-! ### The long Duhamel integrand keeping the gain of the extra forcing -/

/-- **The long Duhamel integrand at one time, keeping the gain** (`Circ.circ_integrand_long`
without `L^{β_{k-1}} ≤ L^{β_k}`): `η_s |(𝓕^av_s + F̃_s)(x)| ≤`
`C_av Φ^{av,f}_k L_s^{β_k} s^av_s(x) + 4 C_K √C₁'' ψ^av_{k-1} L_s^{β_{k-1}} s^av_s(x)`. -/
theorem circ_integrand_long_gain {p : BlockBand.Parameters} (d : VSData)
    (P : PsiData (p.n * p.W)) (hPW : P.W = p.W) (hPD : P.D = d.D)
    (hPS : P.S = shortRingProfile d.b p.n p.W)
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
      Forcing.avConst d I e (n + 4) *
          Forcing.phiAvF psiI psiA (P.lEta s) (Forcing.yScale P s) (n + 4) *
          P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv x s +
        4 * vsCK d * Real.sqrt d.C1pp * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3) *
          P.sAv x s := by
  have hF := Discharge.forcing_av_uncond c hAP hpsi1 hI hI0 he0 (fun _ h => hE h) (by omega)
    hn σ x
  have hX := Discharge.extraForcing_long_uncond d p.n_ge_four p.W_pos P hPW hPD hPS hz σ hσ hs hH x
  have hΨ : P.bigPsiAv (n + 3) s H ≤ psiA (n + 3) :=
    (hAP (n + 3) (Finset.mem_Icc.mpr ⟨by omega, by norm_num [vsK]; omega⟩)).2
  have hL := c.lEta_pos
  have hs0 := (Forcing.sAv_pos c x).le
  have hLb0 : 0 ≤ P.lEta s ^ Expo.lossBeta (n + 3) := Real.rpow_nonneg hL.le _
  have hA0 : 0 ≤ 4 * vsCK d * Real.sqrt d.C1pp := by
    have := (vsCK_pos d).le
    positivity
  have hX' : vsHeight P.z s * ‖extraForcingLong (n := n) P.S P.z s (fun y => P.avErr σ y s H) x‖
      ≤ 4 * vsCK d * Real.sqrt d.C1pp * psiA (n + 3) * P.lEta s ^ Expo.lossBeta (n + 3) *
        P.sAv x s := by
    refine hX.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hΨ hA0
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hLb0) hs0
    linarith
  have hη := c.height_pos
  have hF' : vsHeight P.z s * ‖forcingAv P σ x s H‖ ≤ Forcing.avConst d I e (n + 4) *
      Forcing.phiAvF psiI psiA (P.lEta s) (Forcing.yScale P s) (n + 4) *
      P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv x s := by
    refine hF.trans (le_of_eq ?_)
    ring
  calc vsHeight P.z s * ‖((fun y => forcingAv P σ y s H) +
        extraForcingLong (n := n) P.S P.z s (fun y => P.avErr σ y s H)) x‖
      ≤ vsHeight P.z s * ‖forcingAv P σ x s H‖ + vsHeight P.z s *
          ‖extraForcingLong (n := n) P.S P.z s (fun y => P.avErr σ y s H) x‖ := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hη.le
    _ ≤ _ := add_le_add hF' hX'

end BlockBand.Native.ErdosRiabov.LLGrid
