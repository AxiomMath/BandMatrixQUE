module

public import BlockBand.Native.ErdosRiabov.LLGrid.GainCirc

/-!
# The gained (LL) level and its fixed-time tail

The (LL) level with the gains of the remainders kept, and the fixed-time tail bound at that
level.

* **`llGridLevelGain`** `= llCD · B + N^{ε/2} llZ(L) + llR0Gain(L)` and
  **`llLevelGain`** `= 2 llGridLevelGain + 1` (`llR0Gain` keeps the gains
  `L^{-(β_k-β_{k-1})}`, `L^{-(β_k-β_{k-2})}`; `llGridLevel` has `R₀` instead);
* **`llGrid_tail_gain`**: `LLGrid.llGrid_tail` at the gained level (`circLL_tail_gain`).
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
open BlockBand.Native.ErdosRiabov.Circ
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open scoped NNReal ENNReal ComplexConjugate

/-- **The gained grid level** `llCD · B + N^{ε/2} llZ(L) + llR0Gain(L)`. -/
def llGridLevelGain (d : VSData) (psiI psiA : ℕ → ℝ) (LamM : ℝ) (n : ℕ) (B ε : ℝ) (N : ℕ)
    (L : ℝ) : ℝ :=
  llCD d n * B + (N : ℝ) ^ (ε / 2) * llZ d psiI psiA LamM L n + llR0Gain d psiA n L

/-- **The gained (LL) level** `B₂ = 2 (llCD · B + N^{ε/2} llZ(L) + llR0Gain(L)) + 1`. -/
def llLevelGain (d : VSData) (psiI psiA : ℕ → ℝ) (LamM : ℝ) (n : ℕ) (B ε : ℝ) (N : ℕ)
    (L : ℝ) : ℝ :=
  2 * llGridLevelGain d psiI psiA LamM n B ε N L + 1

/-- `0 ≤ llGridLevelGain` for `B ≥ 0`, `L > 0`. -/
theorem llGridLevelGain_nonneg (d : VSData) {psiI psiA : ℕ → ℝ} (hI : ∀ j, 1 ≤ psiI j)
    (hA : ∀ j, 0 ≤ psiA j) (LamM : ℝ) {n : ℕ} (hn : n + 4 ≤ 8) {B : ℝ} (hB : 0 ≤ B) (ε : ℝ)
    (N : ℕ) {L : ℝ} (hL : 0 < L) : 0 ≤ llGridLevelGain d psiI psiA LamM n B ε N L := by
  have h1 := llCD_nonneg d hn
  have h2 := llZ_nonneg d hI hA LamM hL n
  have h3 := llR0Gain_nonneg d hA n hL
  have h4 : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  unfold llGridLevelGain
  positivity

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

/-- **The fixed-time (LL) tail at the gained grid level** (`circLL_tail_gain` with
`λ = N^{ε/2} llZ(L) L_T^{β} s^av_T(u)/η_T²`): for `0 < L ≤ L_T`, `B ≥ 0`, under `hFB`, `hAPF`:
`P(T ≤ τ, llGridLevelGain(B, ε, N, L) L_T^β s^av_T(u) ≤ llQ_T(H_T)(u)) ≤ 4 exp(-N^ε/4)`.
-/
theorem llGrid_tail_gain {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            B * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    (hAPF : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, (T : WithTop ℝ≥0) ≤ τ x →
      Forcing.APriori P T (pathH p x T) psiI psiA)
    (ε : ℝ) {L : ℝ} (hL0 : 0 < L) (hLT : L ≤ P.lEta T) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧
        llGridLevelGain d psiI psiA LamM n B ε (p.n * p.W) L *
            (P.lEta T ^ Expo.lossBeta (n + 4) * P.sAv u T) ≤
          llQ P σ T (pathH p x T) u} ≤
      4 * ENNReal.ofReal (Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ ε / 4))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hηT := vsHeight_pos hzi hT1
  have hη2 : vsHeight P.z T ^ 2 ≠ 0 := (pow_pos hηT 2).ne'
  have hLT1 := (QV.qvFlow_of d hb hPS hPW hPD hz hP6 hT1).one_le T ⟨NNReal.coe_nonneg T, le_rfl⟩
  have hLpos : 0 < P.lEta T := by linarith
  have hL0' : P.lEta T ≠ 0 := hLpos.ne'
  have hsu := P.sAv_pos hN hW hzi hT1 u
  have hcm : 0 < imLower d.kappa d.C0 := d.cm_pos
  have hβ1 := lossBeta_lt_one hn
  have hγ1 : 1 - Expo.lossBeta (n + 4) ≠ 0 := by linarith
  have hγ2 : 2 - 2 * Expo.lossBeta (n + 4) ≠ 0 := by linarith
  have hγ2p : 0 < (2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0 :=
    mul_pos (by linarith) hcm
  have hNr : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast hN
  have hc₁0 := llC1_pos d n
  have hZ0 : 0 ≤ llZ d psiI psiA LamM L n := llZ_nonneg d hI hAv LamM hL0 n
  have hLb0 : 0 < P.lEta T ^ Expo.lossBeta (n + 4) := Real.rpow_pos_of_pos hLpos _
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = ((p.n * p.W : ℕ) : ℝ) ^ (ε / 2) *
      (llZ d psiI psiA LamM L n * P.lEta T ^ Expo.lossBeta (n + 4) * P.sAv u T /
        vsHeight P.z T ^ 2) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by
    have := Real.rpow_nonneg hNr.le (ε / 2)
    rw [hlam]
    positivity
  have htail := circLL_tail_gain μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP hn σ hσ u hB hFB
    hAPF hL0 hLT hlam0
  -- the threshold
  have hpow1 : P.lEta T ^ (-(1 - Expo.lossBeta (n + 4))) =
      P.lEta T ^ Expo.lossBeta (n + 4) / P.lEta T := by
    rw [eq_div_iff hL0', ← Real.rpow_add_one hL0']
    congr 1
    ring
  have hrule1 : QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T =
      2 / ((1 - Expo.lossBeta (n + 4)) * imLower d.kappa d.C0) *
        P.lEta T ^ (-(1 - Expo.lossBeta (n + 4))) := by
    simp only [QV.qvIntRule, hγ1, ↓reduceIte]
  have hthr : vsHeight P.z T ^ 2 * (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) /
        vsHeight P.z T ^ 2 * P.lEta T * B * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T *
          P.sAv u T + lam) +
      llR0Gain d psiA n L * P.lEta T ^ Expo.lossBeta (n + 4) * P.sAv u T =
      llGridLevelGain d psiI psiA LamM n B ε (p.n * p.W) L *
        (P.lEta T ^ Expo.lossBeta (n + 4) * P.sAv u T) := by
    have h1m : (1 - Expo.lossBeta (n + 4)) * imLower d.kappa d.C0 ≠ 0 :=
      (mul_pos (by linarith) hcm).ne'
    rw [hrule1, hpow1, hlam]
    unfold llGridLevelGain llCD llC1
    field_simp
  -- the variance
  have hφ0 : 0 < QV.qvPhiAv psiI psiA (n + 4) (P.lEta T) := QV.qvPhiAv_pos hI hAv (n + 4) hLpos
  have hφΦ : QV.qvPhiAv psiI psiA (n + 4) (P.lEta T) ≤ QV.qvPhiAv psiI psiA (n + 4) L :=
    QV.qvPhiAv_anti (fun j => by linarith [hI j]) hAv hL0 hLT
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ((n : ℝ) + 4) ^ 2 * (QV.qvC d * LamM ^ 3) * llC1 d n ^ 2 *
      (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0)) *
        (P.lEta T ^ Expo.lossBeta (n + 4)) ^ 2 * P.sAv u T ^ 2 / vsHeight P.z T ^ 4 :=
    ⟨_, rfl⟩
  have hqvC := QV.qvC_pos d
  have hQ0 : 0 < Q := by
    have : 0 < LamM ^ 3 := by positivity
    rw [hQ]
    positivity
  have hpow2 : P.lEta T ^ (-(2 - 2 * Expo.lossBeta (n + 4))) =
      (P.lEta T ^ Expo.lossBeta (n + 4)) ^ 2 / P.lEta T ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hL0'), ← Real.rpow_natCast (P.lEta T) 2, ← Real.rpow_add hLpos,
      ← Real.rpow_natCast (P.lEta T ^ Expo.lossBeta (n + 4)) 2, ← Real.rpow_mul hLpos.le]
    congr 1
    push_cast
    ring
  have hrule2 : QV.qvIntRule d P (2 - 2 * Expo.lossBeta (n + 4)) T =
      2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0) *
        P.lEta T ^ (-(2 - 2 * Expo.lossBeta (n + 4))) := by
    simp only [QV.qvIntRule, hγ2, ↓reduceIte]
  have hgen : QV.qvMartGen d P psiI psiA LamM T
      (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z T ^ 2) 1 u =
      (((n + 2 + 1 : ℕ) : ℝ) + 1) ^ 2 * QV.qvC d * LamM ^ 3 *
        QV.qvPhiAv psiI psiA (n + 4) (P.lEta T) ^ 2 *
          (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z T ^ 2) ^ 2 *
            P.lEta T ^ 2 * P.sAv u T ^ 2 := rfl
  have hA : QV.qvMartGen d P psiI psiA LamM T
      (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z T ^ 2) 1 u *
        QV.qvIntRule d P (2 - 2 * Expo.lossBeta (n + 4)) T =
      Q * QV.qvPhiAv psiI psiA (n + 4) (P.lEta T) ^ 2 := by
    rw [hgen, hrule2, hpow2, hQ]
    unfold llC1
    push_cast
    field_simp
    ring
  have hlam2 : lam ^ 2 = ((p.n * p.W : ℕ) : ℝ) ^ ε * (Q * QV.qvPhiAv psiI psiA (n + 4) L ^ 2) := by
    have hs1 : Real.sqrt (QV.qvC d * LamM ^ 3) ^ 2 = QV.qvC d * LamM ^ 3 :=
      Real.sq_sqrt (by positivity)
    have hs2 : Real.sqrt (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0)) ^ 2 =
        2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0) :=
      Real.sq_sqrt (by positivity)
    have hN2 : (((p.n * p.W : ℕ) : ℝ) ^ (ε / 2)) ^ 2 = ((p.n * p.W : ℕ) : ℝ) ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
      congr 1
      push_cast
      ring
    rw [hlam, hQ, llZ]
    calc _ = (((p.n * p.W : ℕ) : ℝ) ^ (ε / 2)) ^ 2 * (((n : ℝ) + 4) ^ 2 *
          Real.sqrt (QV.qvC d * LamM ^ 3) ^ 2 * QV.qvPhiAv psiI psiA (n + 4) L ^ 2 *
          llC1 d n ^ 2 *
          Real.sqrt (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0)) ^ 2 *
          (P.lEta T ^ Expo.lossBeta (n + 4)) ^ 2 * P.sAv u T ^ 2 / (vsHeight P.z T ^ 2) ^ 2) := by
          ring
      _ = _ := by
          rw [hs1, hs2, hN2]
          push_cast
          ring
  -- the exponent
  have hexp : -(lam ^ 2 / (4 * (QV.qvMartGen d P psiI psiA LamM T
      (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z T ^ 2) 1 u *
        QV.qvIntRule d P (2 - 2 * Expo.lossBeta (n + 4)) T))) ≤
      -(((p.n * p.W : ℕ) : ℝ) ^ ε / 4) := by
    rw [hA, hlam2, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have hNe := Real.rpow_nonneg hNr.le ε
    have hsq : QV.qvPhiAv psiI psiA (n + 4) (P.lEta T) ^ 2 ≤
        QV.qvPhiAv psiI psiA (n + 4) L ^ 2 := pow_le_pow_left₀ hφ0.le hφΦ 2
    have := mul_le_mul_of_nonneg_left hsq (mul_nonneg hNe hQ0.le)
    calc ((p.n * p.W : ℕ) : ℝ) ^ ε / 4 * (4 * (Q * QV.qvPhiAv psiI psiA (n + 4) (P.lEta T) ^ 2))
        = ((p.n * p.W : ℕ) : ℝ) ^ ε * Q * QV.qvPhiAv psiI psiA (n + 4) (P.lEta T) ^ 2 := by ring
      _ ≤ ((p.n * p.W : ℕ) : ℝ) ^ ε * Q * QV.qvPhiAv psiI psiA (n + 4) L ^ 2 := this
      _ = _ := by ring
  refine le_trans (measure_mono fun x hx => ?_) (htail.trans ?_)
  · obtain ⟨hτx, hge⟩ := hx
    exact ⟨hτx, (le_of_eq hthr).trans hge⟩
  · exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp))

end Tail

end BlockBand.Native.ErdosRiabov.LLGrid
