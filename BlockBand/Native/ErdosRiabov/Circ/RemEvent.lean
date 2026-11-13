module

public import BlockBand.Native.ErdosRiabov.Circ.RemBound

/-!
# The (LL) event: fixed-time tail and the event form of `linTerm_long`

The hypothesis (LL) of `linTerm_long`, a bound on `T̂^{(k-2)} T̂^{(k)}[𝒳]`, holds outside an event
of small probability, and `linTerm_long` holds with (LL) assumed only on an event.

* `circ_LL_pointwise` (deterministic, one time `s`, `Forcing.APriori` at `s`, `L_s ≥ 1`):
  `η² |T̂^{(k-2)} T̂^{(k)}[𝒳](y)| ≤ η² |Θ̊^{(k-2)} Θ̊^{(k)}[𝒳](y)| + R₀ L^{β} s^av(y)`,
  `R₀ = 2 C_K² C_w √C₁ ψ^A_{k-1} + C_K² C₁ ψ^A_{k-2}` (decomposition and the remainder bounds).
* **`circLL_tail`** (the tail of the (LL) event at a fixed time `T`, one site `u`;
  `circBound_long` and `circ_LL_pointwise`): if a.s. `Forcing.APriori` holds at `T` on `{T ≤ τ}`,
  then
  `P(T ≤ τ, η_T²(D_T + λ) + R₀ L_T^β s^av_T(u) ≤ η_T² |T̂^{(k-2)}_T T̂^{(k)}_T[𝒳_T](u)|)`
  `≤ 4 exp(-λ²/(4 A y))`,
  `D_T`, `A y` those of `circBound_long`.
* `circLLEvent B₂ T`: the event `E` of `x` with
  `η_s² |T̂^{(k-2)}_s T̂^{(k)}_s[𝒳_s](y)| ≤ B₂ L_s^β s^av_s(y)`
  for all `s ∈ (0,T]`, `s ≤ τ`, all `y` (its complement is covered by `circLL_tail` on a grid of `s`
  and all `u`).
* **`linTerm_long_event`**: `linTerm_long` with (LL) assumed a.s. on an event `E`;
  conclusion `P(T ≤ τ, x ∈ E, D + λ ≤ |T̂^{(k)}_T[𝒳_T](u)|) ≤ 4 exp(…)`;
  **`linTerm_long_compl`**: `P(T ≤ τ, D + λ ≤ |…|) ≤ 4 exp(…) + P(Eᶜ)`, and
  `linTerm_long_LLEvent`: the same with `E = circLLEvent B₂ T` (no (LL) hypothesis).
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
### The pointwise (LL) bound
-/

/-- **The (LL) quantity, pointwise** (deterministic): under the hypotheses of `circ_LL_bound`
without its two-ring hypothesis:
`η² |T̂^{(k-2)} T̂^{(k)}[𝒳](y)| ≤ η² |Θ̊^{(k-2)} Θ̊^{(k)}[𝒳](y)| +
R₀ L^{β_k} s^av_k(y)`.
-/
theorem circ_LL_pointwise (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W))
    (hPW : P.W = W) (hPD : P.D = d.D) (hPS : P.S = shortRingProfile d.b m W)
    (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z) {n : ℕ} (hn : n + 4 ≤ 8)
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian) {psiI psiA : ℕ → ℝ}
    (hAP : Forcing.APriori P s H psiI psiA) (hL1 : 1 ≤ P.lEta s)
    (y : Fin (n + 2 + 2) → Fin (m * W)) :
    vsHeight P.z s ^ 2 *
        ‖circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
            (fun y => P.avErr σ y s H)) y‖ ≤
      vsHeight P.z s ^ 2 * ‖ringOp P.S P.z s ⟨n + 1, by omega⟩ ⟨n, by omega⟩
        (ringOp P.S P.z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
          (fun y => P.avErr σ y s H)) y‖ +
      (2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3)) +
        vsCK d ^ 2 * d.C1pp * psiA (n + 2)) * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hS : StochasticSymm P.S := hPS ▸ shortRingProfile_stochasticSymm d.b_pos d.b_lt_half
    (by omega : 3 ≤ m) hW
  have hzi : 0 < P.z.im := hz.im_pos hN
  have hPW' : 0 < P.W := by rw [hPW]; exact hW
  have hdec := congrFun (circ_twoSlot_decomp hS hzi.ne' hs (fun y => P.avErr σ y s H)) y
  simp only [Pi.add_apply, Pi.sub_apply] at hdec
  rw [hdec]
  have h1 := circ_remOne_bound d hm hW P hPW hPD hPS hz hn σ hσ hs hH hAP y
  have h2 := circ_remTwo_bound d hm hW P hPW hPD hPS hz hn σ hσ hs hH hAP y
  have h3 := circ_remThree_bound d hm hW P hPW hPD hPS hz hn σ hσ hs hH hAP y
  have hL3 : P.lEta s ^ Expo.lossBeta (n + 3) ≤ P.lEta s ^ Expo.lossBeta (n + 4) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (circ_lossBeta_mono (by omega) hn)
  have hL2 : P.lEta s ^ Expo.lossBeta (n + 2) ≤ P.lEta s ^ Expo.lossBeta (n + 4) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (circ_lossBeta_mono (by omega) hn)
  have hsy := (P.sAv_pos hN hPW' hzi hs.2 y).le
  have hψ3 : 0 ≤ psiA (n + 3) := (P.bigPsiAv_nonneg (k := n + 3) s H).trans
    (hAP (n + 3) (Finset.mem_Icc.mpr ⟨by omega, by norm_num [vsK]; omega⟩)).2
  have hψ2 : 0 ≤ psiA (n + 2) := (P.bigPsiAv_nonneg (k := n + 2) s H).trans
    (hAP (n + 2) (Finset.mem_Icc.mpr ⟨by omega, by norm_num [vsK]; omega⟩)).2
  have hc1 : 0 ≤ vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3) := by
    have := le_trans zero_le_one d.one_le_Cwc
    positivity
  have hc2 : 0 ≤ vsCK d ^ 2 * d.C1pp * psiA (n + 2) := by
    have := le_trans zero_le_one d.one_le_C1pp
    positivity
  have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL3 hc1) hsy
  have e2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL2 hc2) hsy
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
  have := mul_le_mul_of_nonneg_left htri hη2
  nlinarith [this, h1, h2, h3, e1, e2]

/-!
### The fixed-time tail of the (LL) event
-/

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

/-- **The tail of the (LL) event at a fixed time `T`.** Under the hypotheses of `circBound_long`
(with its `B`, `hFB`) and, a.s. on `{T ≤ τ}`, `Forcing.APriori P T H_T ψ^I ψ^A` (e.g.
`Apriori.forcingAPriori_of_le_tau`):
`P(T ≤ τ, η_T² (D_T + λ) + R₀ L_T^β s^av_T(u) ≤ η_T² |T̂^{(k-2)}_T T̂^{(k)}_T[𝒳_T](u)|) ≤
4 exp(-λ²/(4 A y))`.
-/
theorem circLL_tail {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            B * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    (hAPF : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, (T : WithTop ℝ≥0) ≤ τ x →
      Forcing.APriori P T (pathH p x T) psiI psiA)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧
        vsHeight P.z T ^ 2 * (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) /
          vsHeight P.z T ^ 2 * P.lEta T * B * QV.qvIntRule d P (1 - Expo.lossBeta (n + 4)) T *
            P.sAv u T + lam) +
          (2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * psiA (n + 3)) +
            vsCK d ^ 2 * d.C1pp * psiA (n + 2)) * P.lEta T ^ Expo.lossBeta (n + 4) * P.sAv u T ≤
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
  have hL1 := (QV.qvFlow_of d hb hPS hPW hPD hz hP6 hT1).one_le T ⟨NNReal.coe_nonneg T, le_rfl⟩
  have hηT := vsHeight_pos hzi hT1
  refine le_trans (measure_mono_ae ?_)
    (circBound_long μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP hn σ hσ u hB hFB hlam)
  filter_upwards [hAPF] with x hx
  intro hxs
  obtain ⟨hτx, hge⟩ := hxs
  refine ⟨hτx, ?_⟩
  have hpt := circ_LL_pointwise d p.n_ge_four p.W_pos P hPW hPD hPS' hz hn σ hσ
    ⟨NNReal.coe_nonneg T, hT1⟩ (H := pathH p x T) (vsBandFin_isHermitian _ _) (hx hτx) hL1 u
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

/-!
### The (LL) event and the event form of the linear-term bound
-/

/-- **The (LL) event**: the samples `x` with
`η_s² |T̂^{(k-2)}_s T̂^{(k)}_s[𝒳_s](y)| ≤ B₂ L_s^{β_k} s^av_s(y)` for every `s ∈ (0, T]` with
`s ≤ τ x` and every `y`.
-/
def circLLEvent {p : BlockBand.Parameters} (P : PsiData (p.n * p.W)) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (τ : RingSample p → WithTop ℝ≥0) (B₂ : ℝ) (T : ℝ≥0) :
    Set (RingSample p) :=
  {x | ∀ s ∈ Ioc (0 : ℝ) T, ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y,
    vsHeight P.z s ^ 2 *
      ‖circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
        (circSlot (Fin.last (n + 2 + 1))
          (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
          (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
      B₂ * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s}

section LinEvent

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

/-- **The long linear term, event form.** As `linTerm_long`, but the two-ring hypothesis (LL)
is assumed only on an event `E` (a.s. on `E`):
`P(T ≤ τ, x ∈ E, D + λ ≤ |T̂^{(k)}_T[𝒳_T](u)|) ≤ 4 exp(-λ²/(4 A y))`, with the same `D`, `A y`.
-/
theorem linTerm_long_event {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hF : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖forcingAv P σ y s (pathH p x s)‖ ≤ B₁ * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    (E : Set (RingSample p))
    (hLL : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, x ∈ E → ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s ^ 2 *
        ‖circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
            (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
          B₂ * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧ x ∈ E ∧
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
    with x h1 h2 h3'
  intro hx
  obtain ⟨hτx, hxE, hge⟩ := hx
  have h3 := h3' hxE
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

/-- **The long linear term, event form with the complement**: under the hypotheses of
`linTerm_long_event`, `P(T ≤ τ, D + λ ≤ |T̂^{(k)}_T[𝒳_T](u)|) ≤ 4 exp(-λ²/(4 A y)) + P(Eᶜ)`. -/
theorem linTerm_long_compl {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hF : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖forcingAv P σ y s (pathH p x s)‖ ≤ B₁ * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    (E : Set (RingSample p))
    (hLL : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, x ∈ E → ∀ s ∈ Ioc (0 : ℝ) T,
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
          QV.qvIntRule d P (2 - 2 * Expo.lossBeta (n + 4)) T))))) +
        driverLaw (κ := Fin (ringDim p)) μ Eᶜ := by
  have h := linTerm_long_event μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP hn σ hσ u hB₁ hB₂
    hF E hLL hlam
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add h le_rfl))
  intro x hx
  by_cases hxE : x ∈ E
  · exact Or.inl ⟨hx.1, hxE, hx.2⟩
  · exact Or.inr hxE

/-- **The long linear term with the (LL) event `E = circLLEvent B₂ T`** (no (LL) hypothesis):
`P(T ≤ τ, D + λ ≤ |T̂^{(k)}_T[𝒳_T](u)|) ≤ 4 exp(-λ²/(4 A y)) + P(Eᶜ)`. -/
theorem linTerm_long_LLEvent {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hF : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖forcingAv P σ y s (pathH p x s)‖ ≤ B₁ * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
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
          QV.qvIntRule d P (2 - 2 * Expo.lossBeta (n + 4)) T))))) +
        driverLaw (κ := Fin (ringDim p)) μ (circLLEvent P σ τ B₂ T)ᶜ := by
  have h := linTerm_long_event μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP hn σ hσ u hB₁ hB₂
    hF (circLLEvent P σ τ B₂ T) (ae_of_all _ fun x hx => hx) hlam
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add h le_rfl))
  intro x hx
  by_cases hxE : x ∈ circLLEvent P σ τ B₂ T
  · exact Or.inl ⟨hx.1, hxE, hx.2⟩
  · exact Or.inr hxE

end LinEvent

end BlockBand.Native.ErdosRiabov.Circ
