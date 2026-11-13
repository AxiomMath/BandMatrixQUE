module

public import BlockBand.Native.ErdosRiabov.LLGrid.Event
public import BlockBand.Native.ErdosRiabov.MI.Conclusion
public import BlockBand.Native.ErdosRiabov.ZigProof.MasterIneq

/-!
# The (LL) event at the thresholds `ψ`, `ψ^av`: all hypotheses discharged

At the zig-step thresholds the (LL) event fails, before `τ`, with probability `≤ N^{-D}` for `N`
large, without further hypotheses.

Setting of `ZigProof.MasterIneqConclusion`: `P = zigPsiData p d.D z`, `τ = zigTau p d z`,
`ψ = zigPsiI d N`, `ψ^av = zigPsiA d N` (called the *P7 thresholds* below, as in the names
`llForcingP7`, `llLevelP7`), `Λ_M = aprLamM d N`, `e = MI.eMI d N k`, `μ = model.law`.

* `llForcingP7 d p z n T = B_T = C_av Φ^{av,f}_k(ψ, L_T, Y_T) + 4 C_K √C₁'' ψ^av_{k-1}`
  (`C_av = avConst d Λ_M e k`): the forcing constant at the final time;
* `llLevelP7 d p z n ε T = llLevel d ψ ψ^av Λ_M n B_T ε N L_T`
  `= 2 (llCD B_T + N^{ε/2} llZ(L_T) + R₀) + 1`;
* `circLLEvent_mono`: the (LL) event grows with the level;
* **`measure_not_circLLEvent_le`**: `∀ d D, 0 < D → ∀ ε > 0, ∃ N₀ : ℕ, ∀ p, p.b = d.b →`
  `N₀ ≤ N → N^{1+ζ₀} ≤ W² → ∀ model z, z ∈ 𝒟 → ∀ T ≤ 1, ∀ n, n + 4 ≤ 8 → ∀ σ saturated,`
  `P(T ≤ τ ∧ x ∉ circLLEvent P σ τ (llLevelP7 d p z n ε T) T) ≤ N^{-D}`;
  **`measure_not_circLLEvent_le_of_le`**: the same for every `B₂ ≥ llLevelP7 d p z n ε T`.
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
open BlockBand.Native.ErdosRiabov.Assembly (zigPsiData)
open BlockBand.Native.ErdosRiabov.ZigProof (zigPsiI zigPsiA zigTau)
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open scoped NNReal ENNReal ComplexConjugate

variable {p : BlockBand.Parameters}

/-- **The forcing constant at the final time** `B_T = C_av Φ^{av,f}_k(ψ, L_T, Y_T) +
4 C_K √C₁'' ψ^av_{k-1}` (`k = n + 4`, P7 thresholds, `Λ_M = aprLamM`, `e = MI.eMI d N k`).
-/
def llForcingP7 (d : VSData) (p : BlockBand.Parameters) (z : ℂ) (n : ℕ) (T : ℝ) : ℝ :=
  Forcing.avConst d (fun _ => Apriori.aprLamM d (p.n * p.W)) (MI.eMI d (p.n * p.W) (n + 4))
      (n + 4) *
    Forcing.phiAvF (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W))
      ((zigPsiData p d.D z).lEta T) (Forcing.yScale (zigPsiData p d.D z) T) (n + 4) +
  4 * vsCK d * Real.sqrt d.C1pp * zigPsiA d (p.n * p.W) (n + 3)

/-- **The (LL) level at the P7 thresholds**
`B₂ = llLevel d ψ ψ^av Λ_M n B_T ε N L_T = 2 (llCD B_T + N^{ε/2} llZ(L_T) + R₀) + 1`.
-/
def llLevelP7 (d : VSData) (p : BlockBand.Parameters) (z : ℂ) (n : ℕ) (ε T : ℝ) : ℝ :=
  llLevel d (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) (Apriori.aprLamM d (p.n * p.W)) n
    (llForcingP7 d p z n T) ε (p.n * p.W) ((zigPsiData p d.D z).lEta T)

/-- The P7 thresholds are `≥ 1`. -/
theorem zig_psi_ge (d : VSData) (p : BlockBand.Parameters) (j : ℕ) :
    1 ≤ zigPsiI d (p.n * p.W) j ∧ 1 ≤ zigPsiA d (p.n * p.W) j := by
  have hN : 1 ≤ p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  exact ⟨Apriori.one_le_aprPsiI d hN j, Apriori.one_le_aprPsiA d hN j⟩

/-- `0 ≤ B_T` for `T ≤ 1`. -/
theorem llForcingP7_nonneg (d : VSData) (p : BlockBand.Parameters) {z : ℂ} (hz : 0 < z.im)
    (n : ℕ) {T : ℝ} (hT1 : T ≤ 1) : 0 ≤ llForcingP7 d p z n T := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hL := (zigPsiData p d.D z).lEta_pos hN p.W_pos hz hT1
  have hY : 0 ≤ Forcing.yScale (zigPsiData p d.D z) T := by
    unfold Forcing.yScale
    exact div_nonneg (Real.sqrt_nonneg _) hL.le
  have hc := MI.avConst_nonneg d (le_trans zero_le_one (MI.aprLamM_one_le d hN))
    (MI.eMI_nonneg d hN (n + 4)) (n + 4)
  have hpsi0 : ∀ j, 0 ≤ zigPsiI d (p.n * p.W) j ∧ 0 ≤ zigPsiA d (p.n * p.W) j := fun j =>
    ⟨le_trans zero_le_one (zig_psi_ge d p j).1, le_trans zero_le_one (zig_psi_ge d p j).2⟩
  have hφ := Forcing.phiAvF_nonneg hpsi0 hL.le hY (n + 4)
  have hA := (zig_psi_ge d p (n + 3)).2
  have hCK := (vsCK_pos d).le
  unfold llForcingP7
  have : 0 ≤ Real.sqrt d.C1pp := Real.sqrt_nonneg _
  have : 0 ≤ zigPsiA d (p.n * p.W) (n + 3) := by linarith
  positivity

/-- **`hFB` at the P7 thresholds with `B = B_T`**:
for `s ∈ (0, T]`, `s ≤ τ(x)`, `η_s |(𝓕^av_s + F̃_s)(y)| ≤ B_T L_s^{β_k} s^av_s(y)`.
-/
theorem forcing_le_T (d : VSData) (hb : d.b = p.b) (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤
    (p.W : ℝ) ^ 2) {z : ℂ} (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z) {T : ℝ}
    (hT1 : T ≤ 1) {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (x : RingSample p) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) T)
    (hsτ : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ zigTau p d z x)
    (y : Fin (n + 2 + 2) → Fin (p.n * p.W)) :
    vsHeight (zigPsiData p d.D z).z s *
        ‖((fun x' => forcingAv (zigPsiData p d.D z) σ x' s (pathH p x s)) +
          extraForcingLong (zigPsiData p d.D z).S (zigPsiData p d.D z).z s
            (fun y => (zigPsiData p d.D z).avErr σ y s (pathH p x s))) y‖ ≤
      llForcingP7 d p z n T * (zigPsiData p d.D z).lEta s ^ Expo.lossBeta (n + 4) *
        (zigPsiData p d.D z).sAv y s := by
  set P := zigPsiData p d.D z
  have hPS : P.S = shortRingProfile p.b p.n p.W := rfl
  have hPW : P.W = p.W := rfl
  have hPD : P.D = d.D := rfl
  have hz' : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z := hz
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := p.W_pos
  have hzi := hz'.im_pos hN
  have hPS' : P.S = shortRingProfile d.b p.n p.W := by rw [hPS, hb]
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz'
  have hs0 : 0 ≤ s := hs.1.le
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have hpsi := zig_psi_ge d p
  have hQ := Apriori.qvAPriori_of_le_tau d hc (psiI := zigPsiI d (p.n * p.W))
    (psiA := zigPsiA d (p.n * p.W)) (fun k _ => by linarith [(hpsi k).1])
    (fun k _ => by linarith [(hpsi k).2]) x hs0 hsτ
  have hflow := QV.qvFlow_of d hb hPS hPW hPD hz' hP6 hT1
  have c := Forcing.fctx_of d p.n_ge_four p.W_pos hz hs0 hs1 P hPW hPD hPS' rfl
    (hflow.one_le s ⟨hs0, hs.2⟩)
  have hAPs := MI.fAPriori_of hN hW hzi hs1 hpsi hQ
  have hIso := MI.isoBAt_of hQ
  have hΛ := MI.aprLamM_one_le d hN
  have he0 := MI.eMI_nonneg d hN (n + 4)
  have hint := circ_integrand_long d P hPW hPD hPS' hz' ⟨hs0, hs1⟩ c
    (VS.vsBandFin_isHermitian _ x) hAPs hpsi hIso (fun _ => by linarith) he0 hn
    (fun _ => Apriori.mbounds_extra_uncond hc hs0 hs1 (by omega)) σ hσ y
  have hLT0 : 0 < P.lEta T := (hflow.inputs T ⟨hs0.trans hs.2, le_rfl⟩).lEta_pos
  have hpsi0 : ∀ j, 0 ≤ zigPsiI d (p.n * p.W) j ∧ 0 ≤ zigPsiA d (p.n * p.W) j := fun j =>
    ⟨le_trans zero_le_one (hpsi j).1, le_trans zero_le_one (hpsi j).2⟩
  have hmono := MI.phiAvF_anti hpsi0 hLT0 (hflow.anti s ⟨hs0, hs.2⟩)
    (MI.yScale_anti P hN hW hzi hs.2 hT1) (k := n + 4) hn
  have hC := MI.avConst_nonneg d (LamM := Apriori.aprLamM d (p.n * p.W)) (by linarith) he0 (n + 4)
  refine hint.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
    (Real.rpow_nonneg (P.lEta_pos hN hW hzi hs1).le _)) (P.sAv_pos hN hW hzi hs1 y).le)
  unfold llForcingP7
  have := mul_le_mul_of_nonneg_left hmono hC
  linarith

/-- The (LL) event grows with the level. -/
theorem circLLEvent_mono (P : PsiData (p.n * p.W)) (hW : 0 < P.W) (hz : 0 < P.z.im) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (τ : RingSample p → WithTop ℝ≥0) {B B' : ℝ} (hBB : B ≤ B')
    (T : ℝ≥0) (hT1 : (T : ℝ) ≤ 1) : circLLEvent P σ τ B T ⊆ circLLEvent P σ τ B' T := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  intro x hx s hs hsτ y
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have h0 : 0 ≤ P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s :=
    mul_nonneg (Real.rpow_nonneg (P.lEta_pos hN hW hz hs1).le _) (P.sAv_pos hN hW hz hs1 y).le
  refine (hx s hs hsτ y).trans ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right hBB h0

/-- **The (LL) event for all `s ≤ T` at once, P7 thresholds, any level `B₂ ≥ llLevelP7`.**
For every `d`, `D > 0`, `ε > 0` there is `N₀` (depending only on `d`, `D`, `ε`) such that for
every ring `p` with `p.b = d.b`, `N = p.n p.W ≥ N₀` and `N^{1+ζ₀} ≤ W²`, every model, every `z ∈ 𝒟`,
every deterministic `T ≤ 1`, every `k = n + 4 ≤ 8`, every saturated pattern `σ` and every
`B₂ ≥ llLevelP7 d p z n ε T`:
`P(T ≤ τ ∧ x ∉ circLLEvent P σ τ B₂ T) ≤ N^{-D}` (`P = zigPsiData p d.D z`, `τ = zigTau p d z`,
`μ = model.law`).
-/
theorem measure_not_circLLEvent_le_of_le : ∀ (d : VSData) (D : ℝ), 0 < D → ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ), BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z →
      ∀ T : ℝ≥0, T ≤ 1 → ∀ {n : ℕ}, n + 4 ≤ 8 → ∀ σ : Fin (n + 2 + 2) → Bool,
      ¬ HasDesatFactor σ → ∀ B₂ : ℝ, llLevelP7 d p z n ε T ≤ B₂ →
        driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
            {x | (T : WithTop ℝ≥0) ≤ zigTau p d z x ∧
              x ∉ circLLEvent (zigPsiData p d.D z) σ (zigTau p d z) B₂ T} ≤
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D)) := by
  intro d D _hD ε hε
  obtain ⟨N₀, hN₀⟩ := measure_circLLEvent_compl_le_gen d hε D
  refine ⟨⌈N₀⌉₊, fun p hpb hN hP6 model z hz T hT n hn σ hσ B₂ hB₂ => ?_⟩
  set P := zigPsiData p d.D z
  set μ : Measure p.SiteMatrix := (model.law : Measure p.SiteMatrix)
  have hb : d.b = p.b := hpb.symm
  have hPS : P.S = shortRingProfile p.b p.n p.W := rfl
  have hPW : P.W = p.W := rfl
  have hPD : P.D = d.D := rfl
  have hz' : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z := hz
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := p.W_pos
  have hzi := hz'.im_pos hNpos
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hT1 : (T : ℝ) ≤ 1 := by exact_mod_cast hT
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz'
  have hpsi := zig_psi_ge d p
  have hIk : ∀ k ∈ kRange, 0 < zigPsiI d (p.n * p.W) k := fun k _ => by linarith [(hpsi k).1]
  have hAk : ∀ k ∈ kRange, 0 < zigPsiA d (p.n * p.W) k := fun k _ => by linarith [(hpsi k).2]
  have hτ := tau_isStoppingTime μ hNpos hW hzi hS (zigPsiI d (p.n * p.W))
    (zigPsiA d (p.n * p.W))
  have hAP := Apriori.qvAPriori_ae μ d hc hIk hAk T
  have hFB : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ zigTau p d z x → ∀ y, vsHeight P.z s *
        ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            llForcingP7 d p z n T * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s :=
    Filter.Eventually.of_forall fun x s hs hsτ y =>
      forcing_le_T d hb hP6 hz hT1 hn σ hσ x hs hsτ y
  have hAPF : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s : ℝ≥0, s ≤ T →
      (s : WithTop ℝ≥0) ≤ zigTau p d z x →
        Forcing.APriori P s (pathH p x s) (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) :=
    Filter.Eventually.of_forall fun x s _ hsτ =>
      Apriori.forcingAPriori_of_le_tau hNpos hW hzi hS hIk hAk x (NNReal.coe_nonneg s)
        (by rw [Real.toNNReal_coe]; exact hsτ)
  have hNR : N₀ ≤ ((p.n * p.W : ℕ) : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hmain := hN₀ p μ P hb hPS hPW hPD hz' hP6 (MI.aprLamM_one_le d hNpos)
    (fun j => (hpsi j).1) (fun j => le_trans zero_le_one (hpsi j).2) hτ T hT1 hAP hn σ hσ
    (llForcingP7_nonneg d p hzi n hT1) hFB hAPF hNR
  refine le_trans (measure_mono fun x hx => ?_) hmain
  exact fun hE => hx.2 (circLLEvent_mono P hW hzi σ (zigTau p d z) hB₂ T hT1 hE)

/-- **The (LL) event for all `s ≤ T` at once, P7 thresholds**: for every `d`, `D > 0`,
`ε > 0` there is `N₀` (depending only on `d`, `D`, `ε`) such that, in the setting of
`MI.MasterIneqSat`, `P(T ≤ τ ∧ x ∉ circLLEvent P σ τ B₂ T) ≤ N^{-D}` with the explicit level
`B₂ = llLevelP7 d p z n ε T = 2 (llCD B_T + N^{ε/2} llZ(L_T) + R₀) + 1`. -/
theorem measure_not_circLLEvent_le : ∀ (d : VSData) (D : ℝ), 0 < D → ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ), BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z →
      ∀ T : ℝ≥0, T ≤ 1 → ∀ {n : ℕ}, n + 4 ≤ 8 → ∀ σ : Fin (n + 2 + 2) → Bool,
      ¬ HasDesatFactor σ →
        driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
            {x | (T : WithTop ℝ≥0) ≤ zigTau p d z x ∧
              x ∉ circLLEvent (zigPsiData p d.D z) σ (zigTau p d z) (llLevelP7 d p z n ε T) T} ≤
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D)) := by
  intro d D hD ε hε
  obtain ⟨N₀, hN₀⟩ := measure_not_circLLEvent_le_of_le d D hD ε hε
  exact ⟨N₀, fun p hpb hN hP6 model z hz T hT n hn σ hσ =>
    hN₀ p hpb hN hP6 model z hz T hT hn σ hσ _ le_rfl⟩

end BlockBand.Native.ErdosRiabov.LLGrid
