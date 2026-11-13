module

public import BlockBand.Native.ErdosRiabov.SatLin.Main

/-!
# `LLGridHyp` for `k = 4, 6` from the (LL) event bound; the case `k = 8`

The (LL) event hypothesis at the `φ`-level follows from the (LL) event bound at the thresholds
for `k = 4, 6`; the case `k = 8` is the named hypothesis `LLGridHyp8`.

* `llLevelP7_le` (deterministic, `k = n+4 ≤ 7`): `LLGrid.llLevelP7 d p z n ε T ≤
  aLL d n ℓ^{757} N^{ε/2} φ^{av}_{k,T}`. The gainless terms `ψ^av_{k-1}`, `ψ^av_{k-2}` of
  `llLevelP7` are dominated by the term `ψ_{k+1}` of `avTerms k` (`4 ≤ k ≤ 7`).
* **`llGridHyp_of_P7`**: `LLGridHyp8 → LLGridHyp` (`k = 4, 6` from
  `LLGrid.measure_not_circLLEvent_le_of_le` at `ε = ε'/4`; `k = 5, 7` vacuous; `k = 8` from
  `LLGridHyp8`).
* **`masterIneqSat_of_LL8`**: `LLGridHyp8 → MI.MasterIneqSat`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.SatLin

open MeasureTheory Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Forcing
open BlockBand.Native.ErdosRiabov.QV
open BlockBand.Native.ErdosRiabov.Circ
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.MI (logL aInt aLam aZ cAvZ)
open BlockBand.Native.ErdosRiabov.Assembly (zigPsiData)
open BlockBand.Native.ErdosRiabov.ZigProof (zigTau zigPsiI zigPsiA)
open BlockBand.Native.ErdosRiabov.Apriori (aprPsiI aprPsiA aprLamM)
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

/-!
### The (LL) level at the thresholds against `φ` (`4 ≤ k ≤ 7`)
-/

section Level

variable (d : VSData) {p : BlockBand.Parameters} {z : ℂ}
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z) {T : ℝ} (hT1 : T ≤ 1) {n : ℕ}
  (hn : n + 4 ≤ 7)
include hz hT1 hn

/-- `ψ^av_j ≤ φ^{av}_{k,T}` for `j + 1 ≤ k = n+4 ≤ 7`. -/
theorem zigPsiA_le_phiT {j : ℕ} (hj : j + 1 ≤ n + 4) :
    zigPsiA d (p.n * p.W) j ≤ phiT d p z T (n + 4) := by
  obtain ⟨hN, hX, hY, -⟩ := zig_scalars d hz hT1
  show aprPsiA d (p.n * p.W) j ≤ phiT d p z T (n + 4)
  rw [(MI.aprPsi_eq d (p.n * p.W)).2]
  exact (thrAv_le_thrIso (Nat.one_le_cast.mpr (MI.mi_N_pos p)) d.xi_pos.le hj).trans
    (thrIso_succ_le_phiAv hN hX hY (by omega) hn)

/-- The forcing constant: `B_T ≤ (m c_av A_Z² + 4 C_K √C₁'') ℓ^{757} φ`. -/
theorem llForcingP7_le :
    LLGrid.llForcingP7 d p z n T ≤
      (((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ) * cAvZ d * aZ d (n + 4) ^ 2 +
        4 * vsCK d * Real.sqrt d.C1pp) * logL (p.n * p.W) ^ 757 * phiT d p z T (n + 4) := by
  have hn8 : n + 4 ≤ 8 := by omega
  obtain ⟨-, hX, hY, hℓ⟩ := zig_scalars d hz hT1
  obtain ⟨hΦ, -, hφ1⟩ := phiT_facts d hz hT1 (k := n + 4) (by omega) hn8
  set L7 := logL (p.n * p.W) ^ 757
  set φ := phiT d p z T (n + 4)
  set m : ℝ := ((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hl504 : logL (p.n * p.W) ^ 504 ≤ L7 := pow_le_pow_right₀ hℓ (by norm_num)
  have hl1 : 1 ≤ L7 := one_le_pow₀ hℓ
  have hφ0 : 0 ≤ φ := by linarith
  obtain ⟨hΛ0, he0, hZ⟩ := MI.z_le d (p := p) hn8
  have hZ0 : 0 ≤ 1 + aprLamM d (p.n * p.W) + MI.eMI d (p.n * p.W) (n + 4) := by linarith
  have hcz := MI.cAvZ_nonneg d
  have hZ2 : (1 + aprLamM d (p.n * p.W) + MI.eMI d (p.n * p.W) (n + 4)) ^ 2 ≤
      aZ d (n + 4) ^ 2 * L7 := by
    have h := pow_le_pow_left₀ hZ0 hZ 2
    rw [mul_pow, ← pow_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hl504 (sq_nonneg _))
  have hcav : cAv d (fun _ => aprLamM d (p.n * p.W)) (MI.eMI d (p.n * p.W) (n + 4)) ≤
      cAvZ d * (aZ d (n + 4) ^ 2 * L7) :=
    (MI.cAv_le d hΛ0 he0).trans (mul_le_mul_of_nonneg_left hZ2 hcz)
  have hC : avConst d (fun _ => aprLamM d (p.n * p.W)) (MI.eMI d (p.n * p.W) (n + 4)) (n + 4) ≤
      m * cAvZ d * aZ d (n + 4) ^ 2 * L7 := by
    unfold avConst
    have := mul_le_mul_of_nonneg_left hcav hm0
    linarith
  have hC0 := MI.avConst_nonneg d hΛ0 he0 (n + 4) (LamM := aprLamM d (p.n * p.W))
  have hpsi0 : ∀ j, 0 ≤ aprPsiI d (p.n * p.W) j ∧ 0 ≤ aprPsiA d (p.n * p.W) j := fun j =>
    ⟨by linarith [(MI.mi_psi_ge d p j).1], by linarith [(MI.mi_psi_ge d p j).2]⟩
  have hΦ0 := phiAvF_nonneg hpsi0 hX.le hY.le (n + 4)
  have hA0 : 0 ≤ m * cAvZ d * aZ d (n + 4) ^ 2 * L7 :=
    mul_nonneg (mul_nonneg (mul_nonneg hm0 hcz) (sq_nonneg _)) (by linarith)
  have h1 := mul_le_mul hC hΦ hΦ0 hA0
  have hψ := zigPsiA_le_phiT d hz hT1 hn (j := n + 3) (by omega)
  have hk0 : 0 ≤ 4 * vsCK d * Real.sqrt d.C1pp :=
    mul_nonneg (mul_nonneg (by norm_num) (vsCK_pos d).le) (Real.sqrt_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hψ hk0
  have h3 := mul_le_mul_of_nonneg_left hl1 (mul_nonneg hk0 hφ0)
  have e : LLGrid.llForcingP7 d p z n T =
      avConst d (fun _ => aprLamM d (p.n * p.W)) (MI.eMI d (p.n * p.W) (n + 4)) (n + 4) *
        phiAvF (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) ((zigPsiData p d.D z).lEta T)
          (yScale (zigPsiData p d.D z) T) (n + 4) +
      4 * vsCK d * Real.sqrt d.C1pp * zigPsiA d (p.n * p.W) (n + 3) := rfl
  rw [e]
  linarith

/-- The noise coefficient: `llZ ≤ 8 (1 + 𝔠 A_Λ³) C₁ c ℓ^{757} φ`. -/
theorem llZ_le :
    LLGrid.llZ d (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) (aprLamM d (p.n * p.W))
        ((zigPsiData p d.D z).lEta T) n ≤
      8 * (1 + qvC d * aLam d ^ 3) * LLGrid.llC1 d n *
        Real.sqrt (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0)) *
          logL (p.n * p.W) ^ 757 * phiT d p z T (n + 4) := by
  have hn8 : n + 4 ≤ 8 := by omega
  obtain ⟨-, hX, -, hℓ⟩ := zig_scalars d hz hT1
  obtain ⟨-, hq, hφ1⟩ := phiT_facts d hz hT1 (k := n + 4) (by omega) hn8
  set L7 := logL (p.n * p.W) ^ 757
  set φ := phiT d p z T (n + 4)
  set Λ := aprLamM d (p.n * p.W)
  set c := Real.sqrt (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0))
  have hl756 : logL (p.n * p.W) ^ 756 ≤ L7 := pow_le_pow_right₀ hℓ (by norm_num)
  obtain ⟨hΛ0, -, -⟩ := MI.z_le d (p := p) hn8
  have hΛ := MI.aprLamM_le_logL d (MI.mi_N_two p)
  have hq0 := (qvC_pos d).le
  have haL := MI.aLam_nonneg d
  have h3 : Λ ^ 3 ≤ aLam d ^ 3 * L7 := by
    have h := pow_le_pow_left₀ hΛ0 hΛ 3
    rw [mul_pow, ← pow_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hl756 (pow_nonneg haL 3))
  have hsqΛ : Real.sqrt (qvC d * Λ ^ 3) ≤ (1 + qvC d * aLam d ^ 3) * L7 := by
    have hx0 : 0 ≤ qvC d * Λ ^ 3 := mul_nonneg hq0 (pow_nonneg hΛ0 3)
    refine (MI.sqrt_le_one_add hx0).trans ?_
    have h4 := mul_le_mul_of_nonneg_left h3 hq0
    have hL1 : 1 ≤ L7 := one_le_pow₀ hℓ
    nlinarith
  have hn8' : (n : ℝ) + 4 ≤ 8 := by
    have : ((n + 4 : ℕ) : ℝ) ≤ 8 := by exact_mod_cast hn8
    push_cast at this; linarith
  have hφq : qvPhiAv (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) (n + 4)
      ((zigPsiData p d.D z).lEta T) ≤ φ := hq
  have hpsi0 : ∀ j, 0 ≤ aprPsiA d (p.n * p.W) j := fun j => by
    linarith [(MI.mi_psi_ge d p j).2]
  have hφq0 : 0 ≤ qvPhiAv (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) (n + 4)
      ((zigPsiData p d.D z).lEta T) :=
    (qvPhiAv_pos (fun j => (MI.mi_psi_ge d p j).1) hpsi0 _ hX).le
  have hsq0 := Real.sqrt_nonneg (qvC d * Λ ^ 3)
  have hB0 : 0 ≤ (1 + qvC d * aLam d ^ 3) * L7 :=
    mul_nonneg (by positivity) (by linarith [one_le_pow₀ hℓ (n := 757)])
  have h1 : ((n : ℝ) + 4) * Real.sqrt (qvC d * Λ ^ 3) ≤ 8 * ((1 + qvC d * aLam d ^ 3) * L7) :=
    mul_le_mul hn8' hsqΛ hsq0 (by norm_num)
  have h2 := mul_le_mul h1 hφq hφq0 (mul_nonneg (by norm_num) hB0)
  have hc0 : 0 ≤ LLGrid.llC1 d n * c := mul_nonneg (LLGrid.llC1_pos d n).le (Real.sqrt_nonneg _)
  have h5 := mul_le_mul_of_nonneg_right h2 hc0
  unfold LLGrid.llZ
  calc _ = ((n : ℝ) + 4) * Real.sqrt (qvC d * Λ ^ 3) * qvPhiAv (zigPsiI d (p.n * p.W))
        (zigPsiA d (p.n * p.W)) (n + 4) ((zigPsiData p d.D z).lEta T) *
        (LLGrid.llC1 d n * c) := by ring
    _ ≤ 8 * ((1 + qvC d * aLam d ^ 3) * L7) * φ * (LLGrid.llC1 d n * c) := h5
    _ = _ := by ring

/-- The remainder constant: `R₀ ≤ (2 C_K² C_w √C₁'' + C_K² C₁'') ℓ^{757} φ`. -/
theorem llR0_le :
    LLGrid.llR0 d (zigPsiA d (p.n * p.W)) n ≤
      (2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp) + vsCK d ^ 2 * d.C1pp) *
        logL (p.n * p.W) ^ 757 * phiT d p z T (n + 4) := by
  have hn8 : n + 4 ≤ 8 := by omega
  obtain ⟨-, -, -, hℓ⟩ := zig_scalars d hz hT1
  obtain ⟨-, -, hφ1⟩ := phiT_facts d hz hT1 (k := n + 4) (by omega) hn8
  have hl1 : 1 ≤ logL (p.n * p.W) ^ 757 := one_le_pow₀ hℓ
  have hψ3 := zigPsiA_le_phiT d hz hT1 hn (j := n + 3) (by omega)
  have hψ2 := zigPsiA_le_phiT d hz hT1 hn (j := n + 2) (by omega)
  have hCw : 0 ≤ d.Cwc := le_trans zero_le_one d.one_le_Cwc
  have hC1 : 0 ≤ d.C1pp := le_trans zero_le_one d.one_le_C1pp
  have hCK := (vsCK_pos d).le
  have ha : 0 ≤ 2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp) := by positivity
  have hb : 0 ≤ vsCK d ^ 2 * d.C1pp := by positivity
  have h1 := mul_le_mul_of_nonneg_left hψ3 ha
  have h2 := mul_le_mul_of_nonneg_left hψ2 hb
  have h3 := mul_le_mul_of_nonneg_left hl1
    (mul_nonneg (add_nonneg ha hb) (by linarith : (0 : ℝ) ≤ phiT d p z T (n + 4)))
  unfold LLGrid.llR0
  linarith

end Level

/-- The constant of `llLevelP7_le` (`k = n+4`). -/
def aLL (d : VSData) (n : ℕ) : ℝ :=
  2 * LLGrid.llCD d n * (((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ) * cAvZ d *
      aZ d (n + 4) ^ 2 + 4 * vsCK d * Real.sqrt d.C1pp) +
    16 * (1 + qvC d * aLam d ^ 3) * LLGrid.llC1 d n *
      Real.sqrt (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0)) +
    2 * (2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp) + vsCK d ^ 2 * d.C1pp) + 1

theorem aLL_nonneg (d : VSData) {n : ℕ} (hn : n + 4 ≤ 8) : 0 ≤ aLL d n := by
  have := LLGrid.llCD_nonneg d hn; have := (LLGrid.llC1_pos d n).le
  have := MI.cAvZ_nonneg d; have := MI.aLam_nonneg d; have := (qvC_pos d).le
  have := (vsCK_pos d).le; have := le_trans zero_le_one d.one_le_Cwc
  have := le_trans zero_le_one d.one_le_C1pp
  unfold aLL
  positivity

/-- **The (LL) level at the thresholds against `φ^{av}_{k,T}`, `4 ≤ k ≤ 7`**:
`llLevelP7 d p z n ε T ≤ aLL d n ℓ^{757} N^{ε/2} φ_k` (`ε ≥ 0`). -/
theorem llLevelP7_le (d : VSData) {p : BlockBand.Parameters} {z : ℂ}
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z) {T : ℝ} (hT1 : T ≤ 1) {n : ℕ}
    (hn : n + 4 ≤ 7) {ε : ℝ} (hε : 0 ≤ ε) :
    LLGrid.llLevelP7 d p z n ε T ≤
      aLL d n * logL (p.n * p.W) ^ 757 * ((p.n * p.W : ℕ) : ℝ) ^ (ε / 2) *
        phiT d p z T (n + 4) := by
  have hn8 : n + 4 ≤ 8 := by omega
  obtain ⟨-, -, -, hℓ⟩ := zig_scalars d hz hT1
  obtain ⟨-, -, hφ1⟩ := phiT_facts d hz hT1 (k := n + 4) (by omega) hn8
  set L7 := logL (p.n * p.W) ^ 757
  set φ := phiT d p z T (n + 4)
  set Nε : ℝ := ((p.n * p.W : ℕ) : ℝ) ^ (ε / 2)
  have hNε : 1 ≤ Nε := Real.one_le_rpow (Nat.one_le_cast.mpr (MI.mi_N_pos p)) (by positivity)
  have hl1 : 1 ≤ L7 := one_le_pow₀ hℓ
  have hφ0 : 0 ≤ φ := by linarith
  set A1 := ((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ) * cAvZ d * aZ d (n + 4) ^ 2 +
    4 * vsCK d * Real.sqrt d.C1pp
  set A2 := 8 * (1 + qvC d * aLam d ^ 3) * LLGrid.llC1 d n *
    Real.sqrt (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0))
  set A3 := 2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp) + vsCK d ^ 2 * d.C1pp
  have hB := llForcingP7_le d hz hT1 hn
  have hZ := llZ_le d hz hT1 hn
  have hR := llR0_le d hz hT1 hn
  have hCD := LLGrid.llCD_nonneg d hn8
  have hA1 : 0 ≤ A1 := by
    have := MI.cAvZ_nonneg d; have := (vsCK_pos d).le; positivity
  have hA2 : 0 ≤ A2 := by
    have := MI.aLam_nonneg d; have := (qvC_pos d).le; have := (LLGrid.llC1_pos d n).le
    positivity
  have hA3 : 0 ≤ A3 := by
    have := (vsCK_pos d).le; have := le_trans zero_le_one d.one_le_Cwc
    have := le_trans zero_le_one d.one_le_C1pp; positivity
  have hP1 : 0 ≤ A1 * L7 * φ := mul_nonneg (mul_nonneg hA1 (by linarith)) hφ0
  have hP3 : 0 ≤ A3 * L7 * φ := mul_nonneg (mul_nonneg hA3 (by linarith)) hφ0
  have t1 := mul_le_mul_of_nonneg_left hB hCD
  have t2 := mul_le_mul_of_nonneg_left hZ (show 0 ≤ Nε by linarith)
  have u1 := mul_le_mul_of_nonneg_left hNε (mul_nonneg hCD hP1)
  have u3 := mul_le_mul_of_nonneg_left hNε hP3
  have u4 : 1 ≤ L7 * Nε * φ := by
    have h1 := mul_le_mul hl1 hNε zero_le_one (by linarith)
    have h2 := mul_le_mul h1 hφ1 zero_le_one (by positivity)
    linarith
  have eL : LLGrid.llLevelP7 d p z n ε T = 2 * (LLGrid.llCD d n * LLGrid.llForcingP7 d p z n T +
      Nε * LLGrid.llZ d (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) (aprLamM d (p.n * p.W))
        ((zigPsiData p d.D z).lEta T) n + LLGrid.llR0 d (zigPsiA d (p.n * p.W)) n) + 1 := rfl
  have ea : aLL d n = 2 * LLGrid.llCD d n * A1 + 2 * A2 + 2 * A3 + 1 := by
    simp only [aLL, A1, A2, A3]; ring
  rw [eL, ea]
  linarith

/-!
### `LLGridHyp` from the (LL) event bound and the `k = 8` case
-/

/-- **The (LL) event at the `φ`-level for `k = 8` (named hypothesis; `llGridHyp8_holds`).**
`LLGridHyp`
restricted to `k = 8`: for every `d`, `D > 0` there is `N₀` such that, in the setting of
`LLGridHyp`, for every saturated `σ` of length `8`,
`P(T ≤ τ ∧ x ∉ circLLEvent P σ τ (N^{ε'/4} φ^{av}_{8,T}) T) ≤ N^{-D}`. -/
def LLGridHyp8 : Prop :=
  ∀ (d : VSData) (D : ℝ), 0 < D → ∃ N₀ : ℕ,
    ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W → d.zeta0 < 1 →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ),
        BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z →
        ∀ T : ℝ≥0, T ≤ 1 → ∀ σ : Fin (4 + 2 + 2) → Bool, ¬ HasDesatFactor σ →
          driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
              {x | (T : WithTop ℝ≥0) ≤ zigTau p d z x ∧
                x ∉ circLLEvent (zigPsiData p d.D z) σ (zigTau p d z)
                  (((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4) * phiT d p z T (4 + 4)) T} ≤
            ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D))

/-- **`LLGridHyp` from the (LL) event bound at the P7 thresholds (`k = 4, 6`) and `LLGridHyp8`
(`k = 8`).**
`k = 5, 7` are vacuous (`MBound.hasDesatFactor_of_odd`).
For `k = 4, 6`:
`LLGrid.measure_not_circLLEvent_le_of_le` at `ε = ε'/4` with `B₂ = N^{ε'/4} φ_k`, using
`llLevelP7_le` and `(aLL 0 + aLL 2) ℓ^{757} ≤ N^{ε'/8}` (`N ≥ absorbN0 … (ε'/8)`).
The hypothesis `LLGridHyp8` is proved as `llGridHyp8_holds`.
-/
theorem llGridHyp_of_P7 (h8 : LLGridHyp8) : LLGridHyp := by
  intro d D hD
  have hε := d.epsP_pos
  obtain ⟨N₈, hN₈⟩ := h8 d D hD
  obtain ⟨N₄, hN₄⟩ := LLGrid.measure_not_circLLEvent_le_of_le d D hD (d.epsP / 4) (by positivity)
  set A := aLL d 0 + aLL d 2
  have hA0 : 0 ≤ A := add_nonneg (aLL_nonneg d (by norm_num)) (aLL_nonneg d (by norm_num))
  refine ⟨max (max N₈ N₄) ⌈MI.absorbN0 A 757 (d.epsP / 8)⌉₊,
    fun p hpb hN hζ hband model z hz T hT n hn σ hσ => ?_⟩
  have hN8 : N₈ ≤ p.n * p.W := le_of_max_le_left (le_of_max_le_left hN)
  have hN4 : N₄ ≤ p.n * p.W := le_of_max_le_right (le_of_max_le_left hN)
  have hNA : MI.absorbN0 A 757 (d.epsP / 8) ≤ ((p.n * p.W : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hN)
  have hT1 : (T : ℝ) ≤ 1 := by exact_mod_cast hT
  have hN0' : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast MI.mi_N_pos p
  have hl := one_le_pow₀ (MI.mi_logL_one (p := p)) (n := 757)
  have hAbs : A * logL (p.n * p.W) ^ 757 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) := by
    have := MI.absorb_of_logL (by positivity) hA0 le_rfl (by positivity) hNA
      (F := A * logL (p.n * p.W) ^ 757) (M := 0)
    unfold MI.Absorb at this
    rw [mul_zero, add_zero] at this
    exact this
  -- `k = 4, 6` from the (LL) event bound at the thresholds
  have hP7 : ∀ {m : ℕ}, m + 4 ≤ 7 → aLL d m ≤ A → ∀ σ' : Fin (m + 2 + 2) → Bool,
      ¬ HasDesatFactor σ' →
      driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
          {x | (T : WithTop ℝ≥0) ≤ zigTau p d z x ∧
            x ∉ circLLEvent (zigPsiData p d.D z) σ' (zigTau p d z)
              (((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4) * phiT d p z T (m + 4)) T} ≤
        ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D)) := by
    intro m hm hmA σ' hσ'
    refine hN₄ p hpb hN4 hband model z hz T hT (by omega) σ' hσ' _ ?_
    have hlev := llLevelP7_le d hz hT1 hm (ε := d.epsP / 4) (by positivity)
    obtain ⟨-, -, hφ1⟩ := phiT_facts d hz hT1 (k := m + 4) (by omega) (by omega)
    have e1 : ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4 / 2) = ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) := by
      congr 1; ring
    have e2 : ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) * ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) =
        ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4) := by
      rw [← Real.rpow_add hN0']; congr 1; ring
    rw [e1] at hlev
    refine hlev.trans ?_
    have hφ0 : 0 ≤ phiT d p z T (m + 4) := by linarith
    have hs0 : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) := Real.rpow_nonneg hN0'.le _
    have h1 : aLL d m * logL (p.n * p.W) ^ 757 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) :=
      (mul_le_mul_of_nonneg_right hmA (by positivity)).trans hAbs
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hs0 hφ0)
    rw [← e2]
    nlinarith
  rcases n with _ | _ | _ | _ | _ | n
  · exact hP7 (m := 0) (by norm_num) (le_add_of_nonneg_right (aLL_nonneg d (by norm_num))) σ hσ
  · exact absurd (MBound.hasDesatFactor_of_odd (by decide) σ) hσ
  · exact hP7 (m := 2) (by norm_num) (le_add_of_nonneg_left (aLL_nonneg d (by norm_num))) σ hσ
  · exact absurd (MBound.hasDesatFactor_of_odd (by decide) σ) hσ
  · exact hN₈ p hpb hN8 hζ hband model z hz T hT σ hσ
  · omega

/-- **The saturated part of the master inequality from the `k = 8` (LL) case.**
`LLGridHyp8 → MI.MasterIneqSat` (`llGridHyp_of_P7`, `masterIneqSat_of_LL`); the hypothesis
`LLGridHyp8` is proved as `llGridHyp8_holds`.
-/
theorem masterIneqSat_of_LL8 (h8 : LLGridHyp8) : MI.MasterIneqSat :=
  masterIneqSat_of_LL (llGridHyp_of_P7 h8)

/-- The statement `Inputs.ShortRingLocalLaw` from `LLGridHyp8` (proved as `llGridHyp8_holds`).
-/
theorem shortRingLocalLaw_of_LL8 (h8 : LLGridHyp8) :
    BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw :=
  shortRingLocalLaw_of_LL (llGridHyp_of_P7 h8)

end BlockBand.Native.ErdosRiabov.SatLin
