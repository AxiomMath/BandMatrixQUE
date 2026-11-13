module

public import BlockBand.Native.ErdosRiabov.LLGrid.GainP7

/-!
# The gained (LL) level is `≤ N^{ε/2} · polylog · φ^{av}_{k,T}`

Setting: `P = zigPsiData p d.D z`, `z ∈ 𝒟`, `T ≤ 1`, `k = n + 4 ≤ 8` (all of `k = 4, …, 8`),
`X = L_T`, `Y = Y_T = ZigProof.yZig P T` (`= Forcing.yScale P T`), `N = p.n p.W`,
`ℓ = MI.logL N = 1 + log N`, `φ^{av}_{k,T} = Expo.phiAv N ξ X Y k` (the form of
`MI.MasterIneqSat`).

The gained terms `ψ^av_{k-1} X^{-(β_k-β_{k-1})}` and `ψ^av_{k-2} X^{-(β_k-β_{k-2})}` are the
`j = k-1` and `j = k-2` summands of the first forcing sum of `Φ^{av,f}_k`
(`Forcing.av_fm_le_phi`; `k - 2 ≥ 2`), and `Φ^{av,f}_k ≤ φ^{av}_k` (`Forcing.phiAvF_le_phiAv`).
The QV term is `φ^{av,qv}_k ≤ φ^{av}_k` (`MI.qvPhiAv_le_phiAv`), `1 ≤ φ^{av}_k` (the term
`ψ_{k,0} = 1`), and the polylogarithms are `Λ_M ≤ A_Λ ℓ^{252}` (`MI.aprLamM_le_logL`),
`e_k ≤ A_E(k) ℓ^{252}` (`MI.eMI_le_logL`), `C_av ≤ (3k²+k+1) c_av (1 + Λ_M + e_k)²`
(`MI.cAv_le`).

* `llCF d n = (3k²+k+1) c_av (1 + A_Λ + A_E(k))² + 4 C_K √C₁''`, `llCR d = 2 C_K² C_w √C₁'' +`
  `C_K² C₁''`, `llCZ d n = k √𝔠 A_Λ² C_reg² C_P^k √(2/((2-2β_k) c_m))` and
  **`llGainA d n = 2 llCD d n · llCF d n + 2 llCZ d n + 2 llCR d + 1`** (constants of `d`, `n`);
* `one_le_phiAv`: `1 ≤ φ^{av}_k`;
* **`llLevelGainP7_le`**: for `N = p.n p.W`, `z ∈ 𝒟`, `T ≤ 1`, `n + 4 ≤ 8`, `ε ≥ 0`:
  `llLevelGainP7 d p z n ε T ≤ N^{ε/2} · (llGainA d n · ℓ^{504}) · φ^{av}_{k,T}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.LLGrid

open Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo
open BlockBand.Native.ErdosRiabov.Flow.Expo.Mono
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Assembly (zigPsiData)
open BlockBand.Native.ErdosRiabov.ZigProof (zigPsiI zigPsiA)

/-! ### Constants -/

/-- The forcing coefficient `(3k²+k+1) c_av (1 + A_Λ + A_E(k))² + 4 C_K √C₁''`, `k = n + 4`. -/
def llCF (d : VSData) (n : ℕ) : ℝ :=
  ((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ) * MI.cAvZ d *
      (1 + MI.aLam d + MI.aExtra d (n + 4)) ^ 2 +
    4 * vsCK d * Real.sqrt d.C1pp

/-- The remainder coefficient `2 C_K² C_w √C₁'' + C_K² C₁''`. -/
def llCR (d : VSData) : ℝ :=
  2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp) + vsCK d ^ 2 * d.C1pp

/-- The noise coefficient `k √𝔠 A_Λ² C_reg² C_P^k √(2/((2-2β_k) c_m))`. -/
def llCZ (d : VSData) (n : ℕ) : ℝ :=
  ((n : ℝ) + 4) * Real.sqrt (QV.qvC d) * MI.aLam d ^ 2 * llC1 d n *
    Real.sqrt (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0))

/-- **The constant of the level bound** `2 llCD · llCF + 2 llCZ + 2 llCR + 1`. -/
def llGainA (d : VSData) (n : ℕ) : ℝ :=
  2 * llCD d n * llCF d n + 2 * llCZ d n + 2 * llCR d + 1

/-! ### `1 ≤ φ^{av}` -/

/-- `1 ≤ φ^{av}_k` (the term `ψ_{k,0} = 1` of `Expo.avTerms`). -/
theorem one_le_phiAv {N ξ X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hY : 0 < Y) (k : ℕ) :
    1 ≤ phiAv N ξ X Y k := by
  have h1 : Term.value N ξ X Y (Term.mono Mono.one) = 1 := by
    simp [Term.value, Mono.value, Mono.one, Mono.gval]
  unfold phiAv avTerms
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  have h2 := Forcing.sum_value_nonneg (ξ := ξ) hN hX hY ((List.range' 2 (k - 2)).flatMap
    (fun j => [Term.mono (pA j * (betaM k / betaM j)),
      Term.mono (pA j * (betaM k / betaM j) * pI (k + 2 - j) *
        (lossC (1 / 2) / alphaM (k + 2 - j)))]))
  have h3 := Forcing.Term.value_nonneg' (ξ := ξ) hN hX hY (Term.mono (pI 2 * pA k * lossC (1 / 2)))
  have h3' := Forcing.Term.value_nonneg' (ξ := ξ) hN hX hY (if k ≤ 3 then
      Term.sqrtOne (pI (2 * k + 2) * (lossC (1 / 2) / alphaM (2 * k + 2)))
    else if k ≤ 7 then Term.mono (pI (k + 1))
    else Term.monoSqrtOne (pI 5) (pA 8 * (lossC 1 / betaM 8)))
  have h4 := Forcing.sum_value_nonneg (ξ := ξ) hN hX hY (if k = 1 then
      [Term.mono (sqY * pA 1 * pI 2)]
    else if k ≤ 7 then [Term.mono (sqY * pA 1 * pI (k + 1)), Term.mono (pA 1 * betaM k)]
    else [Term.mono (sqY * pA 1 * pI 4 * pI 5)])
  have h5 := Forcing.sum_value_nonneg (ξ := ξ) hN hX hY (if k % 2 = 0 then
      [Term.mono (pA (k - 1) * (betaM k / betaM (k - 1)))] ++
        (if 4 ≤ k then [Term.mono (pA (k - 2) * (betaM k / betaM (k - 2)))] else [])
    else [])
  linarith

/-! ### The level bound -/

/-- `√(𝔠 Λ³) ≤ √𝔠 A_Λ² ℓ^{504}` (`N ≥ 2`, `Λ = Λ_M ≥ 1`). -/
theorem sqrt_qvC_lam_le (d : VSData) {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt (QV.qvC d * Apriori.aprLamM d N ^ 3) ≤
      Real.sqrt (QV.qvC d) * (MI.aLam d ^ 2 * MI.logL N ^ 504) := by
  have hΛ := MI.aprLamM_one_le d (show 0 < N by omega)
  have hΛL := MI.aprLamM_le_logL d hN
  have hq := (QV.qvC_pos d).le
  have h3 : Apriori.aprLamM d N ^ 3 ≤ (Apriori.aprLamM d N ^ 2) ^ 2 := by
    have : (Apriori.aprLamM d N ^ 2) ^ 2 = Apriori.aprLamM d N ^ 3 * Apriori.aprLamM d N := by
      ring
    rw [this]
    exact le_mul_of_one_le_right (by positivity) hΛ
  have hs : Real.sqrt (QV.qvC d * Apriori.aprLamM d N ^ 3) ≤
      Real.sqrt (QV.qvC d) * Apriori.aprLamM d N ^ 2 := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ Apriori.aprLamM d N ^ 2), ← Real.sqrt_mul hq]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h3 hq)
  have hsq : Apriori.aprLamM d N ^ 2 ≤ MI.aLam d ^ 2 * MI.logL N ^ 504 := by
    have : (MI.aLam d * MI.logL N ^ 252) ^ 2 = MI.aLam d ^ 2 * MI.logL N ^ 504 := by ring
    rw [← this]
    exact pow_le_pow_left₀ (by linarith) hΛL 2
  exact hs.trans (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _))

/-- `C_av = avConst d Λ_M e_k k ≤ (3k²+k+1) c_av (1 + A_Λ + A_E(k))² ℓ^{504}` (`N ≥ 2`, `k ≤ 8`). -/
theorem avConst_le_logL (d : VSData) {N : ℕ} (hN : 2 ≤ N) {n : ℕ} (hn : n + 4 ≤ 8) :
    Forcing.avConst d (fun _ => Apriori.aprLamM d N) (MI.eMI d N (n + 4)) (n + 4) ≤
      ((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ) * MI.cAvZ d *
        (1 + MI.aLam d + MI.aExtra d (n + 4)) ^ 2 * MI.logL N ^ 504 := by
  have hN0 : 0 < N := by omega
  have hΛ := MI.aprLamM_one_le d hN0
  have hΛL := MI.aprLamM_le_logL d hN
  have he0 := MI.eMI_nonneg d hN0 (n + 4)
  have heL := MI.eMI_le_logL d hN hn
  have hl := MI.one_le_logL (show 1 ≤ N by omega)
  have hl252 : 1 ≤ MI.logL N ^ 252 := one_le_pow₀ hl
  have hA := MI.aLam_nonneg d
  have hE := MI.aExtra_nonneg d (n + 4)
  have hc := MI.cAv_le d (Λ := Apriori.aprLamM d N) (by linarith) he0
  have hZ : 1 + Apriori.aprLamM d N + MI.eMI d N (n + 4) ≤
      (1 + MI.aLam d + MI.aExtra d (n + 4)) * MI.logL N ^ 252 := by
    nlinarith
  have hZ2 : (1 + Apriori.aprLamM d N + MI.eMI d N (n + 4)) ^ 2 ≤
      (1 + MI.aLam d + MI.aExtra d (n + 4)) ^ 2 * MI.logL N ^ 504 := by
    have : ((1 + MI.aLam d + MI.aExtra d (n + 4)) * MI.logL N ^ 252) ^ 2 =
        (1 + MI.aLam d + MI.aExtra d (n + 4)) ^ 2 * MI.logL N ^ 504 := by ring
    rw [← this]
    exact pow_le_pow_left₀ (by linarith) hZ 2
  have hcz := MI.cAvZ_nonneg d
  unfold Forcing.avConst
  have hk0 : (0 : ℝ) ≤ ((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ) *
        Forcing.cAv d (fun _ => Apriori.aprLamM d N) (MI.eMI d N (n + 4))
      ≤ ((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ) *
          (MI.cAvZ d * ((1 + MI.aLam d + MI.aExtra d (n + 4)) ^ 2 * MI.logL N ^ 504)) :=
        mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hZ2 hcz)) hk0
    _ = _ := by ring

section Level

variable (d : VSData) {p : BlockBand.Parameters} {z : ℂ}
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z) {T : ℝ} (hT1 : T ≤ 1) {n : ℕ}
  (hn : n + 4 ≤ 8)
include hz hT1 hn

/-- The scalars: `0 < N`, `0 < L_T`, `0 < Y_T`, `B_T^g ≤ llCF ℓ^{504} Φ^{av,f}_k`,
`llR0Gain(L_T) ≤ llCR Φ^{av,f}_k`, `Φ^{av,f}_k ≤ φ^{av}_k`. -/
theorem gain_parts_le :
    llForcingGainP7 d p z n T ≤ llCF d n * MI.logL (p.n * p.W) ^ 504 *
        Forcing.phiAvF (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W))
          ((zigPsiData p d.D z).lEta T) (Forcing.yScale (zigPsiData p d.D z) T) (n + 4) ∧
      llR0Gain d (zigPsiA d (p.n * p.W)) n ((zigPsiData p d.D z).lEta T) ≤ llCR d *
        Forcing.phiAvF (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W))
          ((zigPsiData p d.D z).lEta T) (Forcing.yScale (zigPsiData p d.D z) T) (n + 4) ∧
      Forcing.phiAvF (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W))
          ((zigPsiData p d.D z).lEta T) (Forcing.yScale (zigPsiData p d.D z) T) (n + 4) ≤
        phiAv ((p.n * p.W : ℕ) : ℝ) d.xi ((zigPsiData p d.D z).lEta T)
          (ZigProof.yZig (zigPsiData p d.D z) T) (n + 4) := by
  set P := zigPsiData p d.D z
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hN2 := MI.mi_N_two p
  have hNr : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast hN
  have hzi : 0 < P.z.im := hz.im_pos hN
  have hX : 0 < P.lEta T := P.lEta_pos hN p.W_pos hzi hT1
  have hY : 0 < Forcing.yScale P T :=
    div_pos (Real.sqrt_pos.2 (mul_pos hNr (vsHeight_pos hzi hT1))) hX
  have hpsi0 : ∀ j, 0 ≤ zigPsiI d (p.n * p.W) j ∧ 0 ≤ zigPsiA d (p.n * p.W) j := fun j =>
    ⟨le_trans zero_le_one (zig_psi_ge d p j).1, le_trans zero_le_one (zig_psi_ge d p j).2⟩
  have h3 := Forcing.av_fm_le_phi hpsi0 hX.le hY.le (k := n + 4) (r := n + 3) (by omega)
    (by omega)
  have h2 := Forcing.av_fm_le_phi hpsi0 hX.le hY.le (k := n + 4) (r := n + 2) (by omega)
    (by omega)
  have hΦ0 := Forcing.phiAvF_nonneg hpsi0 hX.le hY.le (n + 4)
  have hCK := (vsCK_pos d).le
  have hCw : 0 ≤ d.Cwc := le_trans zero_le_one d.one_le_Cwc
  have hC1 : 0 ≤ d.C1pp := le_trans zero_le_one d.one_le_C1pp
  have hs : 0 ≤ Real.sqrt d.C1pp := Real.sqrt_nonneg _
  have hl := MI.one_le_logL (show 1 ≤ p.n * p.W by omega)
  have hl504 : 1 ≤ MI.logL (p.n * p.W) ^ 504 := one_le_pow₀ hl
  refine ⟨?_, ?_, ?_⟩
  · have hav := avConst_le_logL d hN2 hn
    have hcz := MI.cAvZ_nonneg d
    have hK : 0 ≤ 4 * vsCK d * Real.sqrt d.C1pp := by positivity
    have t1 := mul_le_mul_of_nonneg_right hav hΦ0
    have t2 := mul_le_mul_of_nonneg_left h3 hK
    have t3 := mul_le_mul_of_nonneg_left hl504 (mul_nonneg hK hΦ0)
    unfold llForcingGainP7 llCF
    have e1 : 4 * vsCK d * Real.sqrt d.C1pp * zigPsiA d (p.n * p.W) (n + 3) *
        P.lEta T ^ (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 3))) =
        4 * vsCK d * Real.sqrt d.C1pp * (zigPsiA d (p.n * p.W) (n + 3) *
          P.lEta T ^ (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 3)))) := by ring
    rw [e1]
    linarith
  · have t3 := mul_le_mul_of_nonneg_left h3
      (by positivity : 0 ≤ 2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp))
    have t2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ vsCK d ^ 2 * d.C1pp)
    unfold llR0Gain llCR
    have e1 : 2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * zigPsiA d (p.n * p.W) (n + 3)) *
          P.lEta T ^ (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 3))) +
        vsCK d ^ 2 * d.C1pp * zigPsiA d (p.n * p.W) (n + 2) *
          P.lEta T ^ (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 2))) =
        2 * (vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp) * (zigPsiA d (p.n * p.W) (n + 3) *
          P.lEta T ^ (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 3)))) +
        vsCK d ^ 2 * d.C1pp * (zigPsiA d (p.n * p.W) (n + 2) *
          P.lEta T ^ (-(Expo.lossBeta (n + 4) - Expo.lossBeta (n + 2)))) := by ring
    rw [e1]
    linarith
  · have h := Forcing.phiAvF_le_phiAv hNr hX hY (k := n + 4) (by omega) hn (ξ := d.xi)
    rw [← (MI.aprPsi_eq d (p.n * p.W)).1, ← (MI.aprPsi_eq d (p.n * p.W)).2] at h
    exact h

/-- **The gained (LL) level is `≤ N^{ε/2} · polylog · φ^{av}_{k,T}`**: for `z ∈ 𝒟`, `T ≤ 1`,
 `k = n + 4 ≤ 8`, `ε ≥ 0`, `N = p.n p.W`, `ℓ = 1 + log N`:
`llLevelGainP7 d p z n ε T ≤ N^{ε/2} (llGainA d n ℓ^{504}) φ^{av}_{k,T}`,
`φ^{av}_{k,T} = Expo.phiAv N ξ L_T Y_T k`, `Y_T = ZigProof.yZig P T`. -/
theorem llLevelGainP7_le {ε : ℝ} (hε : 0 ≤ ε) :
    llLevelGainP7 d p z n ε T ≤
      ((p.n * p.W : ℕ) : ℝ) ^ (ε / 2) * (llGainA d n * MI.logL (p.n * p.W) ^ 504) *
        phiAv ((p.n * p.W : ℕ) : ℝ) d.xi ((zigPsiData p d.D z).lEta T)
          (ZigProof.yZig (zigPsiData p d.D z) T) (n + 4) := by
  set P := zigPsiData p d.D z
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hN2 := MI.mi_N_two p
  have hNr : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast hN
  have hzi : 0 < P.z.im := hz.im_pos hN
  have hX : 0 < P.lEta T := P.lEta_pos hN p.W_pos hzi hT1
  have hY : 0 < ZigProof.yZig P T :=
    div_pos (Real.sqrt_pos.2 (mul_pos hNr (vsHeight_pos hzi hT1))) hX
  obtain ⟨hB, hR, hΦφ⟩ := gain_parts_le d hz hT1 hn
  set Φ := Forcing.phiAvF (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) (P.lEta T)
    (Forcing.yScale P T) (n + 4)
  set φ := phiAv ((p.n * p.W : ℕ) : ℝ) d.xi (P.lEta T) (ZigProof.yZig P T) (n + 4)
  set ℓ := MI.logL (p.n * p.W) ^ 504
  set E := ((p.n * p.W : ℕ) : ℝ) ^ (ε / 2)
  have hφ1 : 1 ≤ φ := one_le_phiAv hNr hX hY (n + 4)
  have hl := MI.one_le_logL (show 1 ≤ p.n * p.W by omega)
  have hl1 : 1 ≤ ℓ := one_le_pow₀ hl
  have hE1 : 1 ≤ E := Real.one_le_rpow hN1 (by linarith)
  have hpsi := zig_psi_ge d p
  have hpsi0 : ∀ j, 0 ≤ zigPsiI d (p.n * p.W) j ∧ 0 ≤ zigPsiA d (p.n * p.W) j := fun j =>
    ⟨le_trans zero_le_one (hpsi j).1, le_trans zero_le_one (hpsi j).2⟩
  have hΦ0 : 0 ≤ Φ := Forcing.phiAvF_nonneg hpsi0 hX.le
    (div_nonneg (Real.sqrt_nonneg _) hX.le) (n + 4)
  -- the noise term
  have hqv : QV.qvPhiAv (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) (n + 4) (P.lEta T) ≤ φ := by
    have h := MI.qvPhiAv_le_phiAv hNr hX hY (ξ := d.xi) (k := n + 4) (by omega) hn
    rw [← (MI.aprPsi_eq d (p.n * p.W)).1, ← (MI.aprPsi_eq d (p.n * p.W)).2] at h
    exact h
  have hqv0 := (QV.qvPhiAv_pos (fun j => (hpsi j).1) (fun j => (hpsi0 j).2) (n + 4) hX).le
  have hsq := sqrt_qvC_lam_le d hN2
  have hc1 := (llC1_pos d n).le
  have hr0 : 0 ≤ Real.sqrt (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0)) :=
    Real.sqrt_nonneg _
  have hZ : llZ d (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W))
      (Apriori.aprLamM d (p.n * p.W)) (P.lEta T) n ≤ llCZ d n * ℓ * φ := by
    unfold llZ llCZ
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 4 := by positivity
    calc ((n : ℝ) + 4) * Real.sqrt (QV.qvC d * Apriori.aprLamM d (p.n * p.W) ^ 3) *
          QV.qvPhiAv (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) (n + 4) (P.lEta T) *
          llC1 d n * Real.sqrt (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0))
        ≤ ((n : ℝ) + 4) * (Real.sqrt (QV.qvC d) * (MI.aLam d ^ 2 * ℓ)) * φ * llC1 d n *
          Real.sqrt (2 / ((2 - 2 * Expo.lossBeta (n + 4)) * imLower d.kappa d.C0)) := by
          gcongr
      _ = _ := by ring
  have hCD := llCD_nonneg d hn
  have hCF : 0 ≤ llCF d n := by
    have := MI.cAvZ_nonneg d
    have := (vsCK_pos d).le
    unfold llCF
    positivity
  have hCR : 0 ≤ llCR d := by
    have := (vsCK_pos d).le
    have := le_trans zero_le_one d.one_le_Cwc
    have := le_trans zero_le_one d.one_le_C1pp
    unfold llCR
    positivity
  have hCZ : 0 ≤ llCZ d n := by
    unfold llCZ
    have := MI.aLam_nonneg d
    positivity
  have hBφ : llForcingGainP7 d p z n T ≤ llCF d n * ℓ * φ :=
    hB.trans (mul_le_mul_of_nonneg_left hΦφ (by positivity))
  have hRφ : llR0Gain d (zigPsiA d (p.n * p.W)) n (P.lEta T) ≤ llCR d * ℓ * φ := by
    have h1 := mul_le_mul_of_nonneg_left hΦφ hCR
    have h2 := mul_le_mul_of_nonneg_left hl1 (mul_nonneg hCR (by linarith : (0 : ℝ) ≤ φ))
    have e1 : llCR d * φ * ℓ = llCR d * ℓ * φ := by ring
    linarith
  -- assemble
  have hφ0 : 0 ≤ φ := by linarith
  have hEZ := mul_le_mul_of_nonneg_left hZ (by linarith : (0 : ℝ) ≤ E)
  have hCDB := mul_le_mul_of_nonneg_left hBφ hCD
  have hlφ : 1 ≤ ℓ * φ := by
    have := mul_le_mul hl1 hφ1 zero_le_one (by linarith)
    linarith
  have k1 : llCD d n * (llCF d n * ℓ * φ) ≤ E * (llCD d n * llCF d n * (ℓ * φ)) := by
    have h := mul_le_mul_of_nonneg_right hE1 (mul_nonneg (mul_nonneg hCD hCF)
      (by linarith : (0 : ℝ) ≤ ℓ * φ))
    have e1 : llCD d n * (llCF d n * ℓ * φ) = 1 * (llCD d n * llCF d n * (ℓ * φ)) := by ring
    linarith
  have k2 : llCR d * ℓ * φ ≤ E * (llCR d * (ℓ * φ)) := by
    have h := mul_le_mul_of_nonneg_right hE1 (mul_nonneg hCR (by linarith : (0 : ℝ) ≤ ℓ * φ))
    have e1 : llCR d * ℓ * φ = 1 * (llCR d * (ℓ * φ)) := by ring
    linarith
  have k3 : (1 : ℝ) ≤ E * (ℓ * φ) := by
    have := mul_le_mul hE1 hlφ zero_le_one (by linarith)
    linarith
  unfold llLevelGainP7 llLevelGain llGridLevelGain
  have e : E * (llGainA d n * ℓ) * φ = 2 * (E * (llCD d n * llCF d n * (ℓ * φ))) +
      2 * (E * (llCZ d n * ℓ * φ)) + 2 * (E * (llCR d * (ℓ * φ))) + E * (ℓ * φ) := by
    unfold llGainA
    ring
  rw [e]
  linarith

end Level

end BlockBand.Native.ErdosRiabov.LLGrid
