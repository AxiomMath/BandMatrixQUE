module

public import BlockBand.Native.ErdosRiabov.MI.Conclusion

/-!
# The saturated part of the master inequality from a uniform linear-term bound

Probability: `driverLaw model.law`.

* `satLevel d p z t k = N^{ε'/2} φ^{av}_{k,t}`: the level of the saturated linear term
  (`φ^{av}_{k,t} = Expo.phiAv N ξ L_t Y_t k` at the zig data).
* `SatLinUnif` (named hypothesis): for every `d`, `D > 0` there is `N₀` such that, in the setting
  of `MI.MasterIneqSat`, for every `t ≤ 1`, `k = n+1 ≤ 8`, saturated `σ` and sites `u`,
  `MI.SatLinBound … σ u t (satLevel …) (N^{-D}/2)` (the saturated linear-term bound for all `s ∈ (0,t]` on one event).
* `satA d k`, `satN0 d D`: an explicit constant with `C_av iF(k/2-β_k)`, `iF(k/2-β_k) + mSatC`
  `≤ satA d k ℓ_N^{757}`, and the explicit `N₀`.
* **`masterIneqSat_of_satLinUnif`**: `SatLinUnif → MI.MasterIneqSat`, with
  `N₀ = max N₀^{lin} ⌈satN0 d D⌉`. It applies `MI.masterIneq_sat` with `B = N^{ε'/2} φ`,
  `q = N^{-D}/2`. The saturated absorption inequality becomes
  `MI.Absorb (C_av iF) (iF + mSatC) N ε'`, and the tail is `4 e^{-N^{ε'}/4} ≤ N^{-D}/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.SatLin

open MeasureTheory Set Finset
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Forcing
open BlockBand.Native.ErdosRiabov.QV
open BlockBand.Native.ErdosRiabov.MI
open BlockBand.Native.ErdosRiabov.Assembly (zigPsiData)
open BlockBand.Native.ErdosRiabov.Apriori (aprPsiI aprPsiA aprLamM)
open BlockBand.SourceProcess.FiniteDriverIntegration
open Expo (lossAlpha lossBeta)
open scoped NNReal ENNReal

/-! ## The level and the named hypothesis -/

/-- The level of the saturated linear term, `N^{ε'/2} φ^{av}_{k,t}` (zig data). -/
def satLevel (d : VSData) (p : BlockBand.Parameters) (z : ℂ) (t : ℝ) (k : ℕ) : ℝ :=
  ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 2) *
    Expo.phiAv ((p.n * p.W : ℕ) : ℝ) d.xi ((zigPsiData p d.D z).lEta t)
      (ZigProof.yZig (zigPsiData p d.D z) t) k

/-- **The uniform saturated linear-term bound (named hypothesis).** For every `d` and `D > 0`
there is `N₀` such that, in the setting of `MI.MasterIneqSat`, for every deterministic `t ≤ 1`,
`k = n+1 ≤ 8`, saturated `σ` and sites `u`, outside an event of probability `≤ N^{-D}/2`, on
`{t ≤ τ}`, `η_s |T̂^{⊕k}_s[𝒳_s](u)| ≤ N^{ε'/2} φ^{av}_{k,t} L_s^{β_k} s^av_s(u)` for every
`s ∈ (0,t]` (`MI.SatLinBound`). -/
def SatLinUnif : Prop :=
  ∀ (d : VSData) (D : ℝ), 0 < D → ∃ N₀ : ℕ,
    ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W → d.zeta0 < 1 →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ),
        BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z →
        ∀ t : ℝ≥0, t ≤ 1 → ∀ n : ℕ, n + 1 ≤ 8 → ∀ σ : Fin (n + 1) → Bool,
          ¬ HasDesatFactor σ → ∀ u : Fin (n + 1) → Fin (p.n * p.W),
            SatLinBound (model.law : Measure p.SiteMatrix) (zigPsiData p d.D z)
              (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) σ u t
              (satLevel d p z t (n + 1)) (((p.n * p.W : ℕ) : ℝ) ^ (-D) / 2)

/-! ## Exponents -/

/-- `0 ≤ k/2 - β_k` for `k = n+1 ≤ 8`. -/
theorem satGamma_nonneg {n : ℕ} (hn : n + 1 ≤ 8) : 0 ≤ ((n : ℝ) + 1) / 2 - lossBeta (n + 1) := by
  by_cases h0 : n = 0
  · subst h0
    rw [lossBeta_eq (by norm_num), qv_alpha_of_le_four (by norm_num)]
    norm_num
  · have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    linarith [qv_beta_le_one (k := n + 1) hn]

/-- `0 ≤ k - 2β_k` for `k = n+1 ≤ 8`. -/
theorem satGammaM_nonneg {n : ℕ} (hn : n + 1 ≤ 8) : 0 ≤ (n : ℝ) + 1 - 2 * lossBeta (n + 1) := by
  have := satGamma_nonneg hn
  linarith

/-! ## The constant -/

/-- The constant of the saturated absorption:
`(3k²+k+1) c_av A_Z² A_I(k/2-β_k) + A_I(k/2-β_k) + k (1 + 𝔠 A_Λ³ A_I(k-2β_k))`. -/
def satA (d : VSData) (k : ℕ) : ℝ :=
  ((3 * k * k + k + 1 : ℕ) : ℝ) * cAvZ d * 1 * aZ d k ^ 2 * aInt d ((k : ℝ) / 2 - lossBeta k) +
    aInt d ((k : ℝ) / 2 - lossBeta k) +
    (k : ℝ) * 1 * (1 + qvC d * aLam d ^ 3 * aInt d ((k : ℝ) - 2 * lossBeta k))

/-- `satA` at `k = n+1`, in real-cast form. -/
theorem satA_succ (d : VSData) (n : ℕ) :
    satA d (n + 1) =
      ((3 * (n + 1) * (n + 1) + (n + 1) + 1 : ℕ) : ℝ) * cAvZ d * 1 * aZ d (n + 1) ^ 2 *
          aInt d (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) +
        aInt d (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) +
        ((n : ℝ) + 1) * 1 * (1 + qvC d * aLam d ^ 3 * aInt d ((n : ℝ) + 1 - 2 * lossBeta (n + 1)))
    := by
  unfold satA
  push_cast
  ring_nf

/-- The parts of `satA` are nonnegative (`k = n+1 ≤ 8`). -/
theorem satA_parts_nonneg (d : VSData) {n : ℕ} (hn : n + 1 ≤ 8) :
    0 ≤ ((3 * (n + 1) * (n + 1) + (n + 1) + 1 : ℕ) : ℝ) * cAvZ d * 1 * aZ d (n + 1) ^ 2 *
        aInt d (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) ∧
      0 ≤ aInt d (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) ∧
      0 ≤ ((n : ℝ) + 1) * 1 *
        (1 + qvC d * aLam d ^ 3 * aInt d ((n : ℝ) + 1 - 2 * lossBeta (n + 1))) := by
  have a1 := aInt_nonneg d (satGamma_nonneg hn)
  have a2 := aInt_nonneg d (satGammaM_nonneg hn)
  have := cAvZ_nonneg d; have := aLam_nonneg d; have := (qvC_pos d).le
  refine ⟨by positivity, a1, by positivity⟩

theorem satA_nonneg (d : VSData) {n : ℕ} (hn : n + 1 ≤ 8) : 0 ≤ satA d (n + 1) := by
  obtain ⟨h1, h2, h3⟩ := satA_parts_nonneg d hn
  rw [satA_succ]
  linarith

/-- The explicit `N₀`: `Σ_{k ≤ 8} absorbN0 (satA d k) 757 ε' + tailN0 ε' (D+1) + 2`. -/
def satN0 (d : VSData) (D : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 9, absorbN0 (satA d k) 757 d.epsP + tailN0 d.epsP (D + 1) + 2

theorem le_satN0 (d : VSData) (D : ℝ) {k : ℕ} (hk : k ≤ 8) :
    absorbN0 (satA d k) 757 d.epsP ≤ satN0 d D ∧ tailN0 d.epsP (D + 1) ≤ satN0 d D ∧
      2 ≤ satN0 d D := by
  have hs := Finset.sum_nonneg fun j (_ : j ∈ Finset.range 9) =>
    absorbN0_nonneg (satA d j) 757 d.epsP
  have h1 := Finset.single_le_sum (f := fun j => absorbN0 (satA d j) 757 d.epsP)
    (fun j _ => absorbN0_nonneg _ _ _) (Finset.mem_range.mpr (show k < 9 by omega))
  have h2 := tailN0_nonneg d.epsP (D + 1)
  unfold satN0
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ## The polylog bounds -/

section Bounds

variable (d : VSData) {p : BlockBand.Parameters} {P : PsiData (p.n * p.W)} (hPW : P.W = p.W)
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {T : ℝ} (hT1 : T ≤ 1)
include hPW hz hT1

/-- `C_av iF(k/2-β_k) ≤ satA ℓ^{757}` and `iF(k/2-β_k) + mSatC ≤ satA ℓ^{757}`. -/
theorem sat_FM_le {n : ℕ} (hn : n + 1 ≤ 8) :
    avConst d (fun _ => aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 1)) (n + 1) *
        intF d P (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) T ≤
      satA d (n + 1) * logL (p.n * p.W) ^ 757 ∧
    intF d P (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) T +
        mSatC d P (aprLamM d (p.n * p.W)) n T ≤
      satA d (n + 1) * logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, he0, hZ⟩ := z_le d (p := p) hn
  obtain ⟨hp1, hp2, hp3⟩ := satA_parts_nonneg d hn
  have hℓ := mi_logL_one (p := p)
  have hℓ0 : 0 ≤ logL (p.n * p.W) := zero_le_one.trans hℓ
  have hp := pow_nonneg hℓ0 757
  have hl1 : logL (p.n * p.W) ≤ logL (p.n * p.W) ^ 757 := by
    simpa using pow_le_pow_right₀ hℓ (show 1 ≤ 757 by norm_num)
  have hγ := satGamma_nonneg hn
  have hγM := satGammaM_nonneg hn
  have hI0 := intF_nonneg d P hPW hz hT1 hγ
  have hI := intF_le_logL d P hPW hz hT1 hγ
  have hA0 := aInt_nonneg d hγ
  -- the forcing constant
  have hF := fbound_gen (m := ((3 * (n + 1) * (n + 1) + (n + 1) + 1 : ℕ) : ℝ)) (K := 1) (K' := 1)
    hℓ (Nat.cast_nonneg _) (cAv_nonneg d hΛ0 he0) (cAvZ_nonneg d) (cAv_le d hΛ0 he0)
    (by linarith) hZ zero_le_one le_rfl hI0 hA0 hI
  -- the noise constant
  have hM := mbound_gen (m := (n : ℝ) + 1) (K := 1) (K' := 1) hℓ (by positivity) zero_le_one
    le_rfl (qvC_pos d).le hΛ0 (aprLamM_le_logL d (mi_N_two p)) (intF_nonneg d P hPW hz hT1 hγM)
    (intF_le_logL d P hPW hz hT1 hγM)
  rw [satA_succ]
  constructor
  · unfold avConst
    refine (le_of_eq (by ring)).trans (hF.trans ?_)
    nlinarith
  · unfold mSatC
    have e1 : ((n : ℝ) + 1) * Real.sqrt (qvC d * aprLamM d (p.n * p.W) ^ 3 *
        intF d P ((n : ℝ) + 1 - 2 * lossBeta (n + 1)) T) =
        ((n : ℝ) + 1) * 1 * Real.sqrt (qvC d * aprLamM d (p.n * p.W) ^ 3 *
          intF d P ((n : ℝ) + 1 - 2 * lossBeta (n + 1)) T) := by ring
    rw [e1]
    have hI' : intF d P (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) T ≤
        aInt d (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) * logL (p.n * p.W) ^ 757 :=
      hI.trans (mul_le_mul_of_nonneg_left hl1 hA0)
    nlinarith

end Bounds

/-! ## The tail -/

/-- `4 e^{-N^{ε}/4} + N^{-D}/2 ≤ N^{-D}` in `ℝ≥0∞` for `N ≥ max 2 (tailN0 ε (D+1))`. -/
theorem tail_half_ennreal {ε D : ℝ} (hε : 0 < ε) {N : ℕ} (hN2 : (2 : ℝ) ≤ N)
    (hN : tailN0 ε (D + 1) ≤ N) :
    4 * ENNReal.ofReal (Real.exp (-((N : ℝ) ^ ε / 4))) + ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hN1 : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hn0 : (0 : ℝ) < N := by linarith
  have ht := tail_le hε hN1 hN
  have hD : (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) / 2 := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hn0, Real.rpow_neg_one]
    have h0 := Real.rpow_nonneg hn0.le (-D)
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by norm_num) hN2) h0
  have hpos : 0 ≤ (N : ℝ) ^ (-D) / 2 := by have := Real.rpow_nonneg hn0.le (-D); positivity
  rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) hpos]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

/-! ## The reduction -/

/-- **The saturated part of the master inequality from the uniform linear-term bound**, conditional on
`SatLinUnif`.
`SatLinUnif → MI.MasterIneqSat`, with `N₀ = max N₀^{lin} ⌈satN0 d D⌉`: `MI.masterIneq_sat` at
`B = N^{ε'/2} φ^{av}_{k,t}`, `q = N^{-D}/2`. The absorption is `MI.Absorb (C_av iF)
(iF + mSatC) N ε'` (`absorb_of_logL`, `sat_FM_le`); the tail is `tail_half_ennreal`. -/
theorem masterIneqSat_of_satLinUnif (h : SatLinUnif) : MasterIneqSat := by
  intro d D hD
  obtain ⟨Nl, hl⟩ := h d D hD
  refine ⟨max Nl ⌈satN0 d D⌉₊, fun p hpb hN hζ hband model z hz t ht k hk i hσ => ?_⟩
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk8 : k ≤ 8 := (Finset.mem_Icc.mp hk).2
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨σ, u⟩ := i
  have hNR : satN0 d D ≤ ((p.n * p.W : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hN)
  obtain ⟨hNA, hNt, hN2⟩ := le_satN0 d D hk8
  have hT1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have hb : d.b = p.b := hpb.symm
  have hz' : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 (zigPsiData p d.D z).z := hz
  set P := zigPsiData p d.D z
  set μ : Measure p.SiteMatrix := (model.law : Measure p.SiteMatrix)
  set N : ℝ := ((p.n * p.W : ℕ) : ℝ)
  have hN0 : 0 < N := by simp only [N]; linarith
  have hlin := hl p hpb (le_of_max_le_left hN) hζ hband model z hz t ht n hk8 σ hσ u
  obtain ⟨hF, hM⟩ := sat_FM_le d (P := P) rfl hz' hT1 hk8
  have hAbs := absorb_of_logL d.epsP_pos (satA_nonneg d hk8) hF hM (hNA.trans hNR)
  set φ := Expo.phiAv N d.xi (P.lEta t) (Forcing.yScale P t) (n + 1)
  have hφ0 : 0 ≤ φ := by
    obtain ⟨-, hX, hY⟩ := mi_scalars d hb rfl rfl rfl hz' hband t hT1
    exact (phiAvF_nonneg (fun k => ⟨Real.rpow_nonneg hN0.le _, Real.rpow_nonneg hN0.le _⟩)
      hX.le hY.le _).trans (phiAvF_le_phiAv hN0 hX hY (by omega) hk8)
  have hB : 0 ≤ satLevel d p z t (n + 1) := by
    unfold satLevel
    exact mul_nonneg (Real.rpow_nonneg hN0.le _) hφ0
  have hAbs' : satLevel d p z t (n + 1) * intF d P (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) t +
      (avConst d (fun _ => aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 1)) (n + 1) *
          intF d P (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) t +
        N ^ (d.epsP / 2) * mSatC d P (aprLamM d (p.n * p.W)) n t) * φ ≤ N ^ d.epsP * φ := by
    unfold Absorb at hAbs
    have e : satLevel d p z t (n + 1) = N ^ (d.epsP / 2) * φ := rfl
    rw [e]
    have := mul_le_mul_of_nonneg_right hAbs hφ0
    nlinarith
  have hsat := masterIneq_sat μ d hb rfl rfl rfl hz' hband t hT1 hk8 σ hσ u hB hlin hAbs'
  refine le_trans (measure_mono ?_) (hsat.trans
    (tail_half_ennreal d.epsP_pos (hN2.trans hNR) (hNt.trans hNR)))
  intro x hx
  refine ⟨hx.1, ?_⟩
  have h2 := hx.2
  rw [← pathH_coe] at h2
  exact h2

end BlockBand.Native.ErdosRiabov.SatLin
