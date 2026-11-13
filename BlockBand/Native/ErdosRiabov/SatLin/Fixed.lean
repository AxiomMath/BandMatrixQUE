module

public import BlockBand.Native.ErdosRiabov.SatLin.Grid

/-!
# The saturated linear-term bound at one grid time, with an explicit `T`-uniform level

Probability: `driverLaw μ`. Setting: the zig thresholds `ψ = aprPsiI d N`, `ψ^av = aprPsiA d N`,
`Λ = aprLamM d N`, `τ = tau p P ψ ψ^av`, a final time `T ≤ 1` and a grid time `0 < T' ≤ T`.
The bounds hold for every slot.

The level `b` does not depend on `T'`: `iF(γ, T')` does not depend on `T'`
(`intF_time_indep`), `φ^{av,qv}(L_{T'}) ≤ φ^{av,qv}(L_T)` (`qvPhiAv_anti`), and the forcing
control parameter at `s ≤ T'` is bounded by its value at `T` (`MI.phiAvF_anti`).

* `bShort d P T r` (`k = 2`):
  `C_reg C_P² B_F iF(0) + C_K ψ^av_1 + 2r·2√(𝔠Λ³iF(0)) φ^{qv}_2(L_T) C_reg C_P²`,
  `B_F = C_av Φ^{av,f}_2(L_T, Y_T) + 2 C_K ψ^av_1`;
* `bLong d P n B₂ T r` (`k = n+4`): `(C_K C_w C_P^k B₁ + C_P^{k+1} B₂) iF(1-β_k)
  + 2r k √(𝔠Λ³iF(2-2β_k)) φ^{qv}_k(L_T) C_K C_w C_P^k`, `B₁ = C_av Φ^{av,f}_k(L_T, Y_T)`.
* **`satSlot_short`**: `P(T' ≤ τ, slot k fails at level bShort at T') ≤ 4 e^{-r²}`
  (`Circ.linTerm_short` at `T := T'`, `λ = 2r√(Ay)`).
* **`satSlot_long`**: `P(T' ≤ τ, x ∈ circLLEvent σ τ B₂ T, slot k fails at level bLong at T')
  ≤ 4 e^{-r²}` (`Circ.linTerm_long_event` at `T := T'`).
* `slotBad_rotTo`: the failure of slot `i` is the failure of the last slot for the rotated
  pattern and sites (`circSlot_avErr_rotTo`, `MBound.mb_sAv_rotTo`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.SatLin

open MeasureTheory Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Forcing
open BlockBand.Native.ErdosRiabov.QV
open BlockBand.Native.ErdosRiabov.Circ
open BlockBand.Native.ErdosRiabov.Evol (pathH forcingAv)
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.MI (intF eMI avConst_nonneg)
open BlockBand.Native.ErdosRiabov.Apriori (aprPsiI aprPsiA aprLamM)
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open BlockBand.SourceProcess.FiniteDriverIntegration
open Expo (lossAlpha lossBeta)
open scoped NNReal ENNReal ComplexConjugate

variable {p : BlockBand.Parameters}

/-! ### Time-independence and monotonicity -/

/-- `iF(γ, T') = iF(γ, T)`: `L^γ y_γ` is `2/(γ c_m)` or `c_m⁻¹ log((C₀+1)N)`. -/
theorem intF_time_indep (d : VSData) (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) (γ : ℝ) {T T' : ℝ} (hT1 : T ≤ 1)
    (hT'1 : T' ≤ 1) : intF d P γ T' = intF d P γ T := by
  have hN := MI.mi_N_pos p
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hL := P.lEta_pos hN hW (hz.im_pos hN) hT1
  have hL' := P.lEta_pos hN hW (hz.im_pos hN) hT'1
  unfold intF qvIntRule
  split_ifs with h
  · rw [h, Real.rpow_zero, Real.rpow_zero]
  · rw [Real.rpow_neg hL.le, Real.rpow_neg hL'.le]
    have h1 : P.lEta T ^ γ ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
    have h2 : P.lEta T' ^ γ ≠ 0 := (Real.rpow_pos_of_pos hL' _).ne'
    field_simp

/-- `φ^{av,qv}_k(L)` is antitone in `L` (`k ≤ 8`, `ψ ≥ 0`). -/
theorem qvPhiAv_anti {psiI psiA : ℕ → ℝ} (hI : ∀ j, 0 ≤ psiI j) (hA : ∀ j, 0 ≤ psiA j)
    {k : ℕ} (hk : k ≤ 8) {L L' : ℝ} (hL' : 0 < L') (hLL : L' ≤ L) :
    qvPhiAv psiI psiA k L ≤ qvPhiAv psiI psiA k L' := by
  unfold qvPhiAv
  split_ifs with h3 h7
  · refine Real.sqrt_le_sqrt ?_
    have hg : 0 ≤ 1 / 2 - lossAlpha (2 * k + 2) := by
      linarith [qv_alpha_le_half (k := 2 * k + 2) (by omega)]
    have := MI.rpow_neg_anti hL' hLL hg
    have := hI (2 * k + 2)
    nlinarith
  · exact le_rfl
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (hI 5)
    have hg : 0 ≤ 1 - lossBeta 8 := by linarith [qv_beta_le_one (k := 8) le_rfl]
    have := MI.rpow_neg_anti hL' hLL hg
    have := hA 8
    nlinarith

theorem lossBeta_one_two : lossBeta 1 = 0 ∧ lossBeta 2 = 0 := by
  refine ⟨?_, ?_⟩ <;>
    rw [lossBeta_eq (by norm_num), qv_alpha_of_le_four (by norm_num)]

/-- The rotated slot: failure of slot `i` = failure of the last slot for `σ ∘ rot^{i+1}` at
`mbRotTo i u` (`k = n+2`). -/
theorem slotBad_rotTo (P : PsiData (p.n * p.W)) (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0)
    {n : ℕ} (σ : Fin (n + 2) → Bool) (u : Fin (n + 2) → Fin (p.n * p.W)) (b : ℝ)
    (i : Fin (n + 2)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (x : RingSample p) :
    slotBad P σ u b i s x ↔
      slotBad P (fun l => σ ((finRotate (n + 2) ^ ((i : ℕ) + 1)) l))
        (MBound.mbRotTo i u) b (Fin.last (n + 1)) s x := by
  unfold slotBad
  rw [circSlot_avErr_rotTo P hS hz hs (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
    σ i (pathH p x s) u, MBound.mb_sAv_rotTo P s i u]

/-! ### The levels -/

/-- The level of the short slot (`k = 2`). -/
def bShort (d : VSData) (P : PsiData (p.n * p.W)) (T r : ℝ) : ℝ :=
  onestepConst d * kernelActionConst d ^ 2 *
      (avConst d (fun _ => aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) 2) 2 *
          phiAvF (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) (P.lEta T) (yScale P T) 2 +
        2 * vsCK d * aprPsiA d (p.n * p.W) 1) * intF d P 0 T +
    vsCK d * aprPsiA d (p.n * p.W) 1 +
    2 * r * (2 * Real.sqrt (qvC d * aprLamM d (p.n * p.W) ^ 3 * intF d P 0 T) *
      qvPhiAv (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) 2 (P.lEta T) *
        (onestepConst d * kernelActionConst d ^ 2))

/-- The forcing level of the long slot, `B₁ = C_av Φ^{av,f}_k(L_T, Y_T)` (`k = n+4`). -/
def bOne (d : VSData) (P : PsiData (p.n * p.W)) (n : ℕ) (T : ℝ) : ℝ :=
  avConst d (fun _ => aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 4)) (n + 4) *
    phiAvF (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) (P.lEta T) (yScale P T) (n + 4)

/-- The level of the long slot (`k = n+4`, (LL) level `B₂`). -/
def bLong (d : VSData) (P : PsiData (p.n * p.W)) (n : ℕ) (B₂ T r : ℝ) : ℝ :=
  (vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * bOne d P n T +
      kernelActionConst d ^ (n + 4) * kernelActionConst d * B₂) *
      intF d P (1 - lossBeta (n + 4)) T +
    2 * r * (((n : ℝ) + 4) *
      Real.sqrt (qvC d * aprLamM d (p.n * p.W) ^ 3 * intF d P (2 - 2 * lossBeta (n + 4)) T) *
      qvPhiAv (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) (n + 4) (P.lEta T) *
        (vsCK d * d.Cwc * kernelActionConst d ^ (n + 4)))

/-! ### The fixed-time slot bounds -/

section Fixed

variable (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (d : VSData)
  {P : PsiData (p.n * p.W)} (hb : d.b = p.b) (hPS : P.S = shortRingProfile p.b p.n p.W)
  (hPW : P.W = p.W) (hPD : P.D = d.D) (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2)
include hb hPS hPW hPD hz hP6

/-- The short forcing hypothesis of `linTerm_short`, from the a priori forcing bounds at each `s ≤ τ`, with the
forcing parameter at `T`. -/
theorem satFB_short {T : ℝ≥0} (hT1 : (T : ℝ) ≤ 1) {T' : ℝ≥0} (hT'T : T' ≤ T)
    (σ : Fin (0 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) (x : RingSample p) :
    ∀ s ∈ Ioc (0 : ℝ) T', ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤
        tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) x → ∀ y, vsHeight P.z s *
      ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
        extraForcingShort P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
      (avConst d (fun _ => aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) 2) 2 *
          phiAvF (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) (P.lEta T) (yScale P T) 2 +
        2 * vsCK d * aprPsiA d (p.n * p.W) 1) * P.sAv y s := by
  intro s hs hsτ y
  have hN := MI.mi_N_pos p
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hpsi := MI.mi_psi_ge d p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  have hs0 : 0 ≤ s := hs.1.le
  have hsT : s ≤ T := hs.2.trans (by exact_mod_cast hT'T)
  have hs1 : s ≤ 1 := hsT.trans hT1
  have hAPs : ∀ s'' ∈ Ioc (0 : ℝ) s, QV.APriori P (aprPsiI d (p.n * p.W))
      (aprPsiA d (p.n * p.W)) (aprLamM d (p.n * p.W)) s'' (pathH p x s'') := by
    have h := MI.mi_ap_path d hb hPS hPW hPD hz hpsi s.toNNReal x hsτ
    rwa [Real.coe_toNNReal s hs0] at h
  obtain ⟨c, hAPf, hIs, -, -, -, -, -⟩ :=
    MI.mi_at d hb hPS hPW hPD hz hP6 hs0 hs1 hpsi (pathH p x) hAPs (s := s) ⟨hs.1, le_rfl⟩
  have hPS' : P.S = shortRingProfile d.b p.n p.W := by rw [hPS, hb]
  have he0 := MI.eMI_nonneg d hN 2
  have hE := Apriori.mbounds_extra_uncond hc hs0 hs1 (k := 2) le_rfl
  have h := circ_integrand_short d P hPW hPD hPS' hz ⟨hs0, hs1⟩ c
    (VS.vsBandFin_isHermitian _ _) hAPf hpsi hIs (fun _ => by linarith) he0 hE σ hσ y
  rw [lossBeta_one_two.2, Real.rpow_zero, mul_one] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (sAv_pos c y).le)
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hLT := (hF.inputs T ⟨T.2, le_rfl⟩).lEta_pos
  have hpsi0 : ∀ n, 0 ≤ aprPsiI d (p.n * p.W) n ∧ 0 ≤ aprPsiA d (p.n * p.W) n := fun n =>
    ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
  have hΦ := MI.phiAvF_anti hpsi0 hLT (hF.anti s ⟨hs0, hsT⟩) (MI.yScale_anti P hN hW hzi hsT hT1)
    (k := 2) (by norm_num)
  have hC := avConst_nonneg d (by linarith) he0 2 (LamM := aprLamM d (p.n * p.W))
  have := mul_le_mul_of_nonneg_left hΦ hC
  linarith

/-- **The saturated linear-term bound at one grid time, short chains (`k = 2`, last slot).** For `0 < T' ≤ T ≤ 1`,
saturated `σ`, `r ≥ 0`:
`P(T' ≤ τ, bShort L_{T'}^{β_2} s^av_{T'}(u) < η_{T'} |T̂^{(2)}_{T'}[𝒳_{T'}](u)|) ≤ 4 e^{-r²}`. -/
theorem satSlot_short {T : ℝ≥0} (hT1 : (T : ℝ) ≤ 1) {T' : ℝ≥0} (hT'T : T' ≤ T)
    (hT'0 : 0 < (T' : ℝ)) (σ : Fin (0 + 2) → Bool) (hσ : ¬ HasDesatFactor σ)
    (u : Fin (0 + 2) → Fin (p.n * p.W)) {r : ℝ} (hr : 0 ≤ r) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T' : WithTop ℝ≥0) ≤
        tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) x ∧
        slotBad P σ u (bShort d P T r) (Fin.last (0 + 1)) T' x} ≤
      4 * ENNReal.ofReal (Real.exp (-r ^ 2)) := by
  have hN := MI.mi_N_pos p
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hpsi := MI.mi_psi_ge d p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  have hI : ∀ j, 1 ≤ aprPsiI d (p.n * p.W) j := fun j => (hpsi j).1
  have hAv : ∀ j, 0 ≤ aprPsiA d (p.n * p.W) j := fun j => by linarith [(hpsi j).2]
  have hτ := tau_isStoppingTime μ hN hW hzi hS (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W))
  have hT'1 : (T' : ℝ) ≤ 1 := (show (T' : ℝ) ≤ T by exact_mod_cast hT'T).trans hT1
  have hAP := Apriori.qvAPriori_ae μ d hc (psiI := aprPsiI d (p.n * p.W))
    (psiA := aprPsiA d (p.n * p.W)) (fun k _ => by linarith [(hpsi k).1])
    (fun k _ => by linarith [(hpsi k).2]) T'
  set Λ := aprLamM d (p.n * p.W)
  set ψI := aprPsiI d (p.n * p.W)
  set ψA := aprPsiA d (p.n * p.W)
  set BF := avConst d (fun _ => Λ) (eMI d (p.n * p.W) 2) 2 *
      phiAvF ψI ψA (P.lEta T) (yScale P T) 2 + 2 * vsCK d * ψA 1
  have hpsi0 : ∀ n, 0 ≤ ψI n ∧ 0 ≤ ψA n := fun n =>
    ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hLT := (hF.inputs T ⟨T.2, le_rfl⟩).lEta_pos
  have hBF : 0 ≤ BF := by
    have := avConst_nonneg d (by linarith) (MI.eMI_nonneg d hN 2) 2 (LamM := Λ)
    have := phiAvF_nonneg hpsi0 hLT.le (yScale_pos (MI.mi_atT d hb hPS hPW hPD hz hP6 T.2 hT1)).le
      2 (psiI := ψI) (psiA := ψA)
    have := (vsCK_pos d).le
    have := hAv 1
    positivity
  have hFB : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T',
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ tau p P ψI ψA x → ∀ y, vsHeight P.z s *
        ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingShort P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            BF * P.sAv y s :=
    Filter.Eventually.of_forall fun x => satFB_short d hb hPS hPW hPD hz hP6 hT1 hT'T σ hσ x
  -- the noise variance as a square
  have hηT' := vsHeight_pos hzi hT'1
  have hLT' := P.lEta_pos hN hW hzi hT'1
  set cR := onestepConst d * kernelActionConst d ^ 2
  have hcR : 0 < cR := by
    have := QV.qv_onestepConst_pos d; have := kernelActionConst_ge_one d; positivity
  set φq := qvPhiAv ψI ψA (0 + 1 + 1) (P.lEta T')
  have hφq : 0 < φq := qvPhiAv_pos hI hAv _ hLT'
  set I0 := intF d P 0 T'
  have hQI : 0 < qvC d * Λ ^ 3 * I0 := by
    have := MI.qvC_mul_intF_pos d P hPW hz hT'1 (γ := 0) le_rfl hLam
    exact this
  have hsu := P.sAv_pos hN hW hzi hT'1 u
  set Q := ((0 + 1 : ℕ) + 1 : ℝ) * Real.sqrt (qvC d * Λ ^ 3 * I0) * (φq * (cR / vsHeight P.z T')) *
    (P.lEta T' ^ (0 : ℝ) * P.sAv u T')
  have hQ : 0 < Q := by
    have := Real.sqrt_pos.mpr hQI
    have := Real.rpow_pos_of_pos hLT' (0 : ℝ)
    positivity
  have hAy : QV.qvMartGen d P ψI ψA Λ T' (cR / vsHeight P.z T') 0 u * QV.qvIntRule d P 0 T' =
      Q ^ 2 := by
    have h := MI.sq_noise (K := ((0 + 1 : ℕ) : ℝ) + 1) (Q := qvC d * Λ ^ 3)
      (φ := φq * (cR / vsHeight P.z T')) (Lp := P.lEta T' ^ (2 * 0)) (s := P.sAv u T')
      (y := QV.qvIntRule d P 0 T') (I := I0) (Lb := P.lEta T' ^ (0 : ℝ)) hQI.le
      (MI.lp_y d P hPW hz hT'1 (2 * 0) (by push_cast; ring))
    calc _ = (((0 + 1 : ℕ) : ℝ) + 1) ^ 2 * (qvC d * Λ ^ 3) * (φq * (cR / vsHeight P.z T')) ^ 2 *
          P.lEta T' ^ (2 * 0) * P.sAv u T' ^ 2 * QV.qvIntRule d P 0 T' := by
          unfold QV.qvMartGen; ring
      _ = Q ^ 2 := h
  set lam := 2 * r * Q
  have hlam : 0 ≤ lam := by positivity
  have hexp : lam ^ 2 / (4 * (QV.qvMartGen d P ψI ψA Λ T' (cR / vsHeight P.z T') 0 u *
      QV.qvIntRule d P 0 T')) = r ^ 2 := by
    rw [hAy]; simp only [lam]; field_simp; ring
  have h := linTerm_short μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T' hT'1 hAP hT'0 σ hσ u hBF
    hFB hlam
  rw [hexp] at h
  refine le_trans (measure_mono ?_) h
  intro x ⟨hτx, hbad⟩
  refine ⟨hτx, ?_⟩
  unfold slotBad at hbad
  rw [lossBeta_one_two.2, Real.rpow_zero, one_mul] at hbad
  have hI0T : I0 = intF d P 0 T := intF_time_indep d P hPW hz 0 hT1 hT'1
  have hy0 : QV.qvIntRule d P 0 T' = I0 := by
    simp only [I0, intF, Real.rpow_zero, one_mul]
  have hφqT : φq ≤ qvPhiAv ψI ψA 2 (P.lEta T) :=
    qvPhiAv_anti (fun j => (hpsi0 j).1) (fun j => (hpsi0 j).2) (k := 0 + 1 + 1) (by norm_num) hLT
      (hF.anti T' ⟨T'.2, by exact_mod_cast hT'T⟩)
  have hβ1 : P.lEta T' ^ lossBeta 1 = 1 := by rw [lossBeta_one_two.1, Real.rpow_zero]
  have hsq0 : 0 ≤ Real.sqrt (qvC d * Λ ^ 3 * I0) := Real.sqrt_nonneg _
  have hs0 := hsu.le
  have key : vsHeight P.z T' * (cR * BF / vsHeight P.z T' * QV.qvIntRule d P 0 T' *
      P.sAv u T' + vsCK d * ψA 1 * P.lEta T' ^ lossBeta 1 * P.sAv u T' / vsHeight P.z T' + lam) ≤
      bShort d P T r * P.sAv u T' := by
    have e1 : vsHeight P.z T' * (cR * BF / vsHeight P.z T' * QV.qvIntRule d P 0 T' *
        P.sAv u T' + vsCK d * ψA 1 * P.lEta T' ^ lossBeta 1 * P.sAv u T' / vsHeight P.z T' +
          lam) = cR * BF * I0 * P.sAv u T' + vsCK d * ψA 1 * P.sAv u T' +
        2 * r * (2 * Real.sqrt (qvC d * Λ ^ 3 * I0) * φq * cR) * P.sAv u T' := by
      rw [hy0, hβ1]
      simp only [lam, Q, Real.rpow_zero]
      push_cast
      field_simp
      ring
    rw [e1]
    unfold bShort
    rw [← hI0T]
    have h3 : 2 * r * (2 * Real.sqrt (qvC d * Λ ^ 3 * I0) * φq * cR) * P.sAv u T' ≤
        2 * r * (2 * Real.sqrt (qvC d * Λ ^ 3 * I0) * qvPhiAv ψI ψA 2 (P.lEta T) * cR) *
          P.sAv u T' := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hs0
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hφqT (by positivity))
        hcR.le
    have e2 : (cR * BF * I0 + vsCK d * ψA 1 +
        2 * r * (2 * Real.sqrt (qvC d * Λ ^ 3 * I0) * qvPhiAv ψI ψA 2 (P.lEta T) * cR)) *
          P.sAv u T' = cR * BF * I0 * P.sAv u T' + vsCK d * ψA 1 * P.sAv u T' +
        2 * r * (2 * Real.sqrt (qvC d * Λ ^ 3 * I0) * qvPhiAv ψI ψA 2 (P.lEta T) * cR) *
          P.sAv u T' := by ring
    rw [e2]
    linarith
  by_contra hlt
  push Not at hlt
  have := mul_lt_mul_of_pos_left hlt hηT'
  linarith

/-- **The saturated linear-term bound at one grid time, long chains (`k = n+4`, last slot), on the (LL) event at `T`.**
For `T' ≤ T ≤ 1`, saturated `σ`, `B₂, r ≥ 0`:
`P(T' ≤ τ, x ∈ circLLEvent σ τ B₂ T, bLong L_{T'}^{β_k} s^av_{T'}(u) <
η_{T'} |T̂^{(k)}_{T'}[𝒳_{T'}](u)|) ≤ 4 e^{-r²}`. -/
theorem satSlot_long {T : ℝ≥0} (hT1 : (T : ℝ) ≤ 1) {T' : ℝ≥0} (hT'T : T' ≤ T) {n : ℕ}
    (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ)
    (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {B₂ r : ℝ} (hB₂ : 0 ≤ B₂) (hr : 0 ≤ r) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T' : WithTop ℝ≥0) ≤
        tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) x ∧
        x ∈ circLLEvent P σ (tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W))) B₂ T ∧
        slotBad P σ u (bLong d P n B₂ T r) (Fin.last (n + 2 + 1)) T' x} ≤
      4 * ENNReal.ofReal (Real.exp (-r ^ 2)) := by
  have hN := MI.mi_N_pos p
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hpsi := MI.mi_psi_ge d p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  have hI : ∀ j, 1 ≤ aprPsiI d (p.n * p.W) j := fun j => (hpsi j).1
  have hAv : ∀ j, 0 ≤ aprPsiA d (p.n * p.W) j := fun j => by linarith [(hpsi j).2]
  have hτ := tau_isStoppingTime μ hN hW hzi hS (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W))
  have hT'T' : (T' : ℝ) ≤ T := by exact_mod_cast hT'T
  have hT'1 : (T' : ℝ) ≤ 1 := hT'T'.trans hT1
  have hAP := Apriori.qvAPriori_ae μ d hc (psiI := aprPsiI d (p.n * p.W))
    (psiA := aprPsiA d (p.n * p.W)) (fun k _ => by linarith [(hpsi k).1])
    (fun k _ => by linarith [(hpsi k).2]) T'
  set Λ := aprLamM d (p.n * p.W)
  set ψI := aprPsiI d (p.n * p.W)
  set ψA := aprPsiA d (p.n * p.W)
  set β := lossBeta (n + 4)
  have hpsi0 : ∀ n, 0 ≤ ψI n ∧ 0 ≤ ψA n := fun n =>
    ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hLT := (hF.inputs T ⟨T.2, le_rfl⟩).lEta_pos
  have he0 := MI.eMI_nonneg d hN (n + 4)
  have hC0 := avConst_nonneg d (by linarith) he0 (n + 4) (LamM := Λ)
  have hB₁ : 0 ≤ bOne d P n T := by
    unfold bOne
    have := phiAvF_nonneg hpsi0 hLT.le (yScale_pos (MI.mi_atT d hb hPS hPW hPD hz hP6 T.2 hT1)).le
      (n + 4) (psiI := ψI) (psiA := ψA)
    positivity
  -- the forcing hypothesis
  have hFf : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T',
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ tau p P ψI ψA x → ∀ y, vsHeight P.z s *
        ‖forcingAv P σ y s (pathH p x s)‖ ≤ bOne d P n T * P.lEta s ^ β * P.sAv y s := by
    refine Filter.Eventually.of_forall fun x s hs hsτ y => ?_
    have hs0 : 0 ≤ s := hs.1.le
    have hsT : s ≤ T := hs.2.trans hT'T'
    have hs1 : s ≤ 1 := hsT.trans hT1
    have hAPs : ∀ s'' ∈ Ioc (0 : ℝ) s, QV.APriori P ψI ψA Λ s'' (pathH p x s'') := by
      have h := MI.mi_ap_path d hb hPS hPW hPD hz hpsi s.toNNReal x hsτ
      rwa [Real.coe_toNNReal s hs0] at h
    have h := MI.forcingAv_le_T d hb hPS hPW hPD hz hP6 hs0 hs1 hpsi hLam (pathH p x) hAPs
      (k := n + 4) (by omega) hn he0
      (fun h2 _ s'' hs'' => Apriori.mbounds_extra_uncond hc hs''.1.le (hs''.2.trans hs1) h2)
      σ (s := s) ⟨hs.1, le_rfl⟩ y
    have hΦ := MI.phiAvF_anti hpsi0 hLT (hF.anti s ⟨hs0, hsT⟩)
      (MI.yScale_anti P hN hW hzi hsT hT1) (k := n + 4) hn
    have hn0 : 0 ≤ P.lEta s ^ β * P.sAv y s :=
      mul_nonneg (Real.rpow_nonneg (P.lEta_pos hN hW hzi hs1).le _)
        (P.sAv_pos hN hW hzi hs1 y).le
    have := mul_le_mul_of_nonneg_left hΦ (mul_nonneg hC0 hn0)
    unfold bOne
    calc _ ≤ _ := h
      _ ≤ _ := this
      _ = _ := by ring
  -- the (LL) event at `T` covers `T'`
  set E := circLLEvent P σ (tau p P ψI ψA) B₂ T
  have hLL : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, x ∈ E → ∀ s ∈ Ioc (0 : ℝ) T',
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ tau p P ψI ψA x → ∀ y, vsHeight P.z s ^ 2 *
        ‖circSlot ⟨n + 1, by omega⟩ (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
            (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
          B₂ * P.lEta s ^ β * P.sAv y s :=
    Filter.Eventually.of_forall fun x hx s hs hsτ y => hx s ⟨hs.1, hs.2.trans hT'T'⟩ hsτ y
  -- the noise variance as a square
  have hηT' := vsHeight_pos hzi hT'1
  have hLT' := P.lEta_pos hN hW hzi hT'1
  have hCP := kernelActionConst_ge_one d
  have hCK := vsCK_pos d
  have hCw : 0 < d.Cwc := lt_of_lt_of_le zero_lt_one d.one_le_Cwc
  set cW := vsCK d * d.Cwc * kernelActionConst d ^ (n + 4)
  have hcW : 0 < cW := by positivity
  set Bc := vsCK d * (d.Cwc / vsHeight P.z T') * kernelActionConst d ^ (n + 4)
  have hBc : vsHeight P.z T' * Bc = cW := by
    simp only [Bc, cW]; field_simp
  set φq := qvPhiAv ψI ψA (n + 2 + 1 + 1) (P.lEta T')
  have hφq : 0 < φq := qvPhiAv_pos hI hAv _ hLT'
  have hγM : 0 ≤ 2 - 2 * β := by linarith [qv_beta_le_one (k := n + 4) hn]
  set I2 := intF d P (2 - 2 * β) T'
  have hQI : 0 < qvC d * Λ ^ 3 * I2 := MI.qvC_mul_intF_pos d P hPW hz hT'1 hγM hLam
  have hsu := P.sAv_pos hN hW hzi hT'1 u
  set K : ℝ := ((n + 2 + 1 : ℕ) : ℝ) + 1
  have hK : K = (n : ℝ) + 4 := by simp only [K]; push_cast; ring
  set Q := K * Real.sqrt (qvC d * Λ ^ 3 * I2) * (φq * Bc) * (P.lEta T' ^ β * P.sAv u T')
  have hBc0 : 0 < Bc := by simp only [Bc]; positivity
  have hQ : 0 < Q := by
    have := Real.sqrt_pos.mpr hQI
    have := Real.rpow_pos_of_pos hLT' β
    have : 0 < K := by rw [hK]; positivity
    positivity
  have hAy : QV.qvMartGen d P ψI ψA Λ T' Bc 1 u * QV.qvIntRule d P (2 - 2 * β) T' = Q ^ 2 := by
    have h := MI.sq_noise (K := K) (Q := qvC d * Λ ^ 3) (φ := φq * Bc)
      (Lp := P.lEta T' ^ (2 * 1)) (s := P.sAv u T') (y := QV.qvIntRule d P (2 - 2 * β) T')
      (I := I2) (Lb := P.lEta T' ^ β) hQI.le
      (MI.lp_y d P hPW hz hT'1 (2 * 1) (by push_cast; ring))
    calc _ = K ^ 2 * (qvC d * Λ ^ 3) * (φq * Bc) ^ 2 * P.lEta T' ^ (2 * 1) * P.sAv u T' ^ 2 *
          QV.qvIntRule d P (2 - 2 * β) T' := by
          unfold QV.qvMartGen; ring
      _ = Q ^ 2 := h
  set lam := 2 * r * Q
  have hlam : 0 ≤ lam := by positivity
  have hexp : lam ^ 2 / (4 * (QV.qvMartGen d P ψI ψA Λ T' Bc 1 u *
      QV.qvIntRule d P (2 - 2 * β) T')) = r ^ 2 := by
    rw [hAy]; simp only [lam]; field_simp; ring
  have h := linTerm_long_event μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T' hT'1 hAP hn σ hσ u
    hB₁ hB₂ hFf E hLL hlam
  rw [hexp] at h
  refine le_trans (measure_mono ?_) h
  intro x ⟨hτx, hxE, hbad⟩
  refine ⟨hτx, hxE, ?_⟩
  unfold slotBad at hbad
  have hI1 : intF d P (1 - β) T' = intF d P (1 - β) T := intF_time_indep d P hPW hz _ hT1 hT'1
  have hI2 : I2 = intF d P (2 - 2 * β) T := intF_time_indep d P hPW hz _ hT1 hT'1
  have hLy : P.lEta T' * QV.qvIntRule d P (1 - β) T' = P.lEta T' ^ β * intF d P (1 - β) T' := by
    unfold intF
    rw [← mul_assoc, ← Real.rpow_add hLT', show β + (1 - β) = 1 by ring, Real.rpow_one]
  have hφqT : φq ≤ qvPhiAv ψI ψA (n + 4) (P.lEta T) :=
    qvPhiAv_anti (fun j => (hpsi0 j).1) (fun j => (hpsi0 j).2) (k := n + 2 + 1 + 1) (by omega) hLT
      (hF.anti T' ⟨T'.2, hT'T'⟩)
  have hsq0 : 0 ≤ Real.sqrt (qvC d * Λ ^ 3 * I2) := Real.sqrt_nonneg _
  have hnrm : 0 ≤ P.lEta T' ^ β * P.sAv u T' :=
    mul_nonneg (Real.rpow_nonneg hLT'.le _) hsu.le
  set cc := vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * bOne d P n T +
    kernelActionConst d ^ (n + 4) * kernelActionConst d * B₂
  have key : vsHeight P.z T' * (cc / vsHeight P.z T' * P.lEta T' *
      QV.qvIntRule d P (1 - β) T' * P.sAv u T' + lam) ≤
      bLong d P n B₂ T r * (P.lEta T' ^ β * P.sAv u T') := by
    have e1 : vsHeight P.z T' * (cc / vsHeight P.z T' * P.lEta T' *
        QV.qvIntRule d P (1 - β) T' * P.sAv u T' + lam) =
        cc * intF d P (1 - β) T' * (P.lEta T' ^ β * P.sAv u T') +
          2 * r * (K * Real.sqrt (qvC d * Λ ^ 3 * I2) * φq * cW) *
            (P.lEta T' ^ β * P.sAv u T') := by
      have e2 : cc / vsHeight P.z T' * P.lEta T' * QV.qvIntRule d P (1 - β) T' * P.sAv u T' =
          cc / vsHeight P.z T' * (P.lEta T' * QV.qvIntRule d P (1 - β) T') * P.sAv u T' := by
        ring
      rw [e2, hLy, ← hBc]
      simp only [lam, Q]
      field_simp
    rw [e1]
    unfold bLong
    rw [← hI1, ← hI2, ← hK]
    have h3 : 2 * r * (K * Real.sqrt (qvC d * Λ ^ 3 * I2) * φq * cW) *
        (P.lEta T' ^ β * P.sAv u T') ≤
        2 * r * (K * Real.sqrt (qvC d * Λ ^ 3 * I2) * qvPhiAv ψI ψA (n + 4) (P.lEta T) * cW) *
          (P.lEta T' ^ β * P.sAv u T') := by
      have hK0 : 0 ≤ K := by rw [hK]; positivity
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hnrm
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hφqT (by positivity)) hcW.le
    have e3 : (cc * intF d P (1 - β) T' +
        2 * r * (K * Real.sqrt (qvC d * Λ ^ 3 * I2) * qvPhiAv ψI ψA (n + 4) (P.lEta T) * cW)) *
          (P.lEta T' ^ β * P.sAv u T') = cc * intF d P (1 - β) T' * (P.lEta T' ^ β * P.sAv u T') +
        2 * r * (K * Real.sqrt (qvC d * Λ ^ 3 * I2) * qvPhiAv ψI ψA (n + 4) (P.lEta T) * cW) *
          (P.lEta T' ^ β * P.sAv u T') := by ring
    rw [e3]
    linarith
  by_contra hlt
  push Not at hlt
  have := mul_lt_mul_of_pos_left hlt hηT'
  linarith

end Fixed

end BlockBand.Native.ErdosRiabov.SatLin
