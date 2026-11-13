module

public import BlockBand.Native.ErdosRiabov.Circ.BoundBase

/-!
# The regularized bound and the linear term for short chains

Tail bounds of the regularized chain `Θ̊^{(2)}_T[𝒳_T]` and of the linear term for short chains
`k = 2`.

Setting of the martingale estimates (`μ`, VS data `d`, `P.S = shortRingProfile p.b p.n p.W`,
`d.b = p.b`,
`P.W = p.W`, `P.D = d.D`, `P.z ∈ 𝒟`, the parameter bounds, thresholds `ψ^I ≥ 1`, `ψ^A ≥ 0`,
`Λ_M ≥ 1`, a
`driverAugmented` stopping time `τ`, a final time `T ≤ 1`, and `QV.APriori` a.s. on
`(0, T] ∩ [0, τ]`).
The ring is `Θ̊^{(2)}_T = ringOp … T (Fin.last 1) ⟨0⟩`; `η_s = vsHeight P.z s`, `L_s = P.lEta s`,
`C_reg C_P² = onestepConst d · kernelActionConst d ²`, `Λ_0(T) = QV.qvIntRule d P 0 T`
(`c_m⁻¹ log((C₀+1)N)`, the first integration rule).

* `circ_integrand_short` (deterministic, one time `s`, from `Discharge.forcing_av_uncond` and
  `Discharge.extraForcing_two_uncond`):
  `η_s |(𝓕^av_s + F̃_s)(x)| ≤ B_s L_s^{β_2} s^av_{2,s}(x)`,
  `B_s = avConst · Φ^{av,f}_2(ψ, L_s, Y_s) + 2 C_K ψ^A_1`.
* **`circBound_short`**: if a.s. `η_s |(𝓕^av_s + F̃_s)(x)| ≤ B s^av_{2,s}(x)` for `s ≤ τ`,
  `s ∈ (0, T]`, then for `λ ≥ 0`
  `P(T ≤ τ, C_reg C_P² B η_T⁻¹ Λ_0(T) s^av_{2,T}(u) + λ ≤ |Θ̊^{(2)}_T[𝒳_T](u)|)`
  `≤ 4 exp(-λ²/(4 A y))`
  with `A y` of `QV.martingaleEstimate_oneRing`. This is the regularized bound of Erdős–Riabov at
  the fixed time `T`: `η_T|𝒵_T| ≤ s^av_T (C_reg C_P² B Λ_0 + η_T λ)`.
* `circ_remainder_short` (the remainder bound, deterministic): under `QV.APriori` at time `t`,
  `η_t |T̂_t(x_1, x_0) 𝒯_2[𝒳^2](x')| ≤ C_K ψ^A_1 L_t^{β_1} s^av_{2,t}(x)`.
* **`linTerm_short`** (`k = 2`, `0 < T`): the same tail bound for the linear term
  `T̂^{(2)}_T[𝒳_T](u)` with the extra deterministic term `C_K ψ^A_1 L_T^{β_1} s^av_{2,T}(u)/η_T`.
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

/-!
### The deterministic integrand
-/

/-- **The Duhamel integrand of short chains at one time.** For `s ∈ [0,1]`, the forcing
context `FCtx d P s`, (AP) `Forcing.APriori P s H ψ^I ψ^A` with `ψ ≥ 1`, (MI) `IsoBAt`,
(ME) `ExtraBAt` at `k = 2` and Hermitian `H`:
`η_s |(𝓕^av_s + F̃_s)(x)| ≤ (avConst · Φ^{av,f}_2 + 2 C_K ψ^A_1) L_s^{β_2} s^av_{2,s}(x)`.
-/
theorem circ_integrand_short (d : VSData) (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
    (hPD : P.D = d.D) (hPS : P.S = shortRingProfile d.b p.n p.W)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (c : Forcing.FCtx d P s) {H : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ}
    (hH : H.IsHermitian) {psiI psiA : ℕ → ℝ} (hAP : Forcing.APriori P s H psiI psiA)
    (hpsi1 : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) {I : ℕ → ℝ}
    (hI : ∀ n ∈ kRange, Forcing.IsoBAt P s n (I n)) (hI0 : ∀ n, 0 ≤ I n) {e : ℝ}
    (he0 : 0 ≤ e) (hE : Forcing.ExtraBAt P s 2 e) (σ : Fin 2 → Bool) (hσ : ¬ HasDesatFactor σ)
    (x : Fin 2 → Fin (p.n * p.W)) :
    vsHeight P.z s * ‖((fun y => forcingAv P σ y s H) +
        extraForcingShort (n := 0) P.S P.z s (fun y => P.avErr σ y s H)) x‖ ≤
      (Forcing.avConst d I e 2 * Forcing.phiAvF psiI psiA (P.lEta s) (Forcing.yScale P s) 2 +
        2 * vsCK d * psiA 1) * P.lEta s ^ Expo.lossBeta 2 * P.sAv x s := by
  have hF := Discharge.forcing_av_uncond c hAP hpsi1 hI hI0 he0 (fun _ _ => hE) (by norm_num)
    (by norm_num) σ x
  have hX := Discharge.extraForcing_two_uncond d p.n_ge_four p.W_pos P hPW hPD hPS hz σ hσ hs hH x
  have hβ : Expo.lossBeta 1 = Expo.lossBeta 2 := by
    rw [Forcing.lossBeta_eq (by norm_num), Forcing.lossBeta_eq (by norm_num),
      Forcing.lossAlpha_eq_zero (by norm_num), Forcing.lossAlpha_eq_zero (by norm_num)]
  have hΨ : P.bigPsiAv 1 s H ≤ psiA 1 := (hAP 1 (Finset.mem_Icc.mpr ⟨le_rfl, by norm_num [vsK]⟩)).2
  have hL := c.lEta_pos
  have hs0 := (Forcing.sAv_pos c x).le
  have hLb : 0 ≤ P.lEta s ^ Expo.lossBeta 2 := Real.rpow_nonneg hL.le _
  have hCK := (vsCK_pos d).le
  rw [hβ] at hX
  have hX' : vsHeight P.z s * ‖extraForcingShort (n := 0) P.S P.z s (fun y => P.avErr σ y s H) x‖
      ≤ 2 * vsCK d * psiA 1 * P.lEta s ^ Expo.lossBeta 2 * P.sAv x s := by
    refine hX.trans ?_
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΨ (by positivity : (0 : ℝ) ≤
      2 * vsCK d)) (mul_nonneg hLb hs0)
    nlinarith [this]
  have hη := c.height_pos
  calc vsHeight P.z s * ‖((fun y => forcingAv P σ y s H) +
        extraForcingShort (n := 0) P.S P.z s (fun y => P.avErr σ y s H)) x‖
      ≤ vsHeight P.z s * ‖forcingAv P σ x s H‖ + vsHeight P.z s *
          ‖extraForcingShort (n := 0) P.S P.z s (fun y => P.avErr σ y s H) x‖ := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hη.le
    _ ≤ _ := by
        have := hF
        nlinarith [hF, hX']

/-!
### The regularized bound
-/

theorem circ_toNNReal_le {s : ℝ} {T' : ℝ≥0} (hs : s ≤ T') {w : WithTop ℝ≥0}
    (h : (T' : WithTop ℝ≥0) ≤ w) : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ w :=
  (WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hs)).trans h

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

/-- If a.s., for `s ∈ (0, T]` with `s ≤ τ` and all `y`, `η_s |(𝓕^av_s + F̃_s)(y)| ≤ B s^av_{2,s}(y)`
(`B ≥ 0`; e.g.
`B ≥ sup_s B_s` of `circ_integrand_short`), then for `λ ≥ 0`:
`P(T ≤ τ, C_reg C_P² B η_T⁻¹ Λ_0(T) s^av_{2,T}(u) + λ ≤ |Θ̊^{(2)}_T[𝒳_T](u)|) ≤ 4 exp(-λ²/(4 A y))`,
`A y` as in `QV.martingaleEstimate_oneRing`.
-/
theorem circBound_short (σ : Fin (0 + 2) → Bool) (hσ : ¬ HasDesatFactor σ)
    (u : Fin (0 + 2) → Fin (p.n * p.W)) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingShort P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            B * P.sAv y s)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧
        onestepConst d * kernelActionConst d ^ 2 * B / vsHeight P.z T * QV.qvIntRule d P 0 T *
          P.sAv u T + lam ≤
        ‖ringOp P.S P.z T (Fin.last (0 + 1)) ⟨0, by omega⟩
          (fun y => P.avErr σ y T (pathH p x T)) u‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (QV.qvMartGen d P psiI psiA LamM T
        (onestepConst d * kernelActionConst d ^ 2 / vsHeight P.z T) 0 u *
          QV.qvIntRule d P 0 T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hzi := hz.im_pos hN
  have hPS' : P.S = shortRingProfile d.b p.n p.W := evol_PS_eq d P hb hPS
  refine le_trans (measure_mono_ae ?_)
    (QV.martingaleEstimate_oneRing μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP σ u hlam)
  filter_upwards [Discharge.circEvol_short_combMg_uncond μ hzi hPS σ hσ, hFB] with x h1 h2
  intro hx
  obtain ⟨hτx, hge⟩ := hx
  refine ⟨T, le_rfl, hτx, ?_⟩
  have hid := h1 T hT1 u
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      K = onestepConst d * kernelActionConst d ^ (0 + 2) / vsHeight P.z T * P.sAv u T := ⟨_, rfl⟩
  have hηT := vsHeight_pos hzi hT1
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := QV.qv_onestepConst_pos d
    have := kernelActionConst_ge_one d
    have := (QV.qv_sAv_pos P (QV.qv_ups_pos d hPW hz hT1)
      (P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hzi hT1) u).le
    positivity
  have hint : ‖(∫ s in (0 : ℝ)..T, propOp (goodProp P.S P.z (fun _ => .sat) s T)
      (ringOp P.S P.z T (Fin.last (0 + 1)) ⟨0, by omega⟩
        ((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingShort P.S P.z s (fun y => P.avErr σ y s (pathH p x s))))) u‖ ≤
      ∫ s in (0 : ℝ)..T, K * (B * P.lEta s ^ (-(0 : ℝ)) * (vsHeight P.z s)⁻¹) := by
    refine circ_norm_integral_apply_le _ u (NNReal.coe_nonneg T)
      ((circ_rate_intervalIntegrable d P hPW hz 0 B (NNReal.coe_nonneg T) hT1).const_mul K)
      (fun s hs => ?_)
      (fun s hs => ?_)
    · have := vsHeight_pos hzi (hs.2.trans hT1)
      have := Real.rpow_nonneg (P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hzi
        (hs.2.trans hT1)).le (-(0 : ℝ))
      positivity
    · have hs1 : s ≤ 1 := hs.2.trans hT1
      have hηs := vsHeight_pos hzi hs1
      have hf : ∀ y, ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingShort P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            B / vsHeight P.z s * P.sAv y s := by
        intro y
        have h := h2 s hs (circ_toNNReal_le hs.2 hτx) y
        rw [div_mul_eq_mul_div, le_div_iff₀ hηs]
        linarith
      have hreg := regProps_oneRing_apply d p.n_ge_four p.W_pos P hPW hPD hz hs.1.le hs.2 hT1
        (n := 0) (div_nonneg hB hηs.le) _ hf u
      rw [← hPS'] at hreg
      refine hreg.trans (le_of_eq ?_)
      rw [neg_zero, Real.rpow_zero, hK]
      ring
  have hrule := circ_intRule d P hPW hz (γ := 0) (A := B) le_rfl hB (NNReal.coe_nonneg T) hT1
  rw [intervalIntegral.integral_const_mul] at hint
  have hint' := hint.trans (mul_le_mul_of_nonneg_left hrule hK0)
  have htri : ‖ringOp P.S P.z T (Fin.last (0 + 1)) ⟨0, by omega⟩
      (fun y => P.avErr σ y T (pathH p x T)) u‖ ≤ K * (B * QV.qvIntRule d P 0 T) +
        ‖combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
          (fun α s => ((goodProp P.S P.z (fun _ => .sat) s T * circShortMat P.S P.z T :
            Matrix (Sites p (0 + 2)) (Sites p (0 + 2)) ℂ)) u α) T x‖ := by
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add hint' le_rfl)
  have hKe : onestepConst d * kernelActionConst d ^ 2 * B / vsHeight P.z T *
      QV.qvIntRule d P 0 T * P.sAv u T = K * (B * QV.qvIntRule d P 0 T) := by
    rw [hK]; ring
  rw [hKe] at hge
  linarith

end Bound

/-!
### The short remainder
-/

/-- **The remainder of the short linear term.** For a saturated `σ` of length `2`, `t ∈ [0,1]`,
Hermitian `H` and the a priori bound `|𝒳^1_t| ≤ ψ L_t^{β_1} s^av_{1,t}` for every pattern of length
`1`: `η_t |T̂_t(x_1, x_0) 𝒯_2[𝒳^2_t](x')| ≤ C_K ψ L_t^{β_1} s^av_{2,t}(x)`.
-/
theorem circ_remainder_short (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W)
    (P : PsiData (m * W)) (hPW : P.W = W) (hPD : P.D = d.D)
    (hPS : P.S = shortRingProfile d.b m W) (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
    (σ : Fin 2 → Bool) (hσ : ¬ HasDesatFactor σ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian) {ψ : ℝ}
    (hA1 : ∀ (τ' : Fin 1 → Bool) (w : Fin 1 → Fin (m * W)),
      ‖P.avErr τ' w t H‖ ≤ ψ * P.lEta t ^ Expo.lossBeta 1 * P.sAv w t)
    (x : Fin 2 → Fin (m * W)) :
    vsHeight P.z t * ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t (x 1) (x 0) *
        ∑ b, P.avErr σ (update x (Fin.last 1) b) t H‖ ≤
      vsCK d * ψ * P.lEta t ^ Expo.lossBeta 1 * P.sAv x t := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hin := Contr.contrVSInputs_of d hm hW P hPW hPD hz ht.1 ht.2
  have hS : StochasticSymm P.S := hPS ▸ shortRingProfile_stochasticSymm d.b_pos d.b_lt_half
    (by omega : 3 ≤ m) hW
  have hzi : 0 < P.z.im := hz.im_pos hN
  have hη := hin.height_pos
  have hL := hin.lEta_pos
  have hσ' := circ_last_ne_zero σ hσ
  have hT := Discharge.wardReduction_norm_uncond P hS hzi σ hσ' x ht hH
  have h1 := hA1 (wardPatLast σ) (wardSites x)
  have h2 := hA1 (wardPatHead σ) (wardSites x)
  rw [circ_sAv_one] at h1 h2
  have hK : ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t (x 1) (x 0)‖ ≤
      vsCK d * P.ups t (x 0) (x 1) := by
    have h := (lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos d.C0_ge_one
      d.D_ge_six hm hW hz ht.1 ht.2).1 (x 1) (x 0)
    rw [hPS, ← hin.symm]
    simpa only [PsiData.ups, hPW, hPD, vsCK] using h
  have hsAv : P.sAv x t = (P.lEta t)⁻¹ * P.ups t (x 0) (x 1) := by
    have h01 : finRotate 2 0 = 1 := by decide
    have h10 : finRotate 2 1 = 0 := by decide
    simp only [PsiData.sAv, show (2 : ℕ) ≠ 1 by norm_num, ite_false, Fin.prod_univ_two, h01, h10]
    rw [hin.symm (x 1) (x 0), Real.sqrt_mul_self (hin.nonneg _ _)]
    norm_num [Real.rpow_neg_one]
  have hU := hin.nonneg (x 0) (x 1)
  have hCK := vsCK_pos d
  have hψ : 0 ≤ ψ * P.lEta t ^ Expo.lossBeta 1 * (P.lEta t)⁻¹ :=
    (norm_nonneg _).trans h1
  rw [norm_mul, hsAv]
  calc vsHeight P.z t * (‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t (x 1) (x 0)‖ *
        ‖∑ b, P.avErr σ (update x (Fin.last 1) b) t H‖)
      ≤ vsHeight P.z t * (vsCK d * P.ups t (x 0) (x 1) * ((2 * vsHeight P.z t)⁻¹ *
          (2 * (ψ * P.lEta t ^ Expo.lossBeta 1 * (P.lEta t)⁻¹)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hK (hT.trans ?_) (norm_nonneg _)
          (by positivity)) hη.le
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by field_simp

/-!
### The short linear term (`k = 2`)
-/

section Lin

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

/-- **The linear term for `k = 2`** (short chains: `T̂^{(2)}[𝒳] = 𝒵 + 𝓡`, with `𝒵` the
circular term and `𝓡` the remainder). Under the hypotheses of `circBound_short` and `0 < T`:
`P(T ≤ τ, D + C_K ψ^A_1 L_T^{β_1} s^av_{2,T}(u)/η_T + λ ≤ |T̂^{(2)}_T[𝒳_T](u)|)
≤ 4 exp(-λ²/(4 A y))`, `D = C_reg C_P² B η_T⁻¹ Λ_0(T) s^av_{2,T}(u)`.
-/
theorem linTerm_short (hT0 : 0 < (T : ℝ)) (σ : Fin (0 + 2) → Bool) (hσ : ¬ HasDesatFactor σ)
    (u : Fin (0 + 2) → Fin (p.n * p.W)) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingShort P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            B * P.sAv y s)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧
        onestepConst d * kernelActionConst d ^ 2 * B / vsHeight P.z T * QV.qvIntRule d P 0 T *
          P.sAv u T + vsCK d * psiA 1 * P.lEta T ^ Expo.lossBeta 1 * P.sAv u T / vsHeight P.z T +
            lam ≤
        ‖circSlot (Fin.last (0 + 1)) (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) T)
          (fun y => P.avErr σ y T (pathH p x T)) u‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (QV.qvMartGen d P psiI psiA LamM T
        (onestepConst d * kernelActionConst d ^ 2 / vsHeight P.z T) 0 u *
          QV.qvIntRule d P 0 T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hzi := hz.im_pos hN
  have hPS' : P.S = shortRingProfile d.b p.n p.W := evol_PS_eq d P hb hPS
  refine le_trans (measure_mono_ae ?_)
    (circBound_short μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP σ hσ u hB hFB hlam)
  filter_upwards [hAP] with x hA
  intro hx
  obtain ⟨hτx, hge⟩ := hx
  refine ⟨hτx, ?_⟩
  have hAT := hA T ⟨hT0, le_rfl⟩ (by rw [Real.toNNReal_coe]; exact hτx)
  have hne : (⟨0, by omega⟩ : Fin (0 + 2)) ≠ Fin.last (0 + 1) := by
    intro e; have := congrArg Fin.val e; simp at this
  have hdec := congrFun (circSlot_eq_ringOp_add P.S P.z T hne
    (fun y => P.avErr σ y T (pathH p x T))) u
  have hH : (pathH p x T).IsHermitian := vsBandFin_isHermitian _ _
  have hR : vsHeight P.z T * ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) T
      (u (Fin.last (0 + 1))) (u ⟨0, by omega⟩) *
        ∑ b, P.avErr σ (update u (Fin.last (0 + 1)) b) T (pathH p x T)‖ ≤
      vsCK d * psiA 1 * P.lEta T ^ Expo.lossBeta 1 * P.sAv u T :=
    circ_remainder_short d p.n_ge_four p.W_pos P hPW hPD hPS' hz σ hσ
      ⟨NNReal.coe_nonneg T, hT1⟩ hH (ψ := psiA 1)
      (fun τ' w => hAT.av 1 le_rfl (by norm_num) τ' w) u
  have hηT := vsHeight_pos hzi hT1
  have hR' : ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) T
      (u (Fin.last (0 + 1))) (u ⟨0, by omega⟩) *
        ∑ b, P.avErr σ (update u (Fin.last (0 + 1)) b) T (pathH p x T)‖ ≤
      vsCK d * psiA 1 * P.lEta T ^ Expo.lossBeta 1 * P.sAv u T / vsHeight P.z T := by
    rw [le_div_iff₀ hηT]
    linarith
  rw [hdec, Pi.add_apply] at hge
  have htri := norm_add_le (ringOp P.S P.z T (Fin.last (0 + 1)) ⟨0, by omega⟩
    (fun y => P.avErr σ y T (pathH p x T)) u)
    (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) T
      (u (Fin.last (0 + 1))) (u ⟨0, by omega⟩) *
        ∑ b, P.avErr σ (update u (Fin.last (0 + 1)) b) T (pathH p x T))
  linarith

end Lin

end BlockBand.Native.ErdosRiabov.Circ
