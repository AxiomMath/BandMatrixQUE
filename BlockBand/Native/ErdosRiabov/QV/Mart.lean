module

public import BlockBand.Native.ErdosRiabov.QV.Tail
public import BlockBand.Native.ErdosRiabov.Prop.RegProps
public import BlockBand.Native.ErdosRiabov.Circ.LongLinear

/-!
# The martingale estimates

Exponential tail bounds for the propagated martingale parts of the chain fluctuations, in the
families M1–M7 below.

* M1 `martingaleEstimate_av` (non-saturated averaged chains, `k = n + 2 ≤ 8`, coefficient
  `U(s,T)(u,α)` of `Evol.duhamel_av`; `evol_goodProps_av`): `γ = 2 - 2β_k`, `A = qvMartAv`;
* M2 `martingaleEstimate_iso` (isotropic, `k = n + 2 ≤ 8`, `Evol.duhamel_iso`;
  `evol_goodProps_iso`): `γ = 1 - 2α_k`, `A = qvMartIso`; conditional on
  `Split.ExplicitShortStatement`;
* M3 `martingaleEstimate_iso_one` (isotropic `k = 1`, `U = I`): `γ = 0`, `A = qvMartIsoOne`;
* M4 `martingaleEstimate_sat` (averaged, `U = I`, coefficient `δ_{αu}` of
  `Circ.duhamel_av_sat_combMg`): `γ = k - 2β_k`, `A = qvMartSat`;
* M5 `martingaleEstimate_oneRing` (`k = 2`, coefficient `P̂^{⊗2}_{s,T} Θ̊^{(2)}_T` of
  `Circ.circEvol_short_combMg`; `regProps_oneRing`): `γ = 0`;
* M6 `martingaleEstimate_twoRings` (`k = n + 4 ≤ 8`, `Circ.circEvol_long_combMg`;
  `regProps_twoRings`): `γ = 2 - 2β_k`;
* M7 `martingaleEstimate_longLinear` (`k = n + 4 ≤ 8`, `Circ.linTerm_evol_combMg`): `γ = 2 - 2β_k`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.QV

open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.CEH.Flow
open Expo (lossAlpha lossBeta)
open scoped NNReal ENNReal ComplexConjugate

variable {p : BlockBand.Parameters}

/-- The deterministic inputs of the martingale estimates along the flow on `[0, T]`: the single-time
contraction inputs,
`L_s ≥ 1`, `L_T ≤ L_s`, `Υ_s ≤ Υ_T`, and (K1) for the stability operator. -/
structure QVFlow (d : VSData) (P : PsiData (p.n * p.W)) (T : ℝ) : Prop where
  inputs : ∀ s ∈ Icc (0 : ℝ) T, QVInputs d P s
  one_le : ∀ s ∈ Icc (0 : ℝ) T, 1 ≤ P.lEta s
  anti : ∀ s ∈ Icc (0 : ℝ) T, P.lEta T ≤ P.lEta s
  upsMono : ∀ s ∈ Icc (0 : ℝ) T, ∀ x y, P.ups s x y ≤ P.ups T x y
  stab : ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    ‖Split.stabOp s P.S (semicircleM P.z * conj (semicircleM P.z)) x y‖ ≤
      (if x = y then 1 else 0) + vsCK d * P.ups s x y

/-- **`QVFlow` from VS data** (`qvInputs_of`, `vsScales`, `LemmaK.ups_U2_U8_vs`,
`qv_stabOp_le`), under the size hypothesis `N^{1+ζ₀} ≤ W²`.
-/
theorem qvFlow_of (d : VSData) {P : PsiData (p.n * p.W)} (hb : d.b = p.b)
    (hPS : P.S = shortRingProfile p.b p.n p.W) (hPW : P.W = p.W) (hPD : P.D = d.D)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
    (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2) {T : ℝ} (hT1 : T ≤ 1) :
    QVFlow d P T := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hWN : p.W ≤ p.n * p.W := Nat.le_mul_of_pos_left _ (by have := p.n_ge_four; omega)
  have hPS' : P.S = shortRingProfile d.b p.n p.W := by rw [hPS, hb]
  have hsc := fun {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) =>
    vsScales (N := p.n * p.W) (W := p.W) hN hWN d.kappa_pos (by linarith [d.C0_ge_one])
      d.delta0_lt_zeta0.le hP6 hz hs0 hst ht1
  have hL : ∀ s, P.lEta s = localizationLength (p.n * p.W) p.W (vsHeight P.z s) *
      vsHeight P.z s := fun s => by unfold PsiData.lEta; rw [hPW]
  refine ⟨fun s hs => qvInputs_of d p.n_ge_four p.W_pos P hPW hPD hPS' hz hs.1 (hs.2.trans hT1),
    fun s hs => ?_, fun s hs => ?_, fun s hs x y => ?_, fun s hs x y =>
      qv_stabOp_le d p.n_ge_four p.W_pos P hPW hPD hPS' hz hs.1 (hs.2.trans hT1) x y⟩
  · have h := (hsc hs.1 le_rfl (hs.2.trans hT1)).2.2.1
    rw [hL]
    refine le_trans ?_ h
    exact Real.one_le_rpow (by exact_mod_cast hN) d.delta0_pos.le
  · have h := (hsc hs.1 hs.2 hT1).2.1
    rw [hL, hL]
    exact h
  · have h := (LemmaK.ups_U2_U8_vs d p.n_ge_four p.W_pos hz hs.1 hs.2 hT1).2.2.2.2.1 x y
    unfold PsiData.ups
    rw [hPW, hPD]
    exact h

/-!
## Scalar helpers
-/

theorem qv_rate_shift {L LT A : ℝ} (hL : 0 < L) (a : ℝ) (k : ℕ) :
    A * L ^ a * (LT / L) ^ k = A * LT ^ k * L ^ (-((k : ℝ) - a)) := by
  rw [div_pow, Real.rpow_neg hL.le, Real.rpow_sub hL, Real.rpow_natCast]
  field_simp

theorem qvPhiAv_nonneg {psiI psiA : ℕ → ℝ} (hI : ∀ j, 0 ≤ psiI j) (k : ℕ) (L : ℝ) :
    0 ≤ qvPhiAv psiI psiA k L := by
  unfold qvPhiAv
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact hI _
  · exact mul_nonneg (hI 5) (Real.sqrt_nonneg _)

theorem qvPhiIso_nonneg {psiI psiA : ℕ → ℝ} (hI : ∀ j, 0 ≤ psiI j) (k : ℕ) {L : ℝ}
    (hL : 0 < L) : 0 ≤ qvPhiIso psiI psiA k L := by
  unfold qvPhiIso
  have h1 : 0 ≤ psiI k * Real.sqrt (psiI 2) * L ^ (-(1 / 4 : ℝ)) := by
    have := Real.rpow_nonneg hL.le (-(1 / 4 : ℝ)); have := hI k; positivity
  have h2 := Finset.sum_nonneg fun j (_ : j ∈ Finset.Icc 2 ((k + 1) / 2)) =>
    qvPhiMid_nonneg hI k j hL
  have h3 := qvPhiTilde_nonneg (psiA := psiA) hI k L
  linarith

/-- `qvBndAv` at `s` is at most its value with `φ(L_T)` (antitone `φ`, `L_T ≤ L_s`). -/
theorem qvBndAv_le {d : VSData} {P : PsiData (p.n * p.W)} {psiI psiA : ℕ → ℝ} {LamM s T : ℝ}
    (hI : ∀ j, 0 ≤ psiI j) (hA : ∀ j, 0 ≤ psiA j) (hLam : 1 ≤ LamM) (hη : 0 < vsHeight P.z s)
    (hLT : 0 < P.lEta T) (hTs : P.lEta T ≤ P.lEta s) (k : ℕ) :
    qvBndAv d P psiI psiA LamM s k ≤ qvC d * LamM ^ 3 * qvPhiAv psiI psiA k (P.lEta T) ^ 2 *
      P.lEta s ^ (2 * lossBeta k) / vsHeight P.z s := by
  unfold qvBndAv
  have h := qvPhiAv_anti (k := k) hI hA hLT hTs
  have h0 := qvPhiAv_nonneg (psiA := psiA) hI k (P.lEta s)
  have hsq := pow_le_pow_left₀ h0 h 2
  have hc := (qvC_pos d).le
  have hr := Real.rpow_nonneg (hLT.trans_le hTs).le (2 * lossBeta k)
  gcongr

theorem qvBndIso_le {d : VSData} {P : PsiData (p.n * p.W)} {psiI psiA : ℕ → ℝ} {LamM s T : ℝ}
    (hI : ∀ j, 0 ≤ psiI j) (hA : ∀ j, 0 ≤ psiA j) (hLam : 1 ≤ LamM) (hη : 0 < vsHeight P.z s)
    (hLT : 0 < P.lEta T) (hTs : P.lEta T ≤ P.lEta s) {k : ℕ} (hk : k ≤ 8) :
    qvBndIso d P psiI psiA LamM s k ≤ qvC d * LamM ^ 3 * qvPhiIso psiI psiA k (P.lEta T) ^ 2 *
      P.lEta s ^ (2 * lossAlpha k) / vsHeight P.z s := by
  unfold qvBndIso
  have h := qvPhiIso_anti (k := k) hI hA hLT hTs hk
  have h0 := qvPhiIso_nonneg (psiA := psiA) hI k (hLT.trans_le hTs)
  have hsq := pow_le_pow_left₀ h0 h 2
  have hc := (qvC_pos d).le
  have hr := Real.rpow_nonneg (hLT.trans_le hTs).le (2 * lossAlpha k)
  gcongr

/-!
## Positivity
-/

theorem qvPhiAv_pos {psiI psiA : ℕ → ℝ} (hI : ∀ j, 1 ≤ psiI j) (hA : ∀ j, 0 ≤ psiA j) (k : ℕ)
    {L : ℝ} (hL : 0 < L) : 0 < qvPhiAv psiI psiA k L := by
  unfold qvPhiAv
  split_ifs
  · refine Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg one_pos (mul_nonneg ?_ ?_))
    · linarith [hI (2 * k + 2)]
    · exact Real.rpow_nonneg hL.le _
  · linarith [hI (k + 1)]
  · refine mul_pos (by linarith [hI 5]) (Real.sqrt_pos.mpr ?_)
    exact add_pos_of_pos_of_nonneg one_pos (mul_nonneg (hA 8) (Real.rpow_nonneg hL.le _))

theorem qvPhiIso_pos {psiI psiA : ℕ → ℝ} (hI : ∀ j, 1 ≤ psiI j) (k : ℕ) {L : ℝ}
    (hL : 0 < L) : 0 < qvPhiIso psiI psiA k L := by
  have hI0 : ∀ j, 0 ≤ psiI j := fun j => zero_le_one.trans (hI j)
  unfold qvPhiIso
  have h1 : 0 < psiI k * Real.sqrt (psiI 2) * L ^ (-(1 / 4 : ℝ)) :=
    mul_pos (mul_pos (by linarith [hI k]) (Real.sqrt_pos.mpr (by linarith [hI 2])))
      (Real.rpow_pos_of_pos hL _)
  have h2 := Finset.sum_nonneg fun j (_ : j ∈ Finset.Icc 2 ((k + 1) / 2)) =>
    qvPhiMid_nonneg hI0 k j hL
  have h3 := qvPhiTilde_nonneg (psiA := psiA) hI0 k L
  linarith

theorem qv_ups_pos (d : VSData) {P : PsiData (p.n * p.W)} (hPW : P.W = p.W)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {t : ℝ} (ht1 : t ≤ 1) :
    ∀ x y, 0 < P.ups t x y := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  intro x y
  unfold PsiData.ups
  exact Adapters.ErdosRiabov.polynomialControl_pos hN (by rw [hPW]; exact p.W_pos) _
    (vsHeight_pos (hz.im_pos hN) ht1) x y

theorem qv_sAv_pos {N : ℕ} (P : PsiData N) {t : ℝ} (hU : ∀ x y, 0 < P.ups t x y)
    (hL : 0 < P.lEta t) {k : ℕ} (x : Fin k → Fin N) : 0 < P.sAv x t := by
  unfold PsiData.sAv
  split_ifs
  · exact inv_pos.mpr hL
  · exact mul_pos (Real.rpow_pos_of_pos hL _)
      (Real.sqrt_pos.mpr (Finset.prod_pos fun j _ => hU _ _))

theorem qv_sIso_pos {N : ℕ} (P : PsiData N) {t : ℝ} (hU : ∀ x y, 0 < P.ups t x y)
    (hL : 0 < P.lEta t) {k : ℕ} (a b : Fin N) (x : Fin k → Fin N) : 0 < P.sIso a b x t := by
  unfold PsiData.sIso
  exact mul_pos (Real.rpow_pos_of_pos hL _)
    (Real.sqrt_pos.mpr (Finset.prod_pos fun j _ => hU _ _))

theorem qvIntRule_pos (d : VSData) {P : PsiData (p.n * p.W)} (hPW : P.W = p.W)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {γ T : ℝ} (hγ : 0 ≤ γ)
    (hT1 : T ≤ 1) : 0 < qvIntRule d P γ T := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hm : 0 < imLower d.kappa d.C0 := d.cm_pos
  unfold qvIntRule
  split_ifs with h0
  · refine mul_pos (inv_pos.mpr hm) (Real.log_pos ?_)
    have h1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast hN
    nlinarith [d.C0_ge_one]
  · have hγ' : 0 < γ := lt_of_le_of_ne hγ (Ne.symm h0)
    have hL := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) (hz.im_pos hN) hT1
    have := Real.rpow_pos_of_pos hL (-γ)
    have := mul_pos hγ' hm
    positivity

/-!
## Sizes in time
-/

theorem qv_sIso_sq_time_le {N : ℕ} (P : PsiData N) {s t : ℝ} (hU : ∀ x y, 0 ≤ P.ups s x y)
    (hst : ∀ x y, P.ups s x y ≤ P.ups t x y) (hLt : 0 < P.lEta t) (hLs : P.lEta t ≤ P.lEta s)
    {n : ℕ} (a b : Fin N) (x : Fin (n + 1) → Fin N) :
    P.sIso a b x s ^ 2 ≤ (P.lEta t / P.lEta s) ^ n * P.sIso a b x t ^ 2 := by
  have hUt : ∀ x y, 0 ≤ P.ups t x y := fun x y => (hU x y).trans (hst x y)
  have hLs0 := hLt.trans_le hLs
  rw [sIso_qvPairs P hU hLs0 (fun _ => false) a b x, sIso_qvPairs P hUt hLt (fun _ => false) a b x,
    Real.sq_sqrt (qvIsoSq_nonneg P s hU hLs0 _ _ _),
    Real.sq_sqrt (qvIsoSq_nonneg P t hUt hLt _ _ _)]
  have h := qvIsoSq_time_le P hU hst hLt hLs a ((qvPairs (fun _ => false) x).map Prod.fst) b
  rw [List.length_map, qvPairs_length] at h
  exact h

theorem qv_sAv_sq_time_le {N : ℕ} (P : PsiData N) {s t : ℝ} (hU : ∀ x y, 0 ≤ P.ups s x y)
    (hst : ∀ x y, P.ups s x y ≤ P.ups t x y) (hLt : 0 < P.lEta t) (hLs : P.lEta t ≤ P.lEta s)
    {n : ℕ} (x : Fin (n + 1) → Fin N) :
    P.sAv x s ^ 2 ≤ (P.lEta t / P.lEta s) ^ (n + 1) * P.sAv x t ^ 2 := by
  have hUt : ∀ x y, 0 ≤ P.ups t x y := fun x y => (hU x y).trans (hst x y)
  have hLs0 := hLt.trans_le hLs
  rw [sAv_qvPairs P hU hLs0 (fun _ => false) x, sAv_qvPairs P hUt hLt (fun _ => false) x,
    Real.sq_sqrt (qvAvSq_nonneg P s hU hLs0 _ _), Real.sq_sqrt (qvAvSq_nonneg P t hUt hLt _ _)]
  have h := qvAvSq_time_le P hU hst hLt hLs (x (Fin.last n))
    ((qvPairs (fun _ => false) x).map Prod.fst)
  rw [List.length_map, qvPairs_length] at h
  exact h

/-- For `k = 1`, the isotropic propagator `U = vsTensorProp (μ^iso)` is the identity. -/
theorem qv_tensorProp_iso_one (P : PsiData (p.n * p.W)) (σ : Fin 1 → Bool) (μ' : Fin 1 → ℂ)
    (s t : ℝ) (x y : Fin 1 → Fin (p.n * p.W)) :
    vsTensorProp P.S (Evol.muIso P σ) μ' s t x y = if x = y then 1 else 0 := by
  have h0 : Evol.muIso P σ 0 = 0 := by simp [Evol.muIso]
  simp only [vsTensorProp, tensorMat, Fin.prod_univ_one]
  rw [h0, vsPropagator_zero_left, Matrix.one_apply]
  by_cases h : x = y
  · simp [h]
  · have h' : x 0 ≠ y 0 := fun h' => h (funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h')
    simp [h, h']

theorem qv_sum_delta {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι) (f : ι → ℝ) :
    ∑ α, ‖(if u = α then (1 : ℂ) else 0)‖ * f α = f u := by
  rw [Finset.sum_eq_single u (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd
    (Finset.mem_univ u) h)]
  simp

/-!
## The bound constants
-/

/-- `A` of family M1: `k² 𝔠 Λ_M³ φ^av(L_T)² (C_P^k)² L_T² s^av_T(u)²`, `k = n + 2`. -/
def qvMartAv (d : VSData) (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (LamM T : ℝ) {n : ℕ}
    (u : Fin (n + 2) → Fin (p.n * p.W)) : ℝ :=
  ((n : ℝ) + 2) ^ 2 * qvC d * LamM ^ 3 * qvPhiAv psiI psiA (n + 2) (P.lEta T) ^ 2 *
    (kernelActionConst d ^ (n + 2)) ^ 2 * P.lEta T ^ 2 * P.sAv u T ^ 2

/-- `A` of family M2: `k² 𝔠 Λ_M³ φ^iso(L_T)² (C_P^{k-1})² L_T s^iso_T(a,u,b)²`, `k = n + 2`. -/
def qvMartIso (d : VSData) (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (LamM T : ℝ) {n : ℕ}
    (a b : Fin (p.n * p.W)) (u : Fin (n + 2) → Fin (p.n * p.W)) : ℝ :=
  ((n : ℝ) + 2) ^ 2 * qvC d * LamM ^ 3 * qvPhiIso psiI psiA (n + 2) (P.lEta T) ^ 2 *
    (kernelActionConst d ^ (n + 1)) ^ 2 * P.lEta T * P.sIso a b u T ^ 2

/-- `A` of family M3: `𝔠 Λ_M³ φ^iso_1(L_T)² s^iso_T(a,u,b)²`. -/
def qvMartIsoOne (d : VSData) (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (LamM T : ℝ)
    (a b : Fin (p.n * p.W)) (u : Fin 1 → Fin (p.n * p.W)) : ℝ :=
  qvC d * LamM ^ 3 * qvPhiIso psiI psiA 1 (P.lEta T) ^ 2 * P.sIso a b u T ^ 2

/-- `A` of family M4: `k² 𝔠 Λ_M³ φ^av(L_T)² L_T^k s^av_T(u)²`, `k = n + 1`. -/
def qvMartSat (d : VSData) (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (LamM T : ℝ) {n : ℕ}
    (u : Fin (n + 1) → Fin (p.n * p.W)) : ℝ :=
  ((n : ℝ) + 1) ^ 2 * qvC d * LamM ^ 3 * qvPhiAv psiI psiA (n + 1) (P.lEta T) ^ 2 *
    P.lEta T ^ (n + 1) * P.sAv u T ^ 2

/-!
## Matrix forms of the regularized one-coordinate operators
-/

/-- The matrix of `ringOp S z t j a` on `ℂ^{(Fin k → Fin N)}`:
`V(y, α) = Σ_b [α = y[j ↦ b]] Θ̊^{y_a}_t(y_j, b)` (`qvRingMat_apply`). -/
def qvRingMat {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) (j a : Fin k) :
    Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  fun y α => ∑ b, if α = Function.update y j b then
    LemmaK.vsThetaRing S (semicircleM z) (conj (semicircleM z)) t (y a) (y j) b else 0

theorem qvRingMat_apply {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) (j a : Fin k)
    (f : (Fin k → Fin N) → ℂ) (y : Fin k → Fin N) :
    ∑ α, qvRingMat S z t j a y α * f α = ringOp S z t j a f y := by
  unfold qvRingMat ringOp
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (Function.update y j b), qv_ite_pos (Finset.mem_univ _)]

theorem qvRingMat_pi {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) (j a : Fin k)
    (g : (Fin k → Fin N) → ℝ) (hg : ∀ y, 0 ≤ g y) (y : Fin k → Fin N) :
    ∑ α, ‖qvRingMat S z t j a y α‖ * g α ≤ slotOp j (ringKer S z t j a) g y := by
  have h1 : ∀ α, ‖qvRingMat S z t j a y α‖ * g α ≤ ∑ b, (if α = Function.update y j b then
      ringKer S z t j a y b else 0) * g α := by
    intro α
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (le_of_eq ?_)) (hg α)
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : α = Function.update y j b
    · rw [qv_ite_pos h, qv_ite_pos h]; rfl
    · rw [qv_ite_neg h, qv_ite_neg h, norm_zero]
  refine (Finset.sum_le_sum fun α _ => h1 α).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  unfold slotOp
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (Function.update y j b), qv_ite_pos (Finset.mem_univ _)]

theorem qv_mulMat_pi {N k : ℕ} (U V : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (g : (Fin k → Fin N) → ℝ) (hg : ∀ y, 0 ≤ g y) (u : Fin k → Fin N) :
    ∑ α, ‖(U * V) u α‖ * g α ≤ ∑ y, ‖U u y‖ * ∑ α, ‖V y α‖ * g α := by
  have h1 : ∀ α, ‖(U * V) u α‖ * g α ≤ ∑ y, ‖U u y‖ * (‖V y α‖ * g α) := by
    intro α
    rw [Matrix.mul_apply]
    refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hg α)).trans (le_of_eq ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [norm_mul]
    ring
  refine (Finset.sum_le_sum fun α _ => h1 α).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

theorem qv_slotOp_nonneg {N k : ℕ} (j : Fin k) {K : (Fin k → Fin N) → Fin N → ℝ}
    (hK : ∀ y c, 0 ≤ K y c) {g : (Fin k → Fin N) → ℝ} (hg : ∀ y, 0 ≤ g y) (y : Fin k → Fin N) :
    0 ≤ slotOp j K g y :=
  Finset.sum_nonneg fun c _ => mul_nonneg (hK y c) (hg _)

theorem qv_ringPair_pi {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) (j a j' a' : Fin k)
    (g : (Fin k → Fin N) → ℝ) (hg : ∀ y, 0 ≤ g y) (y : Fin k → Fin N) :
    ∑ α, ‖(qvRingMat S z t j a * qvRingMat S z t j' a') y α‖ * g α ≤
      slotOp j (ringKer S z t j a) (slotOp j' (ringKer S z t j' a') g) y := by
  have hK : ∀ j a : Fin k, ∀ y c, 0 ≤ ringKer S z t j a y c := fun _ _ _ _ => norm_nonneg _
  refine (qv_mulMat_pi _ _ g hg y).trans ?_
  refine le_trans ?_ (qvRingMat_pi S z t j a _ (qv_slotOp_nonneg j' (hK j' a') hg) y)
  exact Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
    (qvRingMat_pi S z t j' a' g hg c) (norm_nonneg _)

theorem qv_onestepConst_pos (d : VSData) : 0 < onestepConst d := by
  unfold onestepConst
  have h1 := vsCK_pos d
  have h2 : 0 < d.C1pp := lt_of_lt_of_le one_pos d.one_le_C1pp
  have h3 : 0 < vsCK d / d.cm := div_pos h1 d.cm_pos
  have h4 : 0 < d.C1pp ^ 3 * Real.sqrt d.C1pp := mul_pos (pow_pos h2 3) (Real.sqrt_pos.mpr h2)
  have h5 : 0 < 1 + vsCK d / d.cm := by linarith
  have h6 : (0 : ℝ) < 2 * vsCK d := by linarith
  exact mul_pos (mul_pos h6 h4) h5

theorem qv_goodPropCoef_contDiff {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (cf : Fin k → PropFactor) (T : ℝ) (V : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (u α : Fin k → Fin N) :
    ContDiff ℝ 2 (fun s => ((goodProp S z cf s T : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ) *
      V) u α) := by
  unfold goodProp
  exact contDiff_tensorCoef _ _ _ _ _ _

theorem qv_sum_delta' {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι) (f : ι → ℝ) :
    ∑ α, ‖(if α = u then (1 : ℂ) else 0)‖ * f α = f u := by
  rw [Finset.sum_eq_single u (fun b _ hb => by simp [hb]) (fun h => absurd
    (Finset.mem_univ u) h)]
  simp

/-!
## The regularized matrices of `Circ` as `qvRingMat` and slot tensors
-/

/-- `Circ.circShortMat = qvRingMat` (last coordinate, anchor `⟨n⟩`). -/
theorem qv_circShortMat_eq {N n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) :
    Circ.circShortMat (n := n) S z t = qvRingMat S z t (Fin.last (n + 1)) ⟨n, by omega⟩ := by
  ext y α
  have h := congrFun (Circ.propOp_circShortMat S z t (Pi.single α 1)) y
  rw [propOp_apply, ← qvRingMat_apply] at h
  simpa [Pi.single_apply] using h

/-- `Circ.circLongMat` is the product of the two `qvRingMat`s. -/
theorem qv_circLongMat_eq {N n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) :
    Circ.circLongMat (n := n) S z t =
      qvRingMat S z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩ *
        qvRingMat S z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩ := by
  ext y α
  have h := congrFun (Circ.propOp_circLongMat S z t (Pi.single α 1)) y
  rw [propOp_apply] at h
  simp only [← qvRingMat_apply] at h
  simpa [Pi.single_apply, Matrix.mul_apply] using h

/-- `Circ.circLinMat` (`T̂_t` on the last coordinate) is a one-slot tensor. -/
theorem qv_circLinMat_eq {N n : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) :
    Circ.circLinMat (n := n) S z t = tensorMat (Function.update
      (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (Fin.last (n + 2 + 1))
        (vsKernel S (semicircleM z) (conj (semicircleM z)) t)) := by
  ext y α
  rw [tensorMat_update_one_apply, Circ.circLinMat, LinearMap.toMatrix'_apply,
    Circ.circSlot_apply, Finset.sum_eq_single (α (Fin.last (n + 2 + 1)))]
  · rw [Pi.single_apply]
    by_cases h : α = Function.update y (Fin.last (n + 2 + 1)) (α (Fin.last (n + 2 + 1)))
    · rw [qv_ite_pos h.symm, qv_ite_pos h, mul_one]
    · rw [qv_ite_neg (Ne.symm h), qv_ite_neg h, mul_zero]
  · intro c _ hc
    rw [Pi.single_apply, qv_ite_neg, mul_zero]
    intro h
    apply hc
    rw [← h, Function.update_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- In VS, `T̂^{(k)}_t` commutes with every propagator `goodProp S z c s t` (all factors are
functions of `S`). -/
theorem qv_goodProp_circLin_comm {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {z : ℂ} (hz : z.im ≠ 0) {n : ℕ} (s : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (cf : Fin (n + 2 + 2) → PropFactor) :
    (goodProp S z cf s t : Matrix (Fin (n + 2 + 2) → Fin N) (Fin (n + 2 + 2) → Fin N) ℂ) *
        Circ.circLinMat S z t = Circ.circLinMat S z t * goodProp S z cf s t := by
  rw [qv_circLinMat_eq]
  unfold goodProp vsTensorProp
  rw [← tensorMat_mul, ← tensorMat_mul]
  congr 1
  funext j
  by_cases hj : j = Fin.last (n + 2 + 1)
  · subst hj
    rw [Function.update_self]
    have hμ := Circ.circ_norm_mu1_lt_one hz (cf (Fin.last (n + 2 + 1)))
    have hμ' := Circ.circ_norm_mu2_lt_one hz (cf (Fin.last (n + 2 + 1)))
    have hT := norm_smul_lt_one hμ hμ' ht.1 ht.2
    have hP : Commute (vsPropagator S ((cf (Fin.last (n + 2 + 1))).mu1 z)
        ((cf (Fin.last (n + 2 + 1))).mu2 z) s t) (cMat S) := by
      unfold vsPropagator
      exact (commute_one_sub_vsY_cMat _ _ s).mul_left
        (commute_inv_of_commute_cMat hS (Commute.refl (cMat S)) hT).symm
    exact (commute_vsKernel_of_commute hS hP (Circ.circ_norm_smul_lt_one hz ht)).eq
  · rw [Function.update_of_ne hj, Matrix.mul_one, Matrix.one_mul]

/-- Row sums of a one-slot tensor against `g`:
`Σ_y |A^{(i)}(u,y)| g(y) = Σ_b |A(u_i,b)| g(u[i↦b])`. -/
theorem qv_slot_pi {N k : ℕ} (i : Fin k) (A : Matrix (Fin N) (Fin N) ℂ)
    (g : (Fin k → Fin N) → ℝ) (u : Fin k → Fin N) :
    ∑ y, ‖tensorMat (Function.update (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) i A) u y‖ * g y =
      ∑ b, ‖A (u i) b‖ * g (Function.update u i b) := by
  simp_rw [tensorMat_update_one_apply]
  have e : ∀ y : Fin k → Fin N,
      ‖(if y = Function.update u i (y i) then A (u i) (y i) else 0)‖ * g y =
        ∑ b, if y = Function.update u i b then ‖A (u i) b‖ * g y else 0 := by
    intro y
    rw [Finset.sum_eq_single (y i)]
    · split_ifs <;> simp
    · intro b _ hb
      rw [qv_ite_neg]
      intro h
      apply hb
      rw [h, Function.update_self]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp_rw [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (Function.update u i b), qv_ite_pos (Finset.mem_univ _)]

/-!
## The kernel action `qv_thetaSAv`
-/

theorem qvAvSq_cons_split {N : ℕ} (P : PsiData N) (t : ℝ) (c d : Fin N) (v : List (Fin N)) :
    qvAvSq P t c (d :: v) = (P.lEta t)⁻¹ ^ (v.length + 2) * qvPath (P.ups t) (d :: v) *
      (P.ups t c d * P.ups t ((d :: v).getLast (List.cons_ne_nil d v)) c) := by
  unfold qvAvSq
  rw [show (c :: d :: v) ++ [c] = c :: d :: (v ++ [c]) from rfl, qvPath_cons_cons,
    show d :: (v ++ [c]) = (d :: v) ++ [c] from rfl,
    qvPath_snoc (P.ups t) (d :: v) (List.cons_ne_nil d v) c]
  simp only [List.length_cons]
  ring

theorem qv_C10_core {N : ℕ} (d : VSData) {P : PsiData N} {t : ℝ} (hin : QVInputs d P t)
    (K : Matrix (Fin N) (Fin N) ℂ) {CK : ℝ} (hCK : 0 ≤ CK)
    (hK : ∀ x y, ‖K x y‖ ≤ CK * P.ups t x y) {Q : ℝ} (hQ : 0 ≤ Q) (x d0 e : Fin N) :
    ∑ b, ‖K x b‖ * Real.sqrt (Q * (P.ups t b d0 * P.ups t e b)) ≤
      CK * (d.Cwc / vsHeight P.z t) * Real.sqrt (Q * (P.ups t x d0 * P.ups t e x)) := by
  have hU := hin.nonneg
  have hpt : ∀ b, ‖K x b‖ * Real.sqrt (Q * (P.ups t b d0 * P.ups t e b)) ≤
      CK * Real.sqrt Q * Real.sqrt (P.ups t e b * P.ups t x b * P.ups t b x * P.ups t b d0) := by
    intro b
    have h1 : Real.sqrt (P.ups t e b * P.ups t x b * P.ups t b x * P.ups t b d0) =
        P.ups t x b * Real.sqrt (P.ups t b d0 * P.ups t e b) := by
      rw [show P.ups t e b * P.ups t x b * P.ups t b x * P.ups t b d0 =
          P.ups t x b ^ 2 * (P.ups t b d0 * P.ups t e b) by rw [hin.symm b x]; ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hU x b)]
    rw [h1, Real.sqrt_mul hQ]
    have h0 : 0 ≤ Real.sqrt Q * Real.sqrt (P.ups t b d0 * P.ups t e b) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc ‖K x b‖ * (Real.sqrt Q * Real.sqrt (P.ups t b d0 * P.ups t e b))
        ≤ CK * P.ups t x b * (Real.sqrt Q * Real.sqrt (P.ups t b d0 * P.ups t e b)) :=
          mul_le_mul_of_nonneg_right (hK x b) h0
      _ = _ := by ring
  have hsch := hin.schwarz e x x d0
  calc ∑ b, ‖K x b‖ * Real.sqrt (Q * (P.ups t b d0 * P.ups t e b))
      ≤ ∑ b, CK * Real.sqrt Q *
          Real.sqrt (P.ups t e b * P.ups t x b * P.ups t b x * P.ups t b d0) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = CK * Real.sqrt Q *
          ∑ b, Real.sqrt (P.ups t e b * P.ups t x b * P.ups t b x * P.ups t b d0) := by
        rw [Finset.mul_sum]
    _ ≤ CK * Real.sqrt Q * (d.Cwc / vsHeight P.z t * Real.sqrt (P.ups t e x * P.ups t x d0)) :=
        mul_le_mul_of_nonneg_left hsch (mul_nonneg hCK (Real.sqrt_nonneg _))
    _ = _ := by
        rw [Real.sqrt_mul hQ, show P.ups t x d0 * P.ups t e x = P.ups t e x * P.ups t x d0 by
          ring]
        ring

/-- **Kernel action on `s^av`**: for `k = n + 2` and a kernel `K` with
`|K| ≤ C_K Υ` (K1), `Σ_b |K(x_k, b)| s^av_k(x_1, …, x_{k-1}, b) ≤ C_K C_w η⁻¹ s^av_k(x)`.
-/
theorem qv_thetaSAv {N : ℕ} (d : VSData) {P : PsiData N} {t : ℝ} (hin : QVInputs d P t)
    (K : Matrix (Fin N) (Fin N) ℂ) {CK : ℝ} (hCK : 0 ≤ CK)
    (hK : ∀ x y, ‖K x y‖ ≤ CK * P.ups t x y) {n : ℕ} (x : Fin (n + 2) → Fin N) :
    ∑ b, ‖K (x (Fin.last (n + 1))) b‖ * P.sAv (Function.update x (Fin.last (n + 1)) b) t ≤
      CK * (d.Cwc / vsHeight P.z t) * P.sAv x t := by
  have hU := hin.nonneg
  have hL := hin.lEta_pos
  have hsites : ∀ y : Fin (n + 2) → Fin N, P.sAv y t = Real.sqrt (qvAvSq P t (y (Fin.last (n + 1)))
      (y (Fin.castSucc 0) :: List.ofFn fun i : Fin n => y i.succ.castSucc)) := by
    intro y
    rw [sAv_qvPairs P hU hL (fun _ => false) y, qvPairs_sites, List.ofFn_succ]
  have hc : ∀ (b : Fin N) (j : Fin (n + 1)),
      Function.update x (Fin.last (n + 1)) b j.castSucc = x j.castSucc :=
    fun b j => Function.update_of_ne (Fin.castSucc_lt_last j).ne _ _
  simp only [hsites, hc, Function.update_self]
  simp only [qvAvSq_cons_split]
  exact qv_C10_core d hin K hCK hK (mul_nonneg (pow_nonneg (inv_nonneg.mpr hL.le) _)
    (qvPath_nonneg hU _)) _ _ _

/-- `A` of a family with a size bound `Π(s) ≤ B (L_T/L_s)^j s^av_T(u)` (`k = n + 1`):
`k² 𝔠 Λ_M³ φ^av(L_T)² B² L_T^{2j} s^av_T(u)²`. -/
def qvMartGen (d : VSData) (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (LamM T Bc : ℝ)
    (j : ℕ) {n : ℕ} (u : Fin (n + 1) → Fin (p.n * p.W)) : ℝ :=
  ((n : ℝ) + 1) ^ 2 * qvC d * LamM ^ 3 * qvPhiAv psiI psiA (n + 1) (P.lEta T) ^ 2 * Bc ^ 2 *
    P.lEta T ^ (2 * j) * P.sAv u T ^ 2

/-!
## The martingale estimates
-/

section Mart

variable (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (d : VSData)
  {P : PsiData (p.n * p.W)} (hb : d.b = p.b) (hPS : P.S = shortRingProfile p.b p.n p.W)
  (hPW : P.W = p.W) (hPD : P.D = d.D) (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2)
  {psiI psiA : ℕ → ℝ} {LamM : ℝ} (hLam : 1 ≤ LamM) (hI : ∀ j, 1 ≤ psiI j)
  (hAv : ∀ j, 0 ≤ psiA j) {τ : RingSample p → WithTop ℝ≥0}
  (hτ : IsStoppingTime (driverAugmented (κ := Fin (ringDim p)) μ) τ) (T : ℝ≥0)
  (hT1 : (T : ℝ) ≤ 1)
  (hAP : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
    ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → APriori P psiI psiA LamM s (Evol.pathH p x s))
include hb hPS hPW hPD hz hP6 hLam hI hAv hτ hT1 hAP

/-- **Family M1** (non-saturated averaged chains): for `k = n + 2 ≤ 8`, a pattern `σ` with a
non-saturated factor, `T ≤ 1`, a `driverAugmented` stopping time `τ` and `APriori` a.s. on
`(0, T] ∩ [0, τ]`, the propagated noise `combMg 0 (zfam P.z σ) (avSlots) 1 (α s ↦ U(s,T)(u,α))`,
`U = vsTensorProp (μ^av, μ^next)` (the propagator of `Evol.duhamel_av`), satisfies, for `λ ≥ 0`,
`P(∃ r ≤ T, r ≤ τ, λ ≤ |·_r|) ≤ 4 exp(-λ²/(4 A y_γ))`, `γ = 2 - 2β_k`, `A = qvMartAv`,
`y_γ = qvIntRule γ T`. -/
theorem martingaleEstimate_av {n : ℕ} (hn : n + 2 ≤ 8) (σ : Fin (n + 2) → Bool)
    (hσ : HasDesatFactor σ) (u : Fin (n + 2) → Fin (p.n * p.W)) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) (fun y => avSlots P.S y) (fun _ => 1)
          (fun α s => vsTensorProp P.S (Evol.muAv P σ) (Evol.muNext P σ) s T u α) t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (qvMartAv d P psiI psiA LamM T u *
        qvIntRule d P (2 - 2 * lossBeta (n + 2)) T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hTI : (T : ℝ) ∈ Icc (0 : ℝ) T := ⟨T.2, le_rfl⟩
  have hLT := (hF.inputs T hTI).lEta_pos
  have hI0 : ∀ j, 0 ≤ psiI j := fun j => zero_le_one.trans (hI j)
  have hγ : 0 ≤ 2 - 2 * lossBeta (n + 2) := by linarith [qv_beta_le_one (k := n + 2) hn]
  have hA0 : 0 < qvMartAv d P psiI psiA LamM T u := by
    unfold qvMartAv
    have h1 := qvC_pos d
    have h2 := qvPhiAv_pos hI hAv (n + 2) hLT
    have h3 : 0 < kernelActionConst d := by linarith [kernelActionConst_ge_one d]
    have h4 := qv_sAv_pos P (qv_ups_pos d hPW hz hT1) hLT u
    have h5 : (0 : ℝ) < LamM := by linarith
    have h6 : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos h6 h1) (pow_pos h5 3))
      (pow_pos h2 2)) (pow_pos (pow_pos h3 _) 2)) (pow_pos hLT 2)) (pow_pos h4 2)
  refine qv_tail_of_rate μ d hPW hz σ (fun y => avSlots P.S y) (fun _ => 1)
    (fun α s => vsTensorProp P.S (Evol.muAv P σ) (Evol.muNext P σ) s T u α)
    (fun α => by
      have h : ContDiff ℝ 2 _ := contDiff_tensorCoef (S := P.S) (Evol.muAv P σ)
        (Evol.muNext P σ) (T : ℝ) 1 u α
      simpa only [Matrix.mul_one] using h)
    hτ T hT1 hA0.le hγ (mul_pos hA0 (qvIntRule_pos d hPW hz hγ hT1)) ?_ hlam
  filter_upwards [hAP] with x hx s hs hsτ
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  have hin := hF.inputs s hsI
  have hA : APriori P psiI psiA LamM s (ringMatrixFin p (vsNoise p s.toNNReal x)) := hx s hs hsτ
  rw [← hPS]
  simp only [qv_combDir_eq hη σ (fun y => avSlots P.S y) (fun _ => (1 : RingMat p))
    (fun α s => vsTensorProp P.S (Evol.muAv P σ) (Evol.muNext P σ) s T u α) hs1]
  refine (qv_bracket_av hin hA (ringMatrixFin_isHermitian _) hLam hI hAv (hF.one_le s hsI)
    (n := n + 1) hn σ _).trans ?_
  have hLs := hin.lEta_pos
  have hηs := hin.height_pos
  have hB := qvBndAv_le (d := d) (P := P) (psiI := psiI) (psiA := psiA) (LamM := LamM) hI0 hAv
    hLam hηs hLT (hF.anti s hsI) (n + 2)
  have hG := evol_goodProps_av d P hb hPS hPW hPD hz hs.1.le hs.2 hT1 σ hσ u
  have hS0 : 0 ≤ ∑ α, ‖vsTensorProp P.S (Evol.muAv P σ) (Evol.muNext P σ) s T u α‖ *
      P.sAv α s := Finset.sum_nonneg fun α _ =>
    mul_nonneg (norm_nonneg _) (qv_sAv_pos P (qv_ups_pos d hPW hz hs1) hLs α).le
  have hG2 := pow_le_pow_left₀ hS0 hG 2
  have hBb0 := qvBndAv_nonneg (psiI := psiI) (psiA := psiA) hin (n + 2) hLam
  have hk0 : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by positivity
  set A0 := ((n : ℝ) + 2) ^ 2 * qvC d * LamM ^ 3 * qvPhiAv psiI psiA (n + 2) (P.lEta T) ^ 2 *
    (kernelActionConst d ^ (n + 2)) ^ 2 * P.sAv u T ^ 2 * (vsHeight P.z s)⁻¹ with hA0def
  calc _ ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * (qvC d * LamM ^ 3 *
          qvPhiAv psiI psiA (n + 2) (P.lEta T) ^ 2 * P.lEta s ^ (2 * lossBeta (n + 2)) /
            vsHeight P.z s) *
          (kernelActionConst d ^ (n + 2) * (P.lEta T / P.lEta s) * P.sAv u T) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB hk0) hG2 (sq_nonneg _)
          (mul_nonneg hk0 (hBb0.trans hB))
    _ = A0 * P.lEta s ^ (2 * lossBeta (n + 2)) * (P.lEta T / P.lEta s) ^ 2 := by
        rw [hA0def]; push_cast; ring
    _ = A0 * P.lEta T ^ 2 * P.lEta s ^ (-(((2 : ℕ) : ℝ) - 2 * lossBeta (n + 2))) :=
        qv_rate_shift hLs _ 2
    _ = _ := by rw [hA0def]; unfold qvMartAv; push_cast; ring

/-- **Family M2** (isotropic chains `k = n + 2 ≤ 8`): as M1 for
`combMg 0 (zfam P.z σ) (isoSlots) E_{b'a'} (α s ↦ U(s,T)(u,α))`,
`U = vsTensorProp (μ^iso, μ^next)` (the propagator of `Evol.duhamel_iso`), with
`γ = 1 - 2α_k` and `A = qvMartIso`. Under the hypothesis `Split.ExplicitShortStatement` (`hES`,
proved as `MTerms.explicitShort_holds`). -/
theorem martingaleEstimate_iso (hES : Split.ExplicitShortStatement) {n : ℕ} (hn : n + 2 ≤ 8)
    (σ : Fin (n + 2) → Bool) (a' b' : Fin (p.n * p.W)) (u : Fin (n + 2) → Fin (p.n * p.W))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) (fun y => isoSlots P.S y)
          (fun _ => Matrix.single b' a' 1)
          (fun α s => vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α) t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (qvMartIso d P psiI psiA LamM T a' b' u *
        qvIntRule d P (1 - 2 * lossAlpha (n + 2)) T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hTI : (T : ℝ) ∈ Icc (0 : ℝ) T := ⟨T.2, le_rfl⟩
  have hLT := (hF.inputs T hTI).lEta_pos
  have hI0 : ∀ j, 0 ≤ psiI j := fun j => zero_le_one.trans (hI j)
  have hγ : 0 ≤ 1 - 2 * lossAlpha (n + 2) := by linarith [qv_alpha_le_half (k := n + 2) hn]
  have hA0 : 0 < qvMartIso d P psiI psiA LamM T a' b' u := by
    unfold qvMartIso
    have h1 := qvC_pos d
    have h2 := qvPhiIso_pos (psiA := psiA) hI (n + 2) hLT
    have h3 : 0 < kernelActionConst d := by linarith [kernelActionConst_ge_one d]
    have h4 := qv_sIso_pos P (qv_ups_pos d hPW hz hT1) hLT a' b' u
    have h5 : (0 : ℝ) < LamM := by linarith
    have h6 : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos h6 h1) (pow_pos h5 3))
      (pow_pos h2 2)) (pow_pos (pow_pos h3 _) 2)) hLT) (pow_pos h4 2)
  refine qv_tail_of_rate μ d hPW hz σ (fun y => isoSlots P.S y) (fun _ => Matrix.single b' a' 1)
    (fun α s => vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α)
    (fun α => by
      have h : ContDiff ℝ 2 _ := contDiff_tensorCoef (S := P.S) (Evol.muIso P σ)
        (Evol.muNext P σ) (T : ℝ) 1 u α
      simpa only [Matrix.mul_one] using h)
    hτ T hT1 hA0.le hγ (mul_pos hA0 (qvIntRule_pos d hPW hz hγ hT1)) ?_ hlam
  filter_upwards [hAP] with x hx s hs hsτ
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  have hin := hF.inputs s hsI
  have hA : APriori P psiI psiA LamM s (ringMatrixFin p (vsNoise p s.toNNReal x)) := hx s hs hsτ
  rw [← hPS]
  simp only [qv_combDir_eq hη σ (fun y => isoSlots P.S y)
    (fun _ => (Matrix.single b' a' 1 : RingMat p))
    (fun α s => vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α) hs1]
  refine (qv_bracket_iso hin hA (ringMatrixFin_isHermitian _) hLam hI hAv (hF.one_le s hsI) hES
    hS hη.ne' ⟨hs.1.le, hs1⟩ (hF.stab s hsI) (n := n + 1) hn σ a' b' _).trans ?_
  have hLs := hin.lEta_pos
  have hηs := hin.height_pos
  have hB := qvBndIso_le (d := d) (P := P) (psiI := psiI) (psiA := psiA) (LamM := LamM) hI0 hAv
    hLam hηs hLT (hF.anti s hsI) hn
  have hG := evol_goodProps_iso d P hb hPS hPW hPD hz hs.1.le hs.2 hT1 σ a' b' u
  have hS0 : 0 ≤ ∑ α, ‖vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α‖ *
      P.sIso a' b' α s := Finset.sum_nonneg fun α _ =>
    mul_nonneg (norm_nonneg _) (qv_sIso_pos P (qv_ups_pos d hPW hz hs1) hLs a' b' α).le
  have hG2 := pow_le_pow_left₀ hS0 hG 2
  have hBb0 := qvBndIso_nonneg (psiI := psiI) (psiA := psiA) hin (n + 2) hLam
  have hk0 : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by positivity
  have hsq : (kernelActionConst d ^ (n + 1) * Real.sqrt (P.lEta T / P.lEta s) *
      P.sIso a' b' u T) ^ 2 = (kernelActionConst d ^ (n + 1)) ^ 2 * (P.lEta T / P.lEta s) *
        P.sIso a' b' u T ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hLT.le hLs.le)]
  set A0 := ((n : ℝ) + 2) ^ 2 * qvC d * LamM ^ 3 * qvPhiIso psiI psiA (n + 2) (P.lEta T) ^ 2 *
    (kernelActionConst d ^ (n + 1)) ^ 2 * P.sIso a' b' u T ^ 2 * (vsHeight P.z s)⁻¹ with hA0def
  calc _ ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * (qvC d * LamM ^ 3 *
          qvPhiIso psiI psiA (n + 2) (P.lEta T) ^ 2 * P.lEta s ^ (2 * lossAlpha (n + 2)) /
            vsHeight P.z s) *
          (kernelActionConst d ^ (n + 1) * Real.sqrt (P.lEta T / P.lEta s) *
            P.sIso a' b' u T) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB hk0) hG2 (sq_nonneg _)
          (mul_nonneg hk0 (hBb0.trans hB))
    _ = A0 * P.lEta s ^ (2 * lossAlpha (n + 2)) * (P.lEta T / P.lEta s) ^ 1 := by
        rw [hsq, hA0def]; push_cast; ring
    _ = A0 * P.lEta T ^ 1 * P.lEta s ^ (-(((1 : ℕ) : ℝ) - 2 * lossAlpha (n + 2))) :=
        qv_rate_shift hLs _ 1
    _ = _ := by rw [hA0def]; unfold qvMartIso; push_cast; ring

/-- **Family M3** (isotropic `k = 1`, `U = I` by `qv_tensorProp_iso_one`): as M2 with `γ = 0`
and `A = qvMartIsoOne`. Under the hypothesis `Split.ExplicitShortStatement` (proved as
`MTerms.explicitShort_holds`). -/
theorem martingaleEstimate_iso_one (hES : Split.ExplicitShortStatement) (σ : Fin 1 → Bool)
    (a' b' : Fin (p.n * p.W)) (u : Fin 1 → Fin (p.n * p.W)) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) (fun y => isoSlots P.S y)
          (fun _ => Matrix.single b' a' 1)
          (fun α s => vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α) t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (qvMartIsoOne d P psiI psiA LamM T a' b' u *
        qvIntRule d P 0 T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hTI : (T : ℝ) ∈ Icc (0 : ℝ) T := ⟨T.2, le_rfl⟩
  have hLT := (hF.inputs T hTI).lEta_pos
  have hI0 : ∀ j, 0 ≤ psiI j := fun j => zero_le_one.trans (hI j)
  have hA0 : 0 < qvMartIsoOne d P psiI psiA LamM T a' b' u := by
    unfold qvMartIsoOne
    have h1 := qvC_pos d
    have h2 := qvPhiIso_pos (psiA := psiA) hI 1 hLT
    have h4 := qv_sIso_pos P (qv_ups_pos d hPW hz hT1) hLT a' b' u
    have h5 : (0 : ℝ) < LamM := by linarith
    exact mul_pos (mul_pos (mul_pos h1 (pow_pos h5 3)) (pow_pos h2 2)) (pow_pos h4 2)
  refine qv_tail_of_rate μ d hPW hz σ (fun y => isoSlots P.S y) (fun _ => Matrix.single b' a' 1)
    (fun α s => vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α)
    (fun α => by
      have h : ContDiff ℝ 2 _ := contDiff_tensorCoef (S := P.S) (Evol.muIso P σ)
        (Evol.muNext P σ) (T : ℝ) 1 u α
      simpa only [Matrix.mul_one] using h)
    hτ T hT1 hA0.le le_rfl (mul_pos hA0 (qvIntRule_pos d hPW hz le_rfl hT1)) ?_ hlam
  filter_upwards [hAP] with x hx s hs hsτ
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  have hin := hF.inputs s hsI
  have hA : APriori P psiI psiA LamM s (ringMatrixFin p (vsNoise p s.toNNReal x)) := hx s hs hsτ
  rw [← hPS]
  simp only [qv_combDir_eq hη σ (fun y => isoSlots P.S y)
    (fun _ => (Matrix.single b' a' 1 : RingMat p))
    (fun α s => vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α) hs1]
  refine (qv_bracket_iso hin hA (ringMatrixFin_isHermitian _) hLam hI hAv (hF.one_le s hsI) hES
    hS hη.ne' ⟨hs.1.le, hs1⟩ (hF.stab s hsI) (n := 0) (by norm_num) σ a' b' _).trans ?_
  have hLs := hin.lEta_pos
  have hηs := hin.height_pos
  have hB := qvBndIso_le (d := d) (P := P) (psiI := psiI) (psiA := psiA) (LamM := LamM) hI0 hAv
    hLam hηs hLT (hF.anti s hsI) (k := 1) (by norm_num)
  have hsum : ∑ α, ‖vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α‖ *
      P.sIso a' b' α s = P.sIso a' b' u s := by
    simp only [qv_tensorProp_iso_one]
    exact qv_sum_delta u _
  have hT := qv_sIso_sq_time_le P hin.nonneg (hF.upsMono s hsI) hLT (hF.anti s hsI) a' b' u
  have hBb0 := qvBndIso_nonneg (psiI := psiI) (psiA := psiA) hin 1 hLam
  have hα : lossAlpha 1 = 0 := qv_alpha_of_le_four (by norm_num)
  rw [hsum]
  calc _ ≤ (((0 : ℕ) : ℝ) + 1) ^ 2 * (qvC d * LamM ^ 3 *
          qvPhiIso psiI psiA 1 (P.lEta T) ^ 2 * P.lEta s ^ (2 * lossAlpha 1) /
            vsHeight P.z s) * ((P.lEta T / P.lEta s) ^ 0 * P.sIso a' b' u T ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB (by positivity)) hT (sq_nonneg _)
          (mul_nonneg (by positivity) (hBb0.trans hB))
    _ = _ := by
        rw [hα, mul_zero, Real.rpow_zero, neg_zero, Real.rpow_zero]
        unfold qvMartIsoOne
        push_cast
        ring

/-- **Family M4** (averaged chains with `U = I`, any pattern, `k = n + 1 ≤ 8`): the noise
`combMg 0 (zfam P.z σ) (avSlots) 1 δ_u` satisfies the bound of M1 with `γ = k - 2β_k` and
`A = qvMartSat`. -/
theorem martingaleEstimate_sat {n : ℕ} (hn : n + 1 ≤ 8) (σ : Fin (n + 1) → Bool)
    (u : Fin (n + 1) → Fin (p.n * p.W)) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) (fun y => avSlots P.S y) (fun _ => 1)
          (fun α _ => if α = u then (1 : ℂ) else 0) t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (qvMartSat d P psiI psiA LamM T u *
        qvIntRule d P ((n : ℝ) + 1 - 2 * lossBeta (n + 1)) T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hTI : (T : ℝ) ∈ Icc (0 : ℝ) T := ⟨T.2, le_rfl⟩
  have hLT := (hF.inputs T hTI).lEta_pos
  have hI0 : ∀ j, 0 ≤ psiI j := fun j => zero_le_one.trans (hI j)
  have hγ : 0 ≤ (n : ℝ) + 1 - 2 * lossBeta (n + 1) := by
    rcases n with _ | n
    · have h1 : lossBeta 1 = lossAlpha 2 := qv_beta_eq_alpha (k := 1) (by norm_num)
      have h2 := qv_alpha_le_half (k := 2) (by norm_num)
      norm_num
      linarith
    · have h1 := qv_beta_le_one (k := n + 1 + 1) hn
      have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      linarith
  have hA0 : 0 < qvMartSat d P psiI psiA LamM T u := by
    unfold qvMartSat
    have h1 := qvC_pos d
    have h2 := qvPhiAv_pos hI hAv (n + 1) hLT
    have h4 := qv_sAv_pos P (qv_ups_pos d hPW hz hT1) hLT u
    have h5 : (0 : ℝ) < LamM := by linarith
    have h6 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos h6 h1) (pow_pos h5 3))
      (pow_pos h2 2)) (pow_pos hLT _)) (pow_pos h4 2)
  refine qv_tail_of_rate μ d hPW hz σ (fun y => avSlots P.S y) (fun _ => 1)
    (fun α _ => if α = u then (1 : ℂ) else 0) (fun α => contDiff_const)
    hτ T hT1 hA0.le hγ (mul_pos hA0 (qvIntRule_pos d hPW hz hγ hT1)) ?_ hlam
  filter_upwards [hAP] with x hx s hs hsτ
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  have hin := hF.inputs s hsI
  have hA : APriori P psiI psiA LamM s (ringMatrixFin p (vsNoise p s.toNNReal x)) := hx s hs hsτ
  rw [← hPS]
  simp only [qv_combDir_eq hη σ (fun y => avSlots P.S y) (fun _ => (1 : RingMat p))
    (fun α _ => if α = u then (1 : ℂ) else 0) hs1]
  refine (qv_bracket_av hin hA (ringMatrixFin_isHermitian _) hLam hI hAv (hF.one_le s hsI)
    hn σ _).trans ?_
  have hLs := hin.lEta_pos
  have hηs := hin.height_pos
  have hB := qvBndAv_le (d := d) (P := P) (psiI := psiI) (psiA := psiA) (LamM := LamM) hI0 hAv
    hLam hηs hLT (hF.anti s hsI) (n + 1)
  have hT := qv_sAv_sq_time_le P hin.nonneg (hF.upsMono s hsI) hLT (hF.anti s hsI) u
  have hBb0 := qvBndAv_nonneg (psiI := psiI) (psiA := psiA) hin (n + 1) hLam
  have hk0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by positivity
  rw [qv_sum_delta' u (fun α => P.sAv α s)]
  set A0 := ((n : ℝ) + 1) ^ 2 * qvC d * LamM ^ 3 * qvPhiAv psiI psiA (n + 1) (P.lEta T) ^ 2 *
    P.sAv u T ^ 2 * (vsHeight P.z s)⁻¹ with hA0def
  calc _ ≤ ((n : ℝ) + 1) ^ 2 * (qvC d * LamM ^ 3 *
          qvPhiAv psiI psiA (n + 1) (P.lEta T) ^ 2 * P.lEta s ^ (2 * lossBeta (n + 1)) /
            vsHeight P.z s) * ((P.lEta T / P.lEta s) ^ (n + 1) * P.sAv u T ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB hk0) hT (sq_nonneg _)
          (mul_nonneg hk0 (hBb0.trans hB))
    _ = A0 * P.lEta s ^ (2 * lossBeta (n + 1)) * (P.lEta T / P.lEta s) ^ (n + 1) := by
        rw [hA0def]; ring
    _ = A0 * P.lEta T ^ (n + 1) * P.lEta s ^ (-(((n + 1 : ℕ) : ℝ) - 2 * lossBeta (n + 1))) :=
        qv_rate_shift hLs _ (n + 1)
    _ = _ := by rw [hA0def]; unfold qvMartSat; push_cast; ring

/-- **Averaged chains with a size bound** (the common form of M5–M7): for `k = n + 1 ≤ 8`, a
pattern `σ`, `C²` coefficients `c_α` and `Π(s) = Σ_α |c_α(s)| s^av_s(α) ≤
B (L_T/L_s)^j s^av_T(u)` on `(0, T]`, with `γ = 2j - 2β_k ≥ 0`: the noise
`combMg 0 (zfam P.z σ) (avSlots) 1 c` satisfies the tail bound with `A = qvMartGen`. -/
theorem martingaleEstimate_avOfPi {n : ℕ} (hn : n + 1 ≤ 8) (σ : Fin (n + 1) → Bool)
    (u : Fin (n + 1) → Fin (p.n * p.W)) (c : (Fin (n + 1) → Fin (p.n * p.W)) → ℝ → ℂ)
    (hc : ∀ α, ContDiff ℝ 2 (c α)) {Bc : ℝ} (hBc : 0 < Bc) (j : ℕ) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : 2 * (j : ℝ) - 2 * lossBeta (n + 1) = γ)
    (hPi : ∀ s ∈ Ioc (0 : ℝ) T,
      ∑ α, ‖c α s‖ * P.sAv α s ≤ Bc * (P.lEta T / P.lEta s) ^ j * P.sAv u T)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) (fun y => avSlots P.S y) (fun _ => 1) c t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (qvMartGen d P psiI psiA LamM T Bc j u *
        qvIntRule d P γ T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hTI : (T : ℝ) ∈ Icc (0 : ℝ) T := ⟨T.2, le_rfl⟩
  have hLT := (hF.inputs T hTI).lEta_pos
  have hI0 : ∀ j, 0 ≤ psiI j := fun j => zero_le_one.trans (hI j)
  have hA0 : 0 < qvMartGen d P psiI psiA LamM T Bc j u := by
    unfold qvMartGen
    have h1 := qvC_pos d
    have h2 := qvPhiAv_pos hI hAv (n + 1) hLT
    have h4 := qv_sAv_pos P (qv_ups_pos d hPW hz hT1) hLT u
    have h5 : (0 : ℝ) < LamM := by linarith
    have h6 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos h6 h1) (pow_pos h5 3))
      (pow_pos h2 2)) (pow_pos hBc 2)) (pow_pos hLT _)) (pow_pos h4 2)
  refine qv_tail_of_rate μ d hPW hz σ (fun y => avSlots P.S y) (fun _ => 1) c hc
    hτ T hT1 hA0.le hγ0 (mul_pos hA0 (qvIntRule_pos d hPW hz hγ0 hT1)) ?_ hlam
  filter_upwards [hAP] with x hx s hs hsτ
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  have hin := hF.inputs s hsI
  have hA : APriori P psiI psiA LamM s (ringMatrixFin p (vsNoise p s.toNNReal x)) := hx s hs hsτ
  rw [← hPS]
  simp only [qv_combDir_eq hη σ (fun y => avSlots P.S y) (fun _ => (1 : RingMat p)) c hs1]
  refine (qv_bracket_av hin hA (ringMatrixFin_isHermitian _) hLam hI hAv (hF.one_le s hsI)
    hn σ _).trans ?_
  have hLs := hin.lEta_pos
  have hηs := hin.height_pos
  have hB := qvBndAv_le (d := d) (P := P) (psiI := psiI) (psiA := psiA) (LamM := LamM) hI0 hAv
    hLam hηs hLT (hF.anti s hsI) (n + 1)
  have hS0 : 0 ≤ ∑ α, ‖c α s‖ * P.sAv α s := Finset.sum_nonneg fun α _ =>
    mul_nonneg (norm_nonneg _) (qv_sAv_pos P (qv_ups_pos d hPW hz hs1) hLs α).le
  have hG2 := pow_le_pow_left₀ hS0 (hPi s hs) 2
  have hBb0 := qvBndAv_nonneg (psiI := psiI) (psiA := psiA) hin (n + 1) hLam
  have hk0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by positivity
  set A0 := ((n : ℝ) + 1) ^ 2 * qvC d * LamM ^ 3 * qvPhiAv psiI psiA (n + 1) (P.lEta T) ^ 2 *
    Bc ^ 2 * P.sAv u T ^ 2 * (vsHeight P.z s)⁻¹ with hA0def
  calc _ ≤ ((n : ℝ) + 1) ^ 2 * (qvC d * LamM ^ 3 *
          qvPhiAv psiI psiA (n + 1) (P.lEta T) ^ 2 * P.lEta s ^ (2 * lossBeta (n + 1)) /
            vsHeight P.z s) * (Bc * (P.lEta T / P.lEta s) ^ j * P.sAv u T) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB hk0) hG2 (sq_nonneg _)
          (mul_nonneg hk0 (hBb0.trans hB))
    _ = A0 * P.lEta s ^ (2 * lossBeta (n + 1)) * (P.lEta T / P.lEta s) ^ (2 * j) := by
        rw [hA0def]; ring
    _ = A0 * P.lEta T ^ (2 * j) * P.lEta s ^ (-(((2 * j : ℕ) : ℝ) - 2 * lossBeta (n + 1))) :=
        qv_rate_shift hLs _ (2 * j)
    _ = _ := by rw [← hγ, hA0def]; unfold qvMartGen; push_cast; ring

/-- **Family M5** (one ring, `k = 2`): the noise with coefficient
`V_T(s) = P̂^{⊗2}_{s,T} Θ̊^{(2)}_T` (`goodProp` with saturated factors times `qvRingMat` on the
last coordinate, anchor `x_1`), `Π ≤ C_reg C_P² η_T⁻¹ s^av_T(u)` by `regProps_oneRing`;
`γ = 0` (`β_2 = 0`). -/
theorem martingaleEstimate_oneRing (σ : Fin 2 → Bool) (u : Fin 2 → Fin (p.n * p.W))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) (fun y => avSlots P.S y) (fun _ => 1)
          (fun α s => ((goodProp P.S P.z (fun _ => .sat) s T * Circ.circShortMat P.S P.z T :
            Matrix (Fin (0 + 2) → Fin (p.n * p.W)) (Fin (0 + 2) → Fin (p.n * p.W)) ℂ)) u α)
          t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (qvMartGen d P psiI psiA LamM T
        (onestepConst d * kernelActionConst d ^ 2 / vsHeight P.z T) 0 u *
          qvIntRule d P 0 T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hβ : lossBeta (1 + 1) = 0 := by
    rw [show lossBeta (1 + 1) = lossAlpha 3 from qv_beta_eq_alpha (k := 2) (by norm_num)]
    exact qv_alpha_of_le_four (by norm_num)
  have hBc : 0 < onestepConst d * kernelActionConst d ^ 2 / vsHeight P.z T :=
    div_pos (mul_pos (qv_onestepConst_pos d)
      (pow_pos (lt_of_lt_of_le one_pos (kernelActionConst_ge_one d)) 2)) (vsHeight_pos hη hT1)
  refine martingaleEstimate_avOfPi μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP
    (n := 1) (by norm_num) σ u _ (fun α => qv_goodPropCoef_contDiff P.S P.z _ T _ u α)
    hBc 0 le_rfl (by rw [hβ]; norm_num) ?_ hlam
  intro s hs
  have hg : ∀ y : Fin 2 → Fin (p.n * p.W), 0 ≤ P.sAv y s := fun y =>
    (qv_sAv_pos P (qv_ups_pos d hPW hz (hs.2.trans hT1)) (P.lEta_pos hN (by rw [hPW]; exact
      p.W_pos) hη (hs.2.trans hT1)) y).le
  refine (qv_mulMat_pi _ _ _ hg u).trans ?_
  rw [qv_circShortMat_eq]
  have h := regProps_oneRing d p.n_ge_four p.W_pos P hPW hPD hz hs.1.le hs.2 hT1 (n := 0) u
  rw [← evol_PS_eq d P hb hPS] at h
  rw [pow_zero, mul_one]
  refine le_trans (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
    (qvRingMat_pi P.S P.z T (Fin.last (0 + 1)) ⟨0, by omega⟩ _ hg y) (norm_nonneg _)) ?_
  exact h

/-- **Family M6** (two rings, `k = n + 4 ≤ 8`): the noise with coefficient
`V_T(s) = P̂^{⊗k}_{s,T} Θ̊^{(k-2)}_T Θ̊^{(k)}_T` (`qvRingMat` on coordinates `k-3`, anchor `k-4`,
and `k-1`, anchor `k-2`, 0-based), `Π ≤ C_reg² C_P^k η_T⁻² (L_T/L_s) s^av_T(u)` by
`regProps_twoRings`; `γ = 2 - 2β_k`. -/
theorem martingaleEstimate_twoRings {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) (fun y => avSlots P.S y) (fun _ => 1)
          (fun α s => ((goodProp P.S P.z (fun _ => .sat) s T * Circ.circLongMat P.S P.z T :
            Matrix (Fin (n + 2 + 2) → Fin (p.n * p.W)) (Fin (n + 2 + 2) → Fin (p.n * p.W)) ℂ)) u α)
          t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (qvMartGen d P psiI psiA LamM T
        (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z T ^ 2) 1 u *
          qvIntRule d P (2 - 2 * lossBeta (n + 4)) T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hBc : 0 < onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z T ^ 2 :=
    div_pos (mul_pos (pow_pos (qv_onestepConst_pos d) 2)
      (pow_pos (lt_of_lt_of_le one_pos (kernelActionConst_ge_one d)) _))
      (pow_pos (vsHeight_pos hη hT1) 2)
  refine martingaleEstimate_avOfPi μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP
    (n := n + 3) hn σ u _ (fun α => qv_goodPropCoef_contDiff P.S P.z _ T _ u α)
    hBc 1 (by linarith [qv_beta_le_one (k := n + 4) hn]) (by push_cast; ring) ?_ hlam
  intro s hs
  have hg : ∀ y : Fin (n + 2 + 2) → Fin (p.n * p.W), 0 ≤ P.sAv y s := fun y =>
    (qv_sAv_pos P (qv_ups_pos d hPW hz (hs.2.trans hT1)) (P.lEta_pos hN (by rw [hPW]; exact
      p.W_pos) hη (hs.2.trans hT1)) y).le
  refine (qv_mulMat_pi _ _ _ hg u).trans ?_
  rw [qv_circLongMat_eq]
  have h := regProps_twoRings d p.n_ge_four p.W_pos P hPW hPD hz hs.1.le hs.2 hT1 (n := n) u
  rw [← evol_PS_eq d P hb hPS] at h
  rw [pow_one]
  refine le_trans (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
    (qv_ringPair_pi P.S P.z T _ _ _ _ _ hg y) (norm_nonneg _)) ?_
  exact h

/-- **Family M7** (long linear term, `k = n + 4 ≤ 8`): the noise of
`Circ.linTerm_evol_combMg`, coefficient `V_T(s) = P̃^k_{s,T} T̂^{(k)}_T` (`goodProp` with
`Circ.linFactor n`, identity factor at `k-2`, times `Circ.circLinMat`). By the commutation
`qv_goodProp_circLin_comm`, `goodProps_av_any` and `qv_thetaSAv` with (K1),
`Π ≤ C_K C_w C_P^k η_T⁻¹ (L_T/L_s) s^av_T(u)`; `γ = 2 - 2β_k`. -/
theorem martingaleEstimate_longLinear {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) (fun y => avSlots P.S y) (fun _ => 1)
          (fun α s => ((goodProp P.S P.z (Circ.linFactor n) s T * Circ.circLinMat P.S P.z T :
            Matrix (Fin (n + 2 + 2) → Fin (p.n * p.W)) (Fin (n + 2 + 2) → Fin (p.n * p.W)) ℂ)) u α)
          t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (qvMartGen d P psiI psiA LamM T
        (vsCK d * (d.Cwc / vsHeight P.z T) * kernelActionConst d ^ (n + 4)) 1 u *
          qvIntRule d P (2 - 2 * lossBeta (n + 4)) T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hηT := vsHeight_pos hη hT1
  have hBc : 0 < vsCK d * (d.Cwc / vsHeight P.z T) * kernelActionConst d ^ (n + 4) :=
    mul_pos (mul_pos (vsCK_pos d) (div_pos (lt_of_lt_of_le one_pos d.one_le_Cwc) hηT))
      (pow_pos (lt_of_lt_of_le one_pos (kernelActionConst_ge_one d)) _)
  have hS : StochasticSymm (shortRingProfile d.b p.n p.W) :=
    shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (m := p.n) (by have := p.n_ge_four; omega)
      p.W_pos
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hinT := hF.inputs T ⟨T.2, le_rfl⟩
  refine martingaleEstimate_avOfPi μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP
    (n := n + 3) hn σ u _ (fun α => qv_goodPropCoef_contDiff P.S P.z _ T _ u α)
    hBc 1 (by linarith [qv_beta_le_one (k := n + 4) hn]) (by push_cast; ring) ?_ hlam
  intro s hs
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have hLs := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hη hs1
  have hg : ∀ y : Fin (n + 2 + 2) → Fin (p.n * p.W), 0 ≤ P.sAv y s := fun y =>
    (qv_sAv_pos P (qv_ups_pos d hPW hz hs1) hLs y).le
  have hgT : ∀ y : Fin (n + 2 + 2) → Fin (p.n * p.W), 0 ≤ P.sAv y T := fun y =>
    (qv_sAv_pos P (qv_ups_pos d hPW hz hT1) hinT.lEta_pos y).le
  rw [evol_PS_eq d P hb hPS]
  have hcomm := qv_goodProp_circLin_comm hS hη.ne' s ⟨T.2, hT1⟩ (Circ.linFactor n)
  have hsw : ∑ α, ‖((goodProp (shortRingProfile d.b p.n p.W) P.z (Circ.linFactor n) s T *
      Circ.circLinMat (shortRingProfile d.b p.n p.W) P.z T :
        Matrix (Fin (n + 2 + 2) → Fin (p.n * p.W)) (Fin (n + 2 + 2) → Fin (p.n * p.W)) ℂ)) u α‖ *
          P.sAv α s =
      ∑ α, ‖((Circ.circLinMat (shortRingProfile d.b p.n p.W) P.z T *
        goodProp (shortRingProfile d.b p.n p.W) P.z (Circ.linFactor n) s T :
          Matrix (Fin (n + 2 + 2) → Fin (p.n * p.W)) (Fin (n + 2 + 2) → Fin (p.n * p.W)) ℂ))
            u α‖ * P.sAv α s :=
    Finset.sum_congr rfl fun α _ => congrArg (fun M : Matrix (Fin (n + 2 + 2) → Fin (p.n * p.W))
      (Fin (n + 2 + 2) → Fin (p.n * p.W)) ℂ => ‖M u α‖ * P.sAv α s) hcomm
  refine (le_of_eq hsw).trans ((qv_mulMat_pi _ _ _ hg u).trans ?_)
  have hG : ∀ y, ∑ α, ‖goodProp (shortRingProfile d.b p.n p.W) P.z (Circ.linFactor n) s T y α‖ *
      P.sAv α s ≤ kernelActionConst d ^ (n + 2 + 2) * (P.lEta T / P.lEta s) * P.sAv y T :=
    fun y => goodProps_av_any d p.n_ge_four p.W_pos P hPW hPD hz hs.1.le hs.2 hT1
      (Circ.linFactor n) ⟨n + 1, by omega⟩ (by simp [Circ.linFactor]) y
  have hK : ∀ x y, ‖vsKernel (shortRingProfile d.b p.n p.W) (semicircleM P.z)
      (conj (semicircleM P.z)) T x y‖ ≤ vsCK d * P.ups T x y := by
    intro x y
    have h := (lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos d.C0_ge_one
      d.D_ge_six p.n_ge_four p.W_pos hz T.2 hT1).1 x y
    unfold PsiData.ups
    rw [hPW, hPD]
    exact h
  have hC10 := qv_thetaSAv d hinT _ (vsCK_pos d).le hK (n := n + 2) u
  have hRatio : 0 ≤ kernelActionConst d ^ (n + 2 + 2) * (P.lEta T / P.lEta s) :=
    mul_nonneg (pow_nonneg (by linarith [kernelActionConst_ge_one d]) _)
      (div_nonneg hinT.lEta_pos.le hLs.le)
  calc _ ≤ ∑ y, ‖Circ.circLinMat (shortRingProfile d.b p.n p.W) P.z T u y‖ *
        (kernelActionConst d ^ (n + 2 + 2) * (P.lEta T / P.lEta s) * P.sAv y T) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hG y) (norm_nonneg _)
    _ = kernelActionConst d ^ (n + 2 + 2) * (P.lEta T / P.lEta s) *
        ∑ y, ‖Circ.circLinMat (shortRingProfile d.b p.n p.W) P.z T u y‖ * P.sAv y T := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = kernelActionConst d ^ (n + 2 + 2) * (P.lEta T / P.lEta s) *
        ∑ b, ‖vsKernel (shortRingProfile d.b p.n p.W) (semicircleM P.z) (conj (semicircleM P.z))
          T (u (Fin.last (n + 2 + 1))) b‖ *
            P.sAv (Function.update u (Fin.last (n + 2 + 1)) b) T := by
        rw [qv_circLinMat_eq, qv_slot_pi]
    _ ≤ kernelActionConst d ^ (n + 2 + 2) * (P.lEta T / P.lEta s) *
        (vsCK d * (d.Cwc / vsHeight P.z T) * P.sAv u T) :=
        mul_le_mul_of_nonneg_left hC10 hRatio
    _ = _ := by ring

end Mart

end BlockBand.Native.ErdosRiabov.QV
