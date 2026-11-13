module

public import BlockBand.Native.ErdosRiabov.MI.ForcingFam
public import BlockBand.Native.ErdosRiabov.Apriori.Bounds
public import BlockBand.Native.ErdosRiabov.Discharge.All2

/-!
# Master inequalities: noise constants, the event inclusion and the explicit constants

* The constants of the master inequalities, explicit in `VSData`, `Λ_M`, `k`, `T`:
  forcing constants `fAvC`, `fAvOneC`, `fIsoC`, `fIsoOneC` (of the form `C_F iF(γ_F)`) and
  noise constants `mAvC`, `mAvOneC`, `mIsoC`, `mIsoOneC`, `mSatC`
  (`C_M √(𝔠 Λ³ iF(γ_M))`); the extra `M`-bound constant `eMI d N k` (`Apriori.extraConst` with
  the isotropic constants `I_n`), the `M`-bound constant `Λ_M = Apriori.aprLamM d N`.
* `sq_noise`, `lp_y`: the QV variance `A y` of `QV.martingaleEstimate_*` is
  `(C_M √(𝔠 Λ³ iF) φ^{qv} L_T^{α/β} s_T)²`.
* `mi_event_le`, `mi_event_le'` (deterministic set inclusion): if a.s. on
  `{T ≤ τ}` (and on a good event `G`) `X ≤ F den + mg_T`, then
  `{T ≤ τ, bnd ≤ X/den} ⊆ {∃ t ≤ T, t ≤ τ, λ ≤ mg_t} (∪ {T ≤ τ, ¬G})` a.s. whenever
  `F + λ/den ≤ bnd`.
* `mi_tail`: `4 e^{-(r√Q)²/(4Q)} = 4 e^{-r²/4}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MI

open MeasureTheory Set Finset
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Forcing
open BlockBand.Native.ErdosRiabov.QV
open Expo (lossAlpha lossBeta)
open scoped NNReal ENNReal

variable {p : BlockBand.Parameters}

/-!
## Constants
-/

/-- The extra `M`-bound constant `E_k = extraConst d (I) k` with
`I_n = mbConstI d Λ_N (mzeroConst d) n`
(`Apriori.mbounds_extra_uncond`). -/
def eMI (d : VSData) (N k : ℕ) : ℝ :=
  Apriori.extraConst d (MBound.mbConstI d (MBound.mbLambda d N) (MZero.mzeroConst d)) k

theorem eMI_nonneg (d : VSData) {N : ℕ} (hN : 0 < N) (k : ℕ) : 0 ≤ eMI d N k := by
  have hΛ := MBound.mbLambda_nonneg d hN
  have hI := fun j => MBound.mbConstI_nonneg d _ _ hΛ (MZero.mzeroConst_nonneg d) j
  have hc7 : 0 ≤ Apriori.aprC7 d := by
    unfold Apriori.aprC7
    have := (vsCK_pos d).le
    have := d.one_le_C1pp
    have := d.cm_pos
    positivity
  have hCS := Apriori.constS_nonneg d
  have hC0 : 0 ≤ d.C0 + 1 := by linarith [d.C0_ge_one]
  have hCwc : 0 ≤ d.Cwc := by linarith [d.one_le_Cwc]
  have hs := Finset.sum_nonneg fun i (_ : i ∈ Finset.Ioo 1 (k + 1)) =>
    mul_nonneg (hI i) (hI (k - i + 2))
  unfold eMI Apriori.extraConst
  have := hI k
  positivity

/-- Forcing constant, non-saturated averaged chains `k = n+2`: `C_av C_P^k iF(1-β_k)`. -/
def fAvC (d : VSData) (P : PsiData (p.n * p.W)) (LamM e : ℝ) (n : ℕ) (T : ℝ) : ℝ :=
  avConst d (fun _ => LamM) e (n + 2) * kernelActionConst d ^ (n + 2) *
    intF d P (1 - lossBeta (n + 2)) T

/-- Forcing constant, averaged `k = 1`: `C_av C_7 iF(1-β_1)`. -/
def fAvOneC (d : VSData) (P : PsiData (p.n * p.W)) (LamM e : ℝ) (T : ℝ) : ℝ :=
  avConst d (fun _ => LamM) e 1 * (1 + vsCK d * d.C1pp / d.cm) * intF d P (1 - lossBeta 1) T

/-- Forcing constant, isotropic `k = n+2`: `C_iso C_P^{k-1} iF(1/2-α_k)`. -/
def fIsoC (d : VSData) (P : PsiData (p.n * p.W)) (LamM : ℝ) (n : ℕ) (T : ℝ) : ℝ :=
  isoConst d (fun _ => LamM) (n + 2) * kernelActionConst d ^ (n + 1) *
    intF d P (1 / 2 - lossAlpha (n + 2)) T

/-- Forcing constant, isotropic `k = 1`: `C_iso iF(0)`. -/
def fIsoOneC (d : VSData) (P : PsiData (p.n * p.W)) (LamM : ℝ) (T : ℝ) : ℝ :=
  isoConst d (fun _ => LamM) 1 * 1 * intF d P (0 - lossAlpha 1) T

/-- Noise constant, averaged non-saturated chains (`k = n+2`): `k C_P^k √(𝔠 Λ³ iF(2-2β_k))`. -/
def mAvC (d : VSData) (P : PsiData (p.n * p.W)) (LamM : ℝ) (n : ℕ) (T : ℝ) : ℝ :=
  ((n : ℝ) + 2) * kernelActionConst d ^ (n + 2) *
    Real.sqrt (qvC d * LamM ^ 3 * intF d P (2 - 2 * lossBeta (n + 2)) T)

/-- Noise constant, M1 at `k = 1`: `C_7 √(𝔠 Λ³ iF(2-2β_1))`. -/
def mAvOneC (d : VSData) (P : PsiData (p.n * p.W)) (LamM : ℝ) (T : ℝ) : ℝ :=
  ((0 : ℝ) + 1) * (1 + vsCK d * d.C1pp / d.cm) *
    Real.sqrt (qvC d * LamM ^ 3 * intF d P (2 - 2 * lossBeta 1) T)

/-- Noise constant, isotropic chains (`k = n+2`): `k C_P^{k-1} √(𝔠 Λ³ iF(1-2α_k))`. -/
def mIsoC (d : VSData) (P : PsiData (p.n * p.W)) (LamM : ℝ) (n : ℕ) (T : ℝ) : ℝ :=
  ((n : ℝ) + 2) * kernelActionConst d ^ (n + 1) *
    Real.sqrt (qvC d * LamM ^ 3 * intF d P (1 - 2 * lossAlpha (n + 2)) T)

/-- Noise constant, isotropic chains (`k = 1`): `√(𝔠 Λ³ iF(0))`. -/
def mIsoOneC (d : VSData) (P : PsiData (p.n * p.W)) (LamM : ℝ) (T : ℝ) : ℝ :=
  1 * Real.sqrt (qvC d * LamM ^ 3 * intF d P 0 T)

/-- Noise constant, saturated averaged chains (`k = n+1`): `k √(𝔠 Λ³ iF(k-2β_k))`. -/
def mSatC (d : VSData) (P : PsiData (p.n * p.W)) (LamM : ℝ) (n : ℕ) (T : ℝ) : ℝ :=
  ((n : ℝ) + 1) * Real.sqrt (qvC d * LamM ^ 3 * intF d P ((n : ℝ) + 1 - 2 * lossBeta (n + 1)) T)

/-!
## The variance identity
-/

/-- `K² Q φ² L_p s² y = (K √(Q I) φ (L_b s))²` when `L_p y = L_b² I`. -/
theorem sq_noise {K Q φ Lp s y I Lb : ℝ} (hQI : 0 ≤ Q * I) (hLy : Lp * y = Lb ^ 2 * I) :
    K ^ 2 * Q * φ ^ 2 * Lp * s ^ 2 * y = (K * Real.sqrt (Q * I) * φ * (Lb * s)) ^ 2 := by
  rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hQI]
  linear_combination (K ^ 2 * Q * φ ^ 2 * s ^ 2) * hLy

/-- `L_T^a y_γ = (L_T^b)² iF(γ)` when `a - γ = 2b`. -/
theorem lp_y (d : VSData) (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {T : ℝ} (hT1 : T ≤ 1) (a : ℕ)
    {b γ : ℝ} (h : (a : ℝ) - γ = 2 * b) :
    P.lEta T ^ a * qvIntRule d P γ T = (P.lEta T ^ b) ^ 2 * intF d P γ T := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hL := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) (hz.im_pos hN) hT1
  rw [← Real.rpow_natCast, rpow_mul_qvIntRule d P hPW hz hT1, h, ← Real.rpow_natCast
    (P.lEta T ^ b), ← Real.rpow_mul hL.le]
  push_cast
  ring_nf

theorem qvC_mul_intF_pos (d : VSData) (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {T γ LamM : ℝ} (hT1 : T ≤ 1)
    (hγ : 0 ≤ γ) (hLam : 1 ≤ LamM) : 0 < qvC d * LamM ^ 3 * intF d P γ T := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hL := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) (hz.im_pos hN) hT1
  have h1 := qvC_pos d
  have h2 : 0 < intF d P γ T :=
    mul_pos (Real.rpow_pos_of_pos hL _) (qvIntRule_pos d hPW hz hγ hT1)
  have h3 : (0 : ℝ) < LamM := by linarith
  positivity

/-!
## The tail and the event inclusion
-/

/-- `-(r√Q)²/(4Q) = -r²/4` for `Q > 0`. -/
theorem mi_tail {Q r : ℝ} (hQ : 0 < Q) :
    (r * Real.sqrt Q) ^ 2 / (4 * Q) = r ^ 2 / 4 := by
  rw [mul_pow, Real.sq_sqrt hQ.le]
  field_simp

/-- **The event inclusion with a good event**.
If a.s. on `{T ≤ τ} ∩ G`,
`X ≤ F den + mg_T`, and `F + λ/den ≤ bnd`, `den > 0`, then
`ν{T ≤ τ, bnd ≤ X/den} ≤ ν{∃ t ≤ T, t ≤ τ, λ ≤ mg_t} + ν{T ≤ τ, ¬G}`.
-/
theorem mi_event_le' {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (τ : Ω → WithTop ℝ≥0)
    (T : ℝ≥0) (X : Ω → ℝ) (mg : ℝ≥0 → Ω → ℝ) (G : Ω → Prop) {F lam den bnd : ℝ}
    (hden : 0 < den) (hbnd : F + lam / den ≤ bnd)
    (h : ∀ᵐ x ∂ν, (T : WithTop ℝ≥0) ≤ τ x → G x → X x ≤ F * den + mg T x) :
    ν {x | (T : WithTop ℝ≥0) ≤ τ x ∧ bnd ≤ X x / den} ≤
      ν {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧ lam ≤ mg t x} +
        ν {x | (T : WithTop ℝ≥0) ≤ τ x ∧ ¬ G x} := by
  refine le_trans (measure_mono_ae ?_) (measure_union_le _ _)
  filter_upwards [h] with x hx
  rintro ⟨hT, hb⟩
  by_cases hG : G x
  · left
    refine ⟨T, le_rfl, hT, ?_⟩
    by_contra hlt0
    have hlt := lt_of_not_ge hlt0
    have h1 := hx hT hG
    have h2 : X x / den < F + lam / den := by
      rw [div_lt_iff₀ hden, add_mul, div_mul_cancel₀ _ hden.ne']
      linarith
    linarith
  · exact Or.inr ⟨hT, hG⟩

/-- **The event inclusion**:
`mi_event_le'` with `G = True`.
-/
theorem mi_event_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (τ : Ω → WithTop ℝ≥0)
    (T : ℝ≥0) (X : Ω → ℝ) (mg : ℝ≥0 → Ω → ℝ) {F lam den bnd : ℝ}
    (hden : 0 < den) (hbnd : F + lam / den ≤ bnd)
    (h : ∀ᵐ x ∂ν, (T : WithTop ℝ≥0) ≤ τ x → X x ≤ F * den + mg T x) :
    ν {x | (T : WithTop ℝ≥0) ≤ τ x ∧ bnd ≤ X x / den} ≤
      ν {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧ lam ≤ mg t x} := by
  have h' := mi_event_le' ν τ T X mg (fun _ => True) hden hbnd
    (h.mono fun x hx hT _ => hx hT)
  have h0 : ν {x | (T : WithTop ℝ≥0) ≤ τ x ∧ ¬ (fun _ => True) x} = 0 := by
    simp
  rwa [h0, add_zero] at h'

/-!
## Small facts
-/

/-- `𝒴_0 = 0` along the path: `H_0 = 0` and `𝒴^k_0(0) = 0` (`k ≥ 1`). -/
theorem isoErr_pathH_zero {P : PsiData (p.n * p.W)} {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool)
    (a b : Fin (p.n * p.W)) (ω : Stochastic.RingSample p) :
    (fun x => P.isoErr σ a b x 0 (Evol.pathH p ω 0)) = 0 := by
  funext x
  rw [Evol.pathH, Real.toNNReal_zero, VS.vsBandFin_zero]
  exact Discharge.isoErr_zero_uncond P hk σ a b x

/-- `s ≤ T ≤ τ` gives `s⁺ ≤ τ`. -/
theorem le_tau_of_le {τ : WithTop ℝ≥0} {T : ℝ≥0} (hT : (T : WithTop ℝ≥0) ≤ τ) {s : ℝ}
    (hs : s ≤ T) : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ :=
  le_trans (WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hs)) hT

end BlockBand.Native.ErdosRiabov.MI
