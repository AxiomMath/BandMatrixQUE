module

public import BlockBand.Native.ErdosRiabov.MI.Forcing

/-!
# Master inequalities: the forcing integrals of the five families

Deterministic bounds on the propagated forcing integrals of the averaged, isotropic and saturated
chains.

Hypotheses: VS data, `ψ ≥ 1`, `Λ ≥ 1`, and **at every `s ∈ (0, T]`** the a priori input
`QV.APriori P ψ^I ψ^A Λ s (H s)` (on `{T ≤ τ}` it is `Apriori.qvAPriori_of_le_tau`); for
averaged `2 ≤ k ≤ 7` also the extra `M`-bound `ExtraBAt P s k e` on `(0, T]`
(`Apriori.mbounds_extra_uncond`). With `C_av = avConst d Λ e k`, `C_iso = isoConst d Λ k`,
`Φ = Φ^{f}_k(ψ, L_T, Y_T)` (`phiAvF`/`phiIsoF`) and `iF = MI.intF`:
* `forcingInt_avGen`/`forcingInt_isoGen`: any propagator `U` with
  `Σ_α |U(s)(u,α)| s_s(α) ≤ K (L_T/L_s)^c s_T(u)` on `(0,T]` (`c ≥ β_k` resp. `α_k`);
* `forcingInt_av` (`k = n+2`, `HasDesatFactor σ`, `U = ⊗P̂`, `K = C_P^k`, `c = 1`),
  `forcingInt_av_one` (`k = 1`, `K = C_7`, `c = 1`), `forcingInt_iso` (`k = n+2`,
  `K = C_P^{k-1}`, `c = 1/2`), `forcingInt_iso_one` (`k = 1`, `U = I`, `K = 1`, `c = 0`);
* `forcingInt_sat` (`k = n+1`, any σ, `U = I`, integrand `T̂^{⊕k}_s[𝒳_s] + 𝓕^av_s`): if
  `η_s |T̂^{⊕k}_s[𝒳_s](u)| ≤ B L_s^{β_k} s^av_s(u)` on `(0, T]`, the integral is
  `≤ (B + C_av Φ) iF(k/2 - β_k) L_T^{β_k} s^av_T(u)`.
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
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Forcing
open BlockBand.Native.ErdosRiabov.QV
open BlockBand.Native.ErdosRiabov.VS (RingMat)
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open Expo (lossAlpha lossBeta)
open scoped ComplexConjugate

variable {p : BlockBand.Parameters}

/-- The forcing constants are nonnegative. -/
theorem avConst_nonneg (d : VSData) {LamM e : ℝ} (hLam : 0 ≤ LamM) (he : 0 ≤ e) (k : ℕ) :
    0 ≤ avConst d (fun _ => LamM) e k := by
  have h0 := one_le_ibar (I := fun _ => LamM) (fun _ => hLam)
  have h1 := d.one_le_Cwc
  have h2 : 0 ≤ Real.sqrt d.C1pp := Real.sqrt_nonneg _
  have h3 : 0 ≤ constS d := Real.rpow_nonneg (by positivity) _
  have h4 : 0 ≤ d.C0 + 1 := by linarith [d.C0_ge_one]
  have h5 : 0 ≤ ibar (fun _ => LamM) := by linarith
  unfold avConst cAv
  positivity

theorem isoConst_nonneg (d : VSData) {LamM : ℝ} (hLam : 0 ≤ LamM) (k : ℕ) :
    0 ≤ isoConst d (fun _ => LamM) k := by
  have h0 := one_le_ibar (I := fun _ => LamM) (fun _ => hLam)
  have h1 := d.one_le_Cwc
  have h1' := d.one_le_C1pp
  have h2 : 0 ≤ Real.sqrt d.C1pp := Real.sqrt_nonneg _
  have h4 : 0 ≤ d.C0 + 1 := by linarith [d.C0_ge_one]
  have h5 : 0 ≤ ibar (fun _ => LamM) := by linarith
  have h6 := (vsCK_pos d).le
  unfold isoConst cIso
  positivity

section Fam

variable (d : VSData) {P : PsiData (p.n * p.W)} (hb : d.b = p.b)
  (hPS : P.S = shortRingProfile p.b p.n p.W) (hPW : P.W = p.W) (hPD : P.D = d.D)
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2)
  {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) {psiI psiA : ℕ → ℝ} (hpsi : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n)
  {LamM : ℝ} (hLam : 1 ≤ LamM) (H : ℝ → RingMat p)
  (hAP : ∀ s ∈ Ioc (0 : ℝ) T, QV.APriori P psiI psiA LamM s (H s))

include hb hPS hPW hPD hz hP6 hT0 hT1 in
/-- The single-time context at `T` (`FCtx`, `1 ≤ L_T`). -/
theorem mi_atT : FCtx d P T := by
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hPS' : P.S = shortRingProfile d.b p.n p.W := by rw [hPS, hb]
  exact fctx_of d p.n_ge_four p.W_pos hz hT0 hT1 P hPW hPD hPS' rfl (hF.one_le T ⟨hT0, le_rfl⟩)

include hb hPS hPW hPD hz hP6 hT0 hT1 hpsi hAP in
/-- The single-time inputs at `s ∈ (0,T]`: `FCtx`, `Forcing.APriori` and `Forcing.IsoBAt`,
`L_T ≤ L_s`,
`Y_s ≤ Y_T`, `0 < L_T`, `QVInputs`, `Υ_s ≤ Υ_T`. -/
theorem mi_at {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) T) :
    FCtx d P s ∧ Forcing.APriori P s (H s) psiI psiA ∧ (∀ n ∈ kRange, IsoBAt P s n LamM) ∧
      P.lEta T ≤ P.lEta s ∧ yScale P s ≤ yScale P T ∧ 0 < P.lEta T ∧ QVInputs d P s ∧
      (∀ x y, P.ups s x y ≤ P.ups T x y) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hη := hz.im_pos hN
  have hF := qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have hPS' : P.S = shortRingProfile d.b p.n p.W := by rw [hPS, hb]
  exact ⟨fctx_of d p.n_ge_four p.W_pos hz hs.1.le hs1 P hPW hPD hPS' rfl (hF.one_le s hsI),
    fAPriori_of hN hW hη hs1 hpsi (hAP s hs), isoBAt_of (hAP s hs), hF.anti s hsI,
    yScale_anti P hN hW hη hs.2 hT1, (hF.inputs T ⟨hT0, le_rfl⟩).lEta_pos, hF.inputs s hsI,
    hF.upsMono s hsI⟩

include hb hPS hPW hPD hz hP6 hT0 hT1 hpsi hLam hAP

/-- The averaged forcing at `s ∈ (0,T]` with `Φ` at time `T`:
`η_s |𝓕^av_s(y)| ≤ C_av (L_s^{β_k} s^av_s(y)) Φ_T` (`forcing_av` and monotonicity in time). -/
theorem forcingAv_le_T {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 8) {e : ℝ} (he0 : 0 ≤ e)
    (hE : 2 ≤ k → k ≤ 7 → ∀ s ∈ Ioc (0 : ℝ) T, ExtraBAt P s k e) (σ : Fin k → Bool)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) T) (y : Fin k → Fin (p.n * p.W)) :
    vsHeight P.z s * ‖forcingAv P σ y s (H s)‖ ≤
      avConst d (fun _ => LamM) e k * (P.lEta s ^ lossBeta k * P.sAv y s) *
        phiAvF psiI psiA (P.lEta T) (yScale P T) k := by
  obtain ⟨c, hAPs, hIs, hLTs, hYs, hLT, -, -⟩ := mi_at d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi H hAP hs
  have hpsi0 : ∀ n, 0 ≤ psiI n ∧ 0 ≤ psiA n := fun n =>
    ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
  have h := Discharge.forcing_av_uncond c hAPs hpsi hIs (fun _ => by linarith) he0
    (fun h2 h7 => hE h2 h7 s hs) hk1 hk σ y
  have h0 : 0 ≤ P.lEta s ^ lossBeta k * P.sAv y s :=
    mul_nonneg (Real.rpow_nonneg c.lEta_pos.le _) (sAv_pos c y).le
  exact h.trans (mul_le_mul_of_nonneg_left (phiAvF_anti hpsi0 hLT hLTs hYs hk)
    (mul_nonneg (avConst_nonneg d (by linarith) he0 k) h0))

/-- The isotropic forcing at `s ∈ (0,T]` with `Φ` at time `T`:
`η_s |𝓕^iso_s(a,y,b)| ≤ C_iso (L_s^{α_k} s^iso_s) Φ_T` (`forcing_iso` and monotonicity in
time). -/
theorem forcingIso_le_T {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 8) (σ : Fin k → Bool)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) T) (a b : Fin (p.n * p.W)) (y : Fin k → Fin (p.n * p.W)) :
    vsHeight P.z s * ‖forcingIso P σ a b y s (H s)‖ ≤
      isoConst d (fun _ => LamM) k * (P.lEta s ^ lossAlpha k * P.sIso a b y s) *
        phiIsoF psiI psiA (P.lEta T) (yScale P T) k := by
  obtain ⟨c, hAPs, hIs, hLTs, hYs, hLT, -, -⟩ := mi_at d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi H hAP hs
  have hpsi0 : ∀ n, 0 ≤ psiI n ∧ 0 ≤ psiA n := fun n =>
    ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
  have h := forcing_iso c hAPs hpsi hIs (fun _ => by linarith) hk1 hk σ y a b
  have h0 : 0 ≤ P.lEta s ^ lossAlpha k * P.sIso a b y s :=
    mul_nonneg (Real.rpow_nonneg c.lEta_pos.le _) (sIso_pos c a b y).le
  exact h.trans (mul_le_mul_of_nonneg_left (phiIsoF_anti hpsi0 hLT hLTs hYs hk)
    (mul_nonneg (isoConst_nonneg d (by linarith) k) h0))

/-- **Forcing integral, averaged chains, any propagator**: if on `(0,T]`
`Σ_α |U(s)(u,α)| s^av_s(α) ≤ K (L_T/L_s)^c s^av_T(u)` (`K ≥ 0`, `β_k ≤ c`), then
`|(∫_0^T U(s) 𝓕^av_s ds)(u)| ≤ C_av K iF(c - β_k) Φ_T L_T^{β_k} s^av_T(u)`.
-/
theorem forcingInt_avGen {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 8) {e : ℝ} (he0 : 0 ≤ e)
    (hE : 2 ≤ k → k ≤ 7 → ∀ s ∈ Ioc (0 : ℝ) T, ExtraBAt P s k e) (σ : Fin k → Bool)
    (u : Fin k → Fin (p.n * p.W))
    (U : ℝ → Matrix (Fin k → Fin (p.n * p.W)) (Fin k → Fin (p.n * p.W)) ℂ) {K c : ℝ}
    (hK : 0 ≤ K) (hc : lossBeta k ≤ c)
    (hG : ∀ s ∈ Ioc (0 : ℝ) T,
      ∑ α, ‖U s u α‖ * P.sAv α s ≤ K * (P.lEta T / P.lEta s) ^ c * P.sAv u T) :
    ‖(∫ s in (0 : ℝ)..T, propOp (U s) (fun y => forcingAv P σ y s (H s))) u‖ ≤
      avConst d (fun _ => LamM) e k * K * intF d P (c - lossBeta k) T *
        phiAvF psiI psiA (P.lEta T) (yScale P T) k * (P.lEta T ^ lossBeta k * P.sAv u T) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hη := hz.im_pos hN
  have cT := mi_atT d hb hPS hPW hPD hz hP6 hT0 hT1
  have hpsi0 : ∀ n, 0 ≤ psiI n ∧ 0 ≤ psiA n := fun n =>
    ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
  set C := avConst d (fun _ => LamM) e k
  set Φ := phiAvF psiI psiA (P.lEta T) (yScale P T) k
  have hC0 : 0 ≤ C := avConst_nonneg d (by linarith) he0 k
  have hΦ0 : 0 ≤ Φ := phiAvF_nonneg hpsi0 cT.lEta_pos.le (yScale_pos cT).le k
  have hsT := P.sAv_pos hN hW hη hT1 u
  have hD : 0 ≤ C * K * Φ * P.sAv u T := by positivity
  refine (forcingInt_core d P hPW hz _ u hT0 hT1 (e := lossBeta k) (c := c) hD (by linarith)
    fun s hs => ?_).trans (le_of_eq (by ring))
  have hηs := vsHeight_pos hη (hs.2.trans hT1)
  have hLs := P.lEta_pos hN hW hη (hs.2.trans hT1)
  have h := pt_propOp (U s) (fun y => forcingAv P σ y s (H s)) (fun α => P.sAv α s) u hηs
    (by have := Real.rpow_nonneg hLs.le (lossBeta k); positivity)
    (fun α => forcingAv_le_T d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi hLam H hAP hk1 hk he0 hE σ hs α)
    (hG s hs)
  refine h.trans (le_of_eq ?_)
  ring

/-- **Forcing integral, isotropic chains, any propagator**: if on `(0,T]`
`Σ_α |U(s)(u,α)| s^iso_s(a,α,b) ≤ K (L_T/L_s)^c s^iso_T(a,u,b)` (`K ≥ 0`, `α_k ≤ c`), then
`|(∫_0^T U(s) 𝓕^iso_s ds)(u)| ≤ C_iso K iF(c - α_k) Φ_T L_T^{α_k} s^iso_T(a,u,b)`.
-/
theorem forcingInt_isoGen {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 8) (σ : Fin k → Bool)
    (a b : Fin (p.n * p.W)) (u : Fin k → Fin (p.n * p.W))
    (U : ℝ → Matrix (Fin k → Fin (p.n * p.W)) (Fin k → Fin (p.n * p.W)) ℂ) {K c : ℝ}
    (hK : 0 ≤ K) (hc : lossAlpha k ≤ c)
    (hG : ∀ s ∈ Ioc (0 : ℝ) T,
      ∑ α, ‖U s u α‖ * P.sIso a b α s ≤ K * (P.lEta T / P.lEta s) ^ c * P.sIso a b u T) :
    ‖(∫ s in (0 : ℝ)..T, propOp (U s) (fun y => forcingIso P σ a b y s (H s))) u‖ ≤
      isoConst d (fun _ => LamM) k * K * intF d P (c - lossAlpha k) T *
        phiIsoF psiI psiA (P.lEta T) (yScale P T) k *
          (P.lEta T ^ lossAlpha k * P.sIso a b u T) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hη := hz.im_pos hN
  have cT := mi_atT d hb hPS hPW hPD hz hP6 hT0 hT1
  have hpsi0 : ∀ n, 0 ≤ psiI n ∧ 0 ≤ psiA n := fun n =>
    ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
  set C := isoConst d (fun _ => LamM) k
  set Φ := phiIsoF psiI psiA (P.lEta T) (yScale P T) k
  have hC0 : 0 ≤ C := isoConst_nonneg d (by linarith) k
  have hΦ0 : 0 ≤ Φ := phiIsoF_nonneg hpsi0 cT.lEta_pos.le (yScale_pos cT).le k
  have hsT := P.sIso_pos hN hW hη hT1 a b u
  have hD : 0 ≤ C * K * Φ * P.sIso a b u T := by positivity
  refine (forcingInt_core d P hPW hz _ u hT0 hT1 (e := lossAlpha k) (c := c) hD (by linarith)
    fun s hs => ?_).trans (le_of_eq (by ring))
  have hηs := vsHeight_pos hη (hs.2.trans hT1)
  have hLs := P.lEta_pos hN hW hη (hs.2.trans hT1)
  have h := pt_propOp (U s) (fun y => forcingIso P σ a b y s (H s)) (fun α => P.sIso a b α s) u
    hηs (by have := Real.rpow_nonneg hLs.le (lossAlpha k); positivity)
    (fun α => forcingIso_le_T d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi hLam H hAP hk1 hk σ hs a b α)
    (hG s hs)
  refine h.trans (le_of_eq ?_)
  ring

/-- **Forcing integral, non-saturated averaged chains** (`k = n+2 ≤ 8`, `HasDesatFactor σ`): with
`U = vsTensorProp (μ^av, μ^next)` (`Evol.duhamel_av`),
`|(∫_0^T U(s,T) 𝓕^av_s ds)(u)| ≤ C_av C_P^k iF(1-β_k) Φ_T L_T^{β_k} s^av_T(u)`.
-/
theorem forcingInt_av {n : ℕ} (hn : n + 2 ≤ 8) {e : ℝ} (he0 : 0 ≤ e)
    (hE : 2 ≤ n + 2 → n + 2 ≤ 7 → ∀ s ∈ Ioc (0 : ℝ) T, ExtraBAt P s (n + 2) e)
    (σ : Fin (n + 2) → Bool) (hσ : HasDesatFactor σ) (u : Fin (n + 2) → Fin (p.n * p.W)) :
    ‖(∫ s in (0 : ℝ)..T, propOp (vsTensorProp P.S (muAv P σ) (muNext P σ) s T)
        (fun y => forcingAv P σ y s (H s))) u‖ ≤
      avConst d (fun _ => LamM) e (n + 2) * kernelActionConst d ^ (n + 2) *
        intF d P (1 - lossBeta (n + 2)) T *
        phiAvF psiI psiA (P.lEta T) (yScale P T) (n + 2) *
          (P.lEta T ^ lossBeta (n + 2) * P.sAv u T) :=
  forcingInt_avGen d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi hLam H hAP (by omega) hn he0 hE σ u _
    (pow_nonneg (by linarith [kernelActionConst_ge_one d]) _)
    (qv_beta_le_one (k := n + 2) hn) fun s hs => by
      rw [Real.rpow_one]
      exact evol_goodProps_av d P hb hPS hPW hPD hz hs.1.le hs.2 hT1 σ hσ u

/-- **Forcing integral, averaged `k = 1`** (`U = P̂`, every one-letter pattern non-saturated):
`≤ C_av C_7 iF(1-β_1) Φ_T L_T^{β_1} s^av_T(u)`, `C_7 = 1 + C_K C₁''/c_m`
(`evol_goodProps_av_one`).
-/
theorem forcingInt_av_one {e : ℝ} (he0 : 0 ≤ e) (σ : Fin 1 → Bool)
    (u : Fin 1 → Fin (p.n * p.W)) :
    ‖(∫ s in (0 : ℝ)..T, propOp (vsTensorProp P.S (muAv P σ) (muNext P σ) s T)
        (fun y => forcingAv P σ y s (H s))) u‖ ≤
      avConst d (fun _ => LamM) e 1 * (1 + vsCK d * d.C1pp / d.cm) *
        intF d P (1 - lossBeta 1) T * phiAvF psiI psiA (P.lEta T) (yScale P T) 1 *
          (P.lEta T ^ lossBeta 1 * P.sAv u T) :=
  forcingInt_avGen d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi hLam H hAP le_rfl (by norm_num) he0
    (fun h => absurd h (by norm_num)) σ u _
    (by have := (vsCK_pos d).le; have := d.one_le_C1pp; have := d.cm_pos; positivity)
    (qv_beta_le_one (k := 1) (by norm_num)) fun s hs => by
      rw [Real.rpow_one]
      exact evol_goodProps_av_one d P hb hPS hPW hz hs.1.le hs.2 hT1 σ u

/-- **Forcing integral, isotropic chains** (`k = n+2 ≤ 8`): with
`U = vsTensorProp (μ^iso, μ^next)` (`Evol.duhamel_iso`, last factor `I`),
`|(∫_0^T U(s,T) 𝓕^iso_s ds)(u)| ≤ C_iso C_P^{k-1} iF(1/2-α_k) Φ_T L_T^{α_k} s^iso_T(a,u,b)`.
-/
theorem forcingInt_iso {n : ℕ} (hn : n + 2 ≤ 8) (σ : Fin (n + 2) → Bool)
    (a b : Fin (p.n * p.W)) (u : Fin (n + 2) → Fin (p.n * p.W)) :
    ‖(∫ s in (0 : ℝ)..T, propOp (vsTensorProp P.S (muIso P σ) (muNext P σ) s T)
        (fun y => forcingIso P σ a b y s (H s))) u‖ ≤
      isoConst d (fun _ => LamM) (n + 2) * kernelActionConst d ^ (n + 1) *
        intF d P (1 / 2 - lossAlpha (n + 2)) T *
        phiIsoF psiI psiA (P.lEta T) (yScale P T) (n + 2) *
          (P.lEta T ^ lossAlpha (n + 2) * P.sIso a b u T) :=
  forcingInt_isoGen d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi hLam H hAP (by omega) hn σ a b u _
    (pow_nonneg (by linarith [kernelActionConst_ge_one d]) _)
    (qv_alpha_le_half (k := n + 2) hn) fun s hs => by
      rw [← Real.sqrt_eq_rpow]
      exact evol_goodProps_iso d P hb hPS hPW hPD hz hs.1.le hs.2 hT1 σ a b u

/-- **Forcing integral, isotropic `k = 1`** (`U = I`, `qv_tensorProp_iso_one`):
`≤ C_iso iF(0) Φ_T s^iso_T(a,u,b)` (`α_1 = 0`;
`iF(0) = c_m⁻¹ log((C₀+1)N)`).
-/
theorem forcingInt_iso_one (σ : Fin 1 → Bool) (a b : Fin (p.n * p.W))
    (u : Fin 1 → Fin (p.n * p.W)) :
    ‖(∫ s in (0 : ℝ)..T, propOp (vsTensorProp P.S (muIso P σ) (muNext P σ) s T)
        (fun y => forcingIso P σ a b y s (H s))) u‖ ≤
      isoConst d (fun _ => LamM) 1 * 1 * intF d P (0 - lossAlpha 1) T *
        phiIsoF psiI psiA (P.lEta T) (yScale P T) 1 *
          (P.lEta T ^ lossAlpha 1 * P.sIso a b u T) :=
  forcingInt_isoGen d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi hLam H hAP le_rfl (by norm_num) σ a b
    u _ zero_le_one (le_of_eq (qv_alpha_of_le_four (by norm_num))) fun s hs => by
      obtain ⟨-, -, -, hLTs, -, hLT, hin, hup⟩ :=
        mi_at d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi H hAP hs
      simp only [qv_tensorProp_iso_one]
      rw [qv_sum_delta u, Real.rpow_zero, one_mul, one_mul]
      have h := qv_sIso_sq_time_le P hin.nonneg hup hLT hLTs (n := 0) a b u
      rw [pow_zero, one_mul] at h
      have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
      have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
      exact (pow_le_pow_iff_left₀ (P.sIso_pos hN hW (hz.im_pos hN) (hs.2.trans hT1) a b u).le
        (P.sIso_pos hN hW (hz.im_pos hN) hT1 a b u).le two_ne_zero).mp h

/-- **Forcing integral, saturated averaged chains** (`k = n+1 ≤ 8`, any pattern, `U = I`): for the
integrand `T̂^{⊕k}_s[𝒳_s] + 𝓕^av_s` of `Circ.duhamel_av_sat_combMg`
(`T̂^{⊕k}_s = propOp (vsTensorGen P.S m m̄ s)`), if on `(0,T]`
`η_s |T̂^{⊕k}_s[𝒳_s](u)| ≤ B L_s^{β_k} s^av_s(u)`, then
`|(∫_0^T (T̂^{⊕k}_s[𝒳_s] + 𝓕^av_s) ds)(u)| ≤ (B + C_av Φ_T) iF(k/2 - β_k) L_T^{β_k} s^av_T(u)`.
-/
theorem forcingInt_sat {n : ℕ} (hn : n + 1 ≤ 8) {e : ℝ} (he0 : 0 ≤ e)
    (hE : 2 ≤ n + 1 → n + 1 ≤ 7 → ∀ s ∈ Ioc (0 : ℝ) T, ExtraBAt P s (n + 1) e)
    (σ : Fin (n + 1) → Bool) (u : Fin (n + 1) → Fin (p.n * p.W)) {B : ℝ} (hB : 0 ≤ B)
    (hlin : ∀ s ∈ Ioc (0 : ℝ) T, vsHeight P.z s *
      ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s)
        (fun y => P.avErr σ y s (H s)) u‖ ≤ B * (P.lEta s ^ lossBeta (n + 1) * P.sAv u s)) :
    ‖(∫ s in (0 : ℝ)..T,
        propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s)
            (fun y => P.avErr σ y s (H s)) +
          fun y => forcingAv P σ y s (H s)) u‖ ≤
      (B + avConst d (fun _ => LamM) e (n + 1) *
          phiAvF psiI psiA (P.lEta T) (yScale P T) (n + 1)) *
        intF d P (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) T *
          (P.lEta T ^ lossBeta (n + 1) * P.sAv u T) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hη := hz.im_pos hN
  have cT := mi_atT d hb hPS hPW hPD hz hP6 hT0 hT1
  have hpsi0 : ∀ n, 0 ≤ psiI n ∧ 0 ≤ psiA n := fun n =>
    ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
  set C := avConst d (fun _ => LamM) e (n + 1)
  set Φ := phiAvF psiI psiA (P.lEta T) (yScale P T) (n + 1)
  set β := lossBeta (n + 1)
  have hC0 : 0 ≤ C := avConst_nonneg d (by linarith) he0 _
  have hΦ0 : 0 ≤ Φ := phiAvF_nonneg hpsi0 cT.lEta_pos.le (yScale_pos cT).le _
  have hsT := P.sAv_pos hN hW hη hT1 u
  have hD : 0 ≤ (B + C * Φ) * P.sAv u T := by positivity
  have hce : 0 ≤ ((n : ℝ) + 1) / 2 - β := by
    by_cases h0 : n = 0
    · subst h0
      have : β = 0 := by
        simp only [β]
        rw [lossBeta_eq (by norm_num), qv_alpha_of_le_four (by norm_num)]
      rw [this]; norm_num
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      linarith [qv_beta_le_one (k := n + 1) hn]
  refine (forcingInt_core d P hPW hz _ u hT0 hT1 (e := β) (c := ((n : ℝ) + 1) / 2) hD hce
    fun s hs => ?_).trans (le_of_eq (by ring))
  obtain ⟨-, -, -, hLTs, -, hLT, hin, hup⟩ := mi_at d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi H hAP hs
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have hηs := vsHeight_pos hη hs1
  have hLs := P.lEta_pos hN hW hη hs1
  have hss := P.sAv_pos hN hW hη hs1 u
  -- `s^av_s(u) ≤ (L_T/L_s)^{k/2} s^av_T(u)`
  have hsz : P.sAv u s ≤ (P.lEta T / P.lEta s) ^ (((n : ℝ) + 1) / 2) * P.sAv u T := by
    have h := qv_sAv_sq_time_le P hin.nonneg hup hLT hLTs u
    have hr : 0 ≤ P.lEta T / P.lEta s := div_nonneg hLT.le hLs.le
    have e1 : ((P.lEta T / P.lEta s) ^ (((n : ℝ) + 1) / 2) * P.sAv u T) ^ 2 =
        (P.lEta T / P.lEta s) ^ (n + 1) * P.sAv u T ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast ((P.lEta T / P.lEta s) ^ (((n : ℝ) + 1) / 2)) 2,
        ← Real.rpow_mul hr, ← Real.rpow_natCast (P.lEta T / P.lEta s) (n + 1)]
      push_cast
      ring_nf
    rw [← e1] at h
    exact (pow_le_pow_iff_left₀ hss.le (by positivity) two_ne_zero).mp h
  have hF := forcingAv_le_T d hb hPS hPW hPD hz hP6 hT0 hT1 hpsi hLam H hAP (by omega) hn he0 hE
    σ hs u
  have hl := hlin s hs
  have hLb := Real.rpow_nonneg hLs.le β
  calc vsHeight P.z s * ‖(propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
        (fun _ => conj (semicircleM P.z)) s) (fun y => P.avErr σ y s (H s)) +
          fun y => forcingAv P σ y s (H s)) u‖
      ≤ vsHeight P.z s * ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
          (fun _ => conj (semicircleM P.z)) s) (fun y => P.avErr σ y s (H s)) u‖ +
        vsHeight P.z s * ‖forcingAv P σ u s (H s)‖ := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hηs.le
    _ ≤ (B + C * Φ) * P.lEta s ^ β * P.sAv u s := by nlinarith
    _ ≤ (B + C * Φ) * P.lEta s ^ β *
        ((P.lEta T / P.lEta s) ^ (((n : ℝ) + 1) / 2) * P.sAv u T) :=
        mul_le_mul_of_nonneg_left hsz (by positivity)
    _ = _ := by ring

end Fam

end BlockBand.Native.ErdosRiabov.MI
