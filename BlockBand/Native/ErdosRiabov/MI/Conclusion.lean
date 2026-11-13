module

public import BlockBand.Native.ErdosRiabov.MI.Absorb
public import BlockBand.Native.ErdosRiabov.ZigProof.PhiBridge

/-!
# the master inequality: `ZigProof.MasterIneqPhi` from the saturated case

Probability: `driverLaw model.law`.

* `miA d k`: an explicit constant (VS data and `k` only) with `C_F, C_M ≤ miA d k ℓ_N^{757}`
  for the four non-saturated families (`fAvC_le`, `mAvC_le`, …); `miN0 d D`: the explicit `N₀`
  (`Σ_{k ≤ 8} absorbN0 (miA d k) 757 ε' + tailN0 ε' D`).
* `absorb_av`, `absorb_av_one`, `absorb_iso`, `absorb_iso_one`: `Absorb` for `N ≥ miN0 d D`.
* `MasterIneqSat` (a named hypothesis here): the averaged clause of
  `ZigProof.MasterIneqPhi` restricted to **saturated** patterns (`¬ HasDesatFactor σ`). It needs
  the saturated linear bound uniformly in `s` on one event and over all slots;
  `MI.masterIneq_sat` reduces it to `SatLinBound`, and it is proved as `SatLin.masterIneqSat`.
* **`masterIneqPhi_of_MI`**: `MasterIneqSat → ZigProof.MasterIneqPhi`, with
  `N₀ = max N₀^{sat} ⌈miN0 d D⌉`; every isotropic index (`k = 1` and `k ≥ 2`) and every
  non-saturated averaged index is proved (`masterIneq_iso*`, `masterIneq_av*`, `tail_le`).
* `shortRingLocalLaw_of_masterIneqSat`: `MasterIneqSat → Inputs.ShortRingLocalLaw`
  (through `ZigProof.shortRingLocalLaw_of_masterIneqPhi`).
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
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Assembly (zigPsiData)
open BlockBand.Native.ErdosRiabov.Apriori (aprPsiI aprPsiA aprLamM)
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open BlockBand.SourceProcess.FiniteDriverIntegration
open Expo (lossAlpha lossBeta)
open scoped NNReal ENNReal

variable {p : BlockBand.Parameters}

/-! ## The explicit constants -/

/-- `A_Z(k) = 1 + A_Λ + A_E(k)`. -/
def aZ (d : VSData) (k : ℕ) : ℝ := 1 + aLam d + aExtra d k

/-- `K_av(k) = C_P^k + C_7`. -/
def kAv (d : VSData) (k : ℕ) : ℝ := kernelActionConst d ^ k + (1 + vsCK d * d.C1pp / d.cm)

/-- The constant of the four non-saturated families:
`(3k²+k+1) c_av K_av A_Z² A_I(1-β) + k K_av (1 + 𝔠 A_Λ³ A_I(2-2β))
+ (3k²+k+1) c_iso C_P^k A_Z² (A_I(1/2-α) + A_I(0)) + k C_P^k (1 + 𝔠 A_Λ³ (A_I(1-2α) + A_I(0)))`. -/
def miA (d : VSData) (k : ℕ) : ℝ :=
  ((3 * k * k + k + 1 : ℕ) : ℝ) * cAvZ d * kAv d k * aZ d k ^ 2 * aInt d (1 - lossBeta k) +
    (k : ℝ) * kAv d k * (1 + qvC d * aLam d ^ 3 * aInt d (2 - 2 * lossBeta k)) +
    ((3 * k * k + k + 1 : ℕ) : ℝ) * cIsoZ d * kernelActionConst d ^ k * aZ d k ^ 2 *
      (aInt d (1 / 2 - lossAlpha k) + aInt d 0) +
    (k : ℝ) * kernelActionConst d ^ k *
      (1 + qvC d * aLam d ^ 3 * (aInt d (1 - 2 * lossAlpha k) + aInt d 0))

/-- The explicit `N₀` of Prop. MI: `Σ_{k ≤ 8} absorbN0 (miA d k) 757 ε' + tailN0 ε' D`. -/
def miN0 (d : VSData) (D : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 9, absorbN0 (miA d k) 757 d.epsP + tailN0 d.epsP D

theorem cAvZ_nonneg (d : VSData) : 0 ≤ cAvZ d := by
  unfold cAvZ
  have := d.one_le_Cwc; have := Apriori.constS_nonneg d; have := d.C0_ge_one
  positivity

theorem cIsoZ_nonneg (d : VSData) : 0 ≤ cIsoZ d := by
  unfold cIsoZ
  have := d.one_le_Cwc; have := d.one_le_C1pp; have := d.C0_ge_one; have := (vsCK_pos d).le
  positivity

theorem aLam_nonneg (d : VSData) : 0 ≤ aLam d := by
  unfold aLam
  have := MBound.mbPowC_ge_one d (Discharge.mzeroConst_le_sum d 8).1 8
  have := pow_nonneg (mbLogC_nonneg d) 252
  have h : 0 ≤ 1 + 18 * MBound.mbPowC d (∑ j ∈ Finset.range (8 + 1), MZero.mzeroConst d j) 8 := by
    linarith
  positivity

theorem kAv_nonneg (d : VSData) (k : ℕ) : 0 ≤ kAv d k := by
  unfold kAv
  have := kernelActionConst_ge_one d; have := (vsCK_pos d).le; have := d.one_le_C1pp
  have := d.cm_pos
  positivity

theorem aZ_one_le (d : VSData) (k : ℕ) : 1 ≤ aZ d k := by
  unfold aZ; linarith [aLam_nonneg d, aExtra_nonneg d k]

/-- The four summands of `miA` are nonnegative (for `0 ≤` the `γ`'s). -/
theorem miA_parts_nonneg (d : VSData) {k : ℕ} (hk : k ≤ 8) :
    0 ≤ ((3 * k * k + k + 1 : ℕ) : ℝ) * cAvZ d * kAv d k * aZ d k ^ 2 * aInt d (1 - lossBeta k) ∧
    0 ≤ (k : ℝ) * kAv d k * (1 + qvC d * aLam d ^ 3 * aInt d (2 - 2 * lossBeta k)) ∧
    0 ≤ ((3 * k * k + k + 1 : ℕ) : ℝ) * cIsoZ d * kernelActionConst d ^ k * aZ d k ^ 2 *
      (aInt d (1 / 2 - lossAlpha k) + aInt d 0) ∧
    0 ≤ (k : ℝ) * kernelActionConst d ^ k *
      (1 + qvC d * aLam d ^ 3 * (aInt d (1 - 2 * lossAlpha k) + aInt d 0)) := by
  have hb := qv_beta_le_one (k := k) hk
  have ha := qv_alpha_le_half (k := k) hk
  have h1 := aInt_nonneg d (γ := 1 - lossBeta k) (by linarith)
  have h2 := aInt_nonneg d (γ := 2 - 2 * lossBeta k) (by linarith)
  have h3 := aInt_nonneg d (γ := 1 / 2 - lossAlpha k) (by linarith)
  have h4 := aInt_nonneg d (γ := 1 - 2 * lossAlpha k) (by linarith)
  have h0 := aInt_nonneg d (γ := 0) le_rfl
  have := cAvZ_nonneg d; have := cIsoZ_nonneg d; have := kAv_nonneg d k
  have := aLam_nonneg d; have := (qvC_pos d).le; have := kernelActionConst_ge_one d
  refine ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem miA_nonneg (d : VSData) {k : ℕ} (hk : k ≤ 8) : 0 ≤ miA d k := by
  obtain ⟨h1, h2, h3, h4⟩ := miA_parts_nonneg d hk
  unfold miA
  linarith

theorem mi_N_two (p : BlockBand.Parameters) : 2 ≤ p.n * p.W := by
  have := p.n_ge_four; have := p.W_pos
  nlinarith

theorem aprLamM_one_le (d : VSData) {N : ℕ} (hN : 0 < N) : 1 ≤ aprLamM d N := by
  have hΛ0 := MBound.mbLambda_nonneg d hN
  have hB0 := MZero.mzeroConst_nonneg d
  have hs := Finset.sum_nonneg fun j (_ : j ∈ Finset.range 9) =>
    add_nonneg (MBound.mbConstA_nonneg d (MBound.mbLambda d N) (MZero.mzeroConst d) hΛ0 hB0 j)
      (MBound.mbConstI_nonneg d (MBound.mbLambda d N) (MZero.mzeroConst d) hΛ0 hB0 j)
  unfold aprLamM
  linarith

theorem cAv_nonneg (d : VSData) {Λ e : ℝ} (hΛ : 0 ≤ Λ) (he : 0 ≤ e) :
    0 ≤ cAv d (fun _ => Λ) e := by
  unfold cAv
  rw [ibar_const]
  have := d.one_le_Cwc; have := Apriori.constS_nonneg d; have := d.C0_ge_one
  positivity

theorem cIso_nonneg (d : VSData) {Λ : ℝ} (hΛ : 0 ≤ Λ) : 0 ≤ cIso d (fun _ => Λ) := by
  unfold cIso
  rw [ibar_const]
  have := d.one_le_Cwc; have := d.one_le_C1pp; have := d.C0_ge_one; have := (vsCK_pos d).le
  positivity

/-! ## Generic polylog bounds -/

theorem sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x :=
  Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩

/-- `m c K I ≤ m c_Z K' A_Z² A_I ℓ^{757}` from `c ≤ c_Z Z²`, `1 ≤ Z ≤ A_Z ℓ^{252}`, `K ≤ K'`,
`I ≤ A_I ℓ` (all nonnegative). -/
theorem fbound_gen {m c cZ K K' Z AZ I AI ℓ : ℝ} (hℓ : 1 ≤ ℓ) (hm : 0 ≤ m) (hc0 : 0 ≤ c)
    (hcZ : 0 ≤ cZ) (hc : c ≤ cZ * Z ^ 2) (hZ1 : 1 ≤ Z) (hZ : Z ≤ AZ * ℓ ^ 252) (hK0 : 0 ≤ K)
    (hK : K ≤ K') (hI0 : 0 ≤ I) (hAI : 0 ≤ AI) (hI : I ≤ AI * ℓ) :
    m * c * K * I ≤ m * cZ * K' * AZ ^ 2 * AI * ℓ ^ 757 := by
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hZ2 : Z ^ 2 ≤ AZ ^ 2 * ℓ ^ 504 := by
    have := pow_le_pow_left₀ (by linarith) hZ 2
    rw [mul_pow, ← pow_mul] at this
    exact this
  have hc' : c ≤ cZ * (AZ ^ 2 * ℓ ^ 504) := hc.trans (mul_le_mul_of_nonneg_left hZ2 hcZ)
  have hK'0 : 0 ≤ K' := hK0.trans hK
  have hA0 : 0 ≤ cZ * (AZ ^ 2 * ℓ ^ 504) := hc0.trans hc'
  have h1 : m * c * K * I ≤ m * (cZ * (AZ ^ 2 * ℓ ^ 504)) * K' * (AI * ℓ) := by
    have := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hc' hm) hK hK0
      (mul_nonneg hm hA0)) hI hI0 (mul_nonneg (mul_nonneg hm hA0) hK'0)
    exact this
  have hp : ℓ ^ 505 ≤ ℓ ^ 757 := pow_le_pow_right₀ hℓ (by norm_num)
  have h2 : m * (cZ * (AZ ^ 2 * ℓ ^ 504)) * K' * (AI * ℓ) =
      m * cZ * K' * AZ ^ 2 * AI * ℓ ^ 505 := by ring
  rw [h2] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left hp ?_)
  have := sq_nonneg AZ
  positivity

/-- `m K √(Q Λ³ I) ≤ m K' (1 + Q A_Λ³ A_I) ℓ^{757}` from `Λ ≤ A_Λ ℓ^{252}`, `I ≤ A_I ℓ`. -/
theorem mbound_gen {m K K' Q Λ AΛ I AI ℓ : ℝ} (hℓ : 1 ≤ ℓ) (hm : 0 ≤ m) (hK0 : 0 ≤ K)
    (hK : K ≤ K') (hQ : 0 ≤ Q) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ AΛ * ℓ ^ 252) (hI0 : 0 ≤ I)
    (hI : I ≤ AI * ℓ) :
    m * K * Real.sqrt (Q * Λ ^ 3 * I) ≤ m * K' * ((1 + Q * AΛ ^ 3 * AI) * ℓ ^ 757) := by
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hx0 : 0 ≤ Q * Λ ^ 3 * I := by positivity
  have hAΛ0 : 0 ≤ AΛ * ℓ ^ 252 := hΛ0.trans hΛ
  have hAI0 : 0 ≤ AI * ℓ := hI0.trans hI
  have h3 : Λ ^ 3 ≤ (AΛ * ℓ ^ 252) ^ 3 := pow_le_pow_left₀ hΛ0 hΛ 3
  have hx : Q * Λ ^ 3 * I ≤ Q * AΛ ^ 3 * AI * ℓ ^ 757 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left h3 hQ) hI hI0
      (mul_nonneg hQ (pow_nonneg hAΛ0 3))
    calc Q * Λ ^ 3 * I ≤ Q * (AΛ * ℓ ^ 252) ^ 3 * (AI * ℓ) := this
      _ = Q * AΛ ^ 3 * AI * ℓ ^ 757 := by ring
  have h1 : 1 ≤ ℓ ^ 757 := one_le_pow₀ hℓ
  have hs := (sqrt_le_one_add hx0).trans (add_le_add h1 hx)
  have hK'0 : 0 ≤ K' := hK0.trans hK
  calc m * K * Real.sqrt (Q * Λ ^ 3 * I) ≤ m * K' * (ℓ ^ 757 + Q * AΛ ^ 3 * AI * ℓ ^ 757) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hK hm) hs (Real.sqrt_nonneg _) (mul_nonneg hm hK'0)
    _ = _ := by ring

/-- Each summand of `miA` is at most `miA`. -/
theorem miA_parts_le (d : VSData) {k : ℕ} (hk : k ≤ 8) :
    ((3 * k * k + k + 1 : ℕ) : ℝ) * cAvZ d * kAv d k * aZ d k ^ 2 * aInt d (1 - lossBeta k) ≤
      miA d k ∧
    (k : ℝ) * kAv d k * (1 + qvC d * aLam d ^ 3 * aInt d (2 - 2 * lossBeta k)) ≤ miA d k ∧
    ((3 * k * k + k + 1 : ℕ) : ℝ) * cIsoZ d * kernelActionConst d ^ k * aZ d k ^ 2 *
      (aInt d (1 / 2 - lossAlpha k) + aInt d 0) ≤ miA d k ∧
    (k : ℝ) * kernelActionConst d ^ k *
      (1 + qvC d * aLam d ^ 3 * (aInt d (1 - 2 * lossAlpha k) + aInt d 0)) ≤ miA d k := by
  obtain ⟨h1, h2, h3, h4⟩ := miA_parts_nonneg d hk
  unfold miA
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The propagator constants are below `K_av`, `C_P^k`. -/
theorem kP_le_kAv (d : VSData) (k : ℕ) : kernelActionConst d ^ k ≤ kAv d k := by
  unfold kAv; have := (vsCK_pos d).le; have := d.one_le_C1pp; have := d.cm_pos
  have : 0 ≤ 1 + vsCK d * d.C1pp / d.cm := by positivity
  linarith

theorem c7_le_kAv (d : VSData) (k : ℕ) : 1 + vsCK d * d.C1pp / d.cm ≤ kAv d k := by
  unfold kAv; have := pow_nonneg (zero_le_one.trans (kernelActionConst_ge_one d)) k
  linarith

theorem c7_nonneg (d : VSData) : 0 ≤ 1 + vsCK d * d.C1pp / d.cm := by
  have := (vsCK_pos d).le; have := d.one_le_C1pp; have := d.cm_pos; positivity

/-! ## Polylog bounds of the constants -/

section Bounds

variable (d : VSData) {P : PsiData (p.n * p.W)} (hPW : P.W = p.W)
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {T : ℝ} (hT1 : T ≤ 1)
include hPW hz hT1

omit hPW hz hT1 in
/-- `Λ_M, e_k ≥ 0` and `1 + Λ_M + e_k ≤ A_Z ℓ^{252}`. -/
theorem z_le {k : ℕ} (hk : k ≤ 8) :
    0 ≤ aprLamM d (p.n * p.W) ∧ 0 ≤ eMI d (p.n * p.W) k ∧
      1 + aprLamM d (p.n * p.W) + eMI d (p.n * p.W) k ≤ aZ d k * logL (p.n * p.W) ^ 252 := by
  have hN2 := mi_N_two p
  have hΛ := aprLamM_le_logL d hN2
  have he := eMI_le_logL d hN2 hk
  have hl := one_le_pow₀ (one_le_logL (show 1 ≤ p.n * p.W by omega)) (n := 252)
  have hΛ1 := aprLamM_one_le d (show 0 < p.n * p.W by omega)
  refine ⟨by linarith, eMI_nonneg d (by omega) k, ?_⟩
  unfold aZ
  nlinarith

omit hPW hz hT1 in
theorem mi_logL_one : 1 ≤ logL (p.n * p.W) := one_le_logL (by have := mi_N_two p; omega)

/-- `fAvC ≤ miA ℓ^{757}` (`k = n+2`). -/
theorem fAvC_le {n : ℕ} (hn : n + 2 ≤ 8) :
    fAvC d P (aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 2)) n T ≤
      miA d (n + 2) * logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, he0, hZ⟩ := z_le d (p := p) hn
  have hℓ := mi_logL_one (p := p)
  have hγ : 0 ≤ 1 - lossBeta (n + 2) := by linarith [qv_beta_le_one (k := n + 2) hn]
  have h := fbound_gen (m := ((3 * (n + 2) * (n + 2) + (n + 2) + 1 : ℕ) : ℝ))
    (K := kernelActionConst d ^ (n + 2)) hℓ (Nat.cast_nonneg _) (cAv_nonneg d hΛ0 he0)
    (cAvZ_nonneg d) (cAv_le d hΛ0 he0) (by linarith) hZ
    (pow_nonneg (zero_le_one.trans (kernelActionConst_ge_one d)) _) (kP_le_kAv d _)
    (intF_nonneg d P hPW hz hT1 hγ) (aInt_nonneg d hγ) (intF_le_logL d P hPW hz hT1 hγ)
  have hp := pow_nonneg (zero_le_one.trans hℓ) 757
  unfold fAvC avConst
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hp)
  exact (miA_parts_le d hn).1

/-- `mAvC ≤ miA ℓ^{757}` (`k = n+2`). -/
theorem mAvC_le {n : ℕ} (hn : n + 2 ≤ 8) :
    mAvC d P (aprLamM d (p.n * p.W)) n T ≤ miA d (n + 2) * logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, -, -⟩ := z_le d (p := p) hn
  have hℓ := mi_logL_one (p := p)
  have hγ : 0 ≤ 2 - 2 * lossBeta (n + 2) := by linarith [qv_beta_le_one (k := n + 2) hn]
  have h := mbound_gen (m := (n : ℝ) + 2) (K := kernelActionConst d ^ (n + 2)) hℓ
    (by positivity) (pow_nonneg (zero_le_one.trans (kernelActionConst_ge_one d)) _)
    (kP_le_kAv d _) (qvC_pos d).le hΛ0 (aprLamM_le_logL d (mi_N_two p))
    (intF_nonneg d P hPW hz hT1 hγ) (intF_le_logL d P hPW hz hT1 hγ)
  have hp := pow_nonneg (zero_le_one.trans hℓ) 757
  unfold mAvC
  refine h.trans ?_
  have e : ((n : ℝ) + 2) * kAv d (n + 2) *
      ((1 + qvC d * aLam d ^ 3 * aInt d (2 - 2 * lossBeta (n + 2))) * logL (p.n * p.W) ^ 757) =
      (((n + 2 : ℕ) : ℝ) * kAv d (n + 2) *
        (1 + qvC d * aLam d ^ 3 * aInt d (2 - 2 * lossBeta (n + 2)))) *
          logL (p.n * p.W) ^ 757 := by push_cast; ring
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ hp
  exact (miA_parts_le d hn).2.1

/-- `fAvOneC ≤ miA ℓ^{757}` (`k = 1`). -/
theorem fAvOneC_le :
    fAvOneC d P (aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) 1) T ≤
      miA d 1 * logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, he0, hZ⟩ := z_le d (p := p) (k := 1) (by norm_num)
  have hℓ := mi_logL_one (p := p)
  have hγ : 0 ≤ 1 - lossBeta 1 := by linarith [qv_beta_le_one (k := 1) (by norm_num)]
  have h := fbound_gen (m := ((3 * 1 * 1 + 1 + 1 : ℕ) : ℝ))
    (K := 1 + vsCK d * d.C1pp / d.cm) hℓ (Nat.cast_nonneg _) (cAv_nonneg d hΛ0 he0)
    (cAvZ_nonneg d) (cAv_le d hΛ0 he0) (by linarith) hZ (c7_nonneg d) (c7_le_kAv d 1)
    (intF_nonneg d P hPW hz hT1 hγ) (aInt_nonneg d hγ) (intF_le_logL d P hPW hz hT1 hγ)
  have hp := pow_nonneg (zero_le_one.trans hℓ) 757
  unfold fAvOneC avConst
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hp)
  exact (miA_parts_le d (k := 1) (by norm_num)).1

/-- `mAvOneC ≤ miA ℓ^{757}` (`k = 1`). -/
theorem mAvOneC_le : mAvOneC d P (aprLamM d (p.n * p.W)) T ≤ miA d 1 * logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, -, -⟩ := z_le d (p := p) (k := 1) (by norm_num)
  have hℓ := mi_logL_one (p := p)
  have hγ : 0 ≤ 2 - 2 * lossBeta 1 := by linarith [qv_beta_le_one (k := 1) (by norm_num)]
  have h := mbound_gen (m := (0 : ℝ) + 1) (K := 1 + vsCK d * d.C1pp / d.cm) hℓ
    (by norm_num) (c7_nonneg d) (c7_le_kAv d 1) (qvC_pos d).le hΛ0
    (aprLamM_le_logL d (mi_N_two p)) (intF_nonneg d P hPW hz hT1 hγ)
    (intF_le_logL d P hPW hz hT1 hγ)
  have hp := pow_nonneg (zero_le_one.trans hℓ) 757
  unfold mAvOneC
  refine h.trans ?_
  have e : ((0 : ℝ) + 1) * kAv d 1 *
      ((1 + qvC d * aLam d ^ 3 * aInt d (2 - 2 * lossBeta 1)) * logL (p.n * p.W) ^ 757) =
      (((1 : ℕ) : ℝ) * kAv d 1 * (1 + qvC d * aLam d ^ 3 * aInt d (2 - 2 * lossBeta 1))) *
        logL (p.n * p.W) ^ 757 := by push_cast; ring
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ hp
  exact (miA_parts_le d (k := 1) (by norm_num)).2.1

/-- `fIsoC ≤ miA ℓ^{757}` (`k = n+2`). -/
theorem fIsoC_le {n : ℕ} (hn : n + 2 ≤ 8) :
    fIsoC d P (aprLamM d (p.n * p.W)) n T ≤ miA d (n + 2) * logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, he0, hZ⟩ := z_le d (p := p) hn
  have hℓ := mi_logL_one (p := p)
  have hγ : 0 ≤ 1 / 2 - lossAlpha (n + 2) := by linarith [qv_alpha_le_half (k := n + 2) hn]
  have hI := intF_le_logL d P hPW hz hT1 hγ
  have hA0 := aInt_nonneg d (γ := 0) le_rfl
  have hC := kernelActionConst_ge_one d
  have h := fbound_gen (m := ((3 * (n + 2) * (n + 2) + (n + 2) + 1 : ℕ) : ℝ))
    (K := kernelActionConst d ^ (n + 1)) (K' := kernelActionConst d ^ (n + 2))
    (AI := aInt d (1 / 2 - lossAlpha (n + 2)) + aInt d 0) hℓ (Nat.cast_nonneg _)
    (cIso_nonneg d hΛ0) (cIsoZ_nonneg d) (cIso_le d hΛ0 (by linarith)) (by linarith) hZ
    (pow_nonneg (by linarith) _) (pow_le_pow_right₀ hC (by omega))
    (intF_nonneg d P hPW hz hT1 hγ) (by linarith [aInt_nonneg d hγ])
    (hI.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith)))
  have hp := pow_nonneg (zero_le_one.trans hℓ) 757
  unfold fIsoC isoConst
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hp)
  exact (miA_parts_le d hn).2.2.1

/-- `mIsoC ≤ miA ℓ^{757}` (`k = n+2`). -/
theorem mIsoC_le {n : ℕ} (hn : n + 2 ≤ 8) :
    mIsoC d P (aprLamM d (p.n * p.W)) n T ≤ miA d (n + 2) * logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, -, -⟩ := z_le d (p := p) hn
  have hℓ := mi_logL_one (p := p)
  have hγ : 0 ≤ 1 - 2 * lossAlpha (n + 2) := by linarith [qv_alpha_le_half (k := n + 2) hn]
  have hA0 := aInt_nonneg d (γ := 0) le_rfl
  have hC := kernelActionConst_ge_one d
  have h := mbound_gen (m := (n : ℝ) + 2) (K := kernelActionConst d ^ (n + 1))
    (K' := kernelActionConst d ^ (n + 2)) (AI := aInt d (1 - 2 * lossAlpha (n + 2)) + aInt d 0)
    hℓ (by positivity) (pow_nonneg (by linarith) _) (pow_le_pow_right₀ hC (by omega))
    (qvC_pos d).le hΛ0 (aprLamM_le_logL d (mi_N_two p)) (intF_nonneg d P hPW hz hT1 hγ)
    ((intF_le_logL d P hPW hz hT1 hγ).trans (mul_le_mul_of_nonneg_right (by linarith)
      (by linarith)))
  have hp := pow_nonneg (zero_le_one.trans hℓ) 757
  unfold mIsoC
  refine h.trans ?_
  have e : ((n : ℝ) + 2) * kernelActionConst d ^ (n + 2) *
      ((1 + qvC d * aLam d ^ 3 * (aInt d (1 - 2 * lossAlpha (n + 2)) + aInt d 0)) *
        logL (p.n * p.W) ^ 757) =
      (((n + 2 : ℕ) : ℝ) * kernelActionConst d ^ (n + 2) *
        (1 + qvC d * aLam d ^ 3 * (aInt d (1 - 2 * lossAlpha (n + 2)) + aInt d 0))) *
          logL (p.n * p.W) ^ 757 := by push_cast; ring
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ hp
  exact (miA_parts_le d hn).2.2.2

/-- `fIsoOneC ≤ miA ℓ^{757}` (`k = 1`). -/
theorem fIsoOneC_le :
    fIsoOneC d P (aprLamM d (p.n * p.W)) T ≤ miA d 1 * logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, he0, hZ⟩ := z_le d (p := p) (k := 1) (by norm_num)
  have hℓ := mi_logL_one (p := p)
  have hα : lossAlpha 1 = 0 := qv_alpha_of_le_four (by norm_num)
  have hγ : (0 : ℝ) ≤ 0 - lossAlpha 1 := by rw [hα]; norm_num
  have hI := intF_le_logL d P hPW hz hT1 hγ
  have hA1 := aInt_nonneg d (γ := 1 / 2 - lossAlpha 1) (by rw [hα]; norm_num)
  have hC := kernelActionConst_ge_one d
  have h := fbound_gen (m := ((3 * 1 * 1 + 1 + 1 : ℕ) : ℝ)) (K := 1)
    (K' := kernelActionConst d ^ 1) (AI := aInt d (1 / 2 - lossAlpha 1) + aInt d 0)
    hℓ (Nat.cast_nonneg _) (cIso_nonneg d hΛ0) (cIsoZ_nonneg d) (cIso_le d hΛ0 (by linarith))
    (by linarith) hZ zero_le_one (by rw [pow_one]; exact hC)
    (intF_nonneg d P hPW hz hT1 hγ) (by linarith [aInt_nonneg d (γ := 0) le_rfl])
    (hI.trans (mul_le_mul_of_nonneg_right (by
      rw [hα, sub_zero]
      linarith [aInt_nonneg d (γ := 1 / 2 - 0) (by norm_num)]) (by linarith)))
  have hp := pow_nonneg (zero_le_one.trans hℓ) 757
  unfold fIsoOneC isoConst
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hp)
  exact (miA_parts_le d (k := 1) (by norm_num)).2.2.1

/-- `mIsoOneC ≤ miA ℓ^{757}` (`k = 1`). -/
theorem mIsoOneC_le :
    mIsoOneC d P (aprLamM d (p.n * p.W)) T ≤ miA d 1 * logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, -, -⟩ := z_le d (p := p) (k := 1) (by norm_num)
  have hℓ := mi_logL_one (p := p)
  have hA0 := aInt_nonneg d (γ := 0) le_rfl
  have hA1 := aInt_nonneg d (γ := 1 - 2 * lossAlpha 1) (by
    rw [qv_alpha_of_le_four (by norm_num)]; norm_num)
  have hC := kernelActionConst_ge_one d
  have h := mbound_gen (m := 1) (K := 1) (K' := kernelActionConst d ^ 1)
    (AI := aInt d (1 - 2 * lossAlpha 1) + aInt d 0) hℓ zero_le_one zero_le_one
    (by rw [pow_one]; exact hC) (qvC_pos d).le hΛ0 (aprLamM_le_logL d (mi_N_two p))
    (intF_nonneg d P hPW hz hT1 le_rfl) ((intF_le_logL d P hPW hz hT1 le_rfl).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by linarith)))
  have hp := pow_nonneg (zero_le_one.trans hℓ) 757
  unfold mIsoOneC
  refine (le_of_eq (by ring)).trans (h.trans ?_)
  have e : 1 * kernelActionConst d ^ 1 *
      ((1 + qvC d * aLam d ^ 3 * (aInt d (1 - 2 * lossAlpha 1) + aInt d 0)) *
        logL (p.n * p.W) ^ 757) =
      (((1 : ℕ) : ℝ) * kernelActionConst d ^ 1 *
        (1 + qvC d * aLam d ^ 3 * (aInt d (1 - 2 * lossAlpha 1) + aInt d 0))) *
          logL (p.n * p.W) ^ 757 := by push_cast; ring
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ hp
  exact (miA_parts_le d (k := 1) (by norm_num)).2.2.2

/-- **Absorption, non-saturated averaged `k = n+2`** for `N ≥ absorbN0 (miA d k) 757 ε'`. -/
theorem absorb_av {n : ℕ} (hn : n + 2 ≤ 8)
    (hN : absorbN0 (miA d (n + 2)) 757 d.epsP ≤ ((p.n * p.W : ℕ) : ℝ)) :
    Absorb (fAvC d P (aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 2)) n T)
      (mAvC d P (aprLamM d (p.n * p.W)) n T) (p.n * p.W) d.epsP :=
  absorb_of_logL d.epsP_pos (miA_nonneg d hn) (fAvC_le d hPW hz hT1 hn)
    (mAvC_le d hPW hz hT1 hn) hN

/-- **Absorption, averaged `k = 1`**. -/
theorem absorb_av_one (hN : absorbN0 (miA d 1) 757 d.epsP ≤ ((p.n * p.W : ℕ) : ℝ)) :
    Absorb (fAvOneC d P (aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) 1) T)
      (mAvOneC d P (aprLamM d (p.n * p.W)) T) (p.n * p.W) d.epsP :=
  absorb_of_logL d.epsP_pos (miA_nonneg d (by norm_num)) (fAvOneC_le d hPW hz hT1)
    (mAvOneC_le d hPW hz hT1) hN

/-- **Absorption, isotropic `k = n+2`**. -/
theorem absorb_iso {n : ℕ} (hn : n + 2 ≤ 8)
    (hN : absorbN0 (miA d (n + 2)) 757 d.epsP ≤ ((p.n * p.W : ℕ) : ℝ)) :
    Absorb (fIsoC d P (aprLamM d (p.n * p.W)) n T) (mIsoC d P (aprLamM d (p.n * p.W)) n T)
      (p.n * p.W) d.epsP :=
  absorb_of_logL d.epsP_pos (miA_nonneg d hn) (fIsoC_le d hPW hz hT1 hn)
    (mIsoC_le d hPW hz hT1 hn) hN

/-- **Absorption, isotropic `k = 1`**. -/
theorem absorb_iso_one (hN : absorbN0 (miA d 1) 757 d.epsP ≤ ((p.n * p.W : ℕ) : ℝ)) :
    Absorb (fIsoOneC d P (aprLamM d (p.n * p.W)) T) (mIsoOneC d P (aprLamM d (p.n * p.W)) T)
      (p.n * p.W) d.epsP :=
  absorb_of_logL d.epsP_pos (miA_nonneg d (by norm_num)) (fIsoOneC_le d hPW hz hT1)
    (mIsoOneC_le d hPW hz hT1) hN

end Bounds

/-! ## `N₀` and the tail -/

theorem absorbN0_nonneg (A : ℝ) (q : ℕ) (ε : ℝ) : 0 ≤ absorbN0 A q ε :=
  le_trans (by norm_num) (le_max_left _ _)

theorem tailN0_nonneg (ε D : ℝ) : 0 ≤ tailN0 ε D := by
  unfold tailN0; positivity

theorem le_miN0 (d : VSData) (D : ℝ) {k : ℕ} (hk : k ≤ 8) :
    absorbN0 (miA d k) 757 d.epsP ≤ miN0 d D ∧ tailN0 d.epsP D ≤ miN0 d D := by
  have hs := Finset.sum_nonneg fun j (_ : j ∈ Finset.range 9) =>
    absorbN0_nonneg (miA d j) 757 d.epsP
  have h1 := Finset.single_le_sum (f := fun j => absorbN0 (miA d j) 757 d.epsP)
    (fun j _ => absorbN0_nonneg _ _ _) (Finset.mem_range.mpr (show k < 9 by omega))
  have h2 := tailN0_nonneg d.epsP D
  unfold miN0
  constructor <;> linarith

/-- The tail in `ℝ≥0∞`: `4 ofReal(e^{-N^{ε'}/4}) ≤ ofReal(N^{-D})` for `N ≥ miN0 d D`. -/
theorem tail_ennreal (d : VSData) (D : ℝ) {N : ℕ} (hN1 : 1 ≤ N) (hN : miN0 d D ≤ N) :
    4 * ENNReal.ofReal (Real.exp (-((N : ℝ) ^ d.epsP / 4))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (tail_le d.epsP_pos hN1 ((le_miN0 d D (k := 0)
    (by norm_num)).2.trans hN))

/-! ## The assembly -/

/-- **The saturated part of the master inequality (named hypothesis, open).** The averaged clause of
`ZigProof.MasterIneqPhi` for **saturated** patterns (`¬ HasDesatFactor σ`): for every `d` and
`D > 0` there is `N₀` such that, in the setting of `MasterIneqPhi`,
`P(t ≤ τ ∧ N^{ε'} φ^{av}_{k,t} < avRatio (σ,u) t H_t) ≤ N^{-D}` for saturated `σ`.
`MI.masterIneq_sat` proves it from `SatLinBound` (the saturated linear bound uniformly in `s ∈ (0,t]` on one event,
summed over the `k` slots, with `q ≤ N^{-D}/2`) and its absorption inequality; that input needs
a grid-in-`s` union for `Circ.circLLEvent`ᶜ and the slot rotation. -/
def MasterIneqSat : Prop :=
  ∀ (d : VSData) (D : ℝ), 0 < D → ∃ N₀ : ℕ,
    ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W → d.zeta0 < 1 →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ),
        BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z →
        ∀ t : ℝ≥0, t ≤ 1 → ∀ k ∈ kRange, ∀ i : AvIdx (p.n * p.W) k, ¬ HasDesatFactor i.1 →
          driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
              {x | (t : WithTop ℝ≥0) ≤ ZigProof.zigTau p d z x ∧
                ((p.n * p.W : ℕ) : ℝ) ^ d.epsP *
                    Expo.phiAv ((p.n * p.W : ℕ) : ℝ) d.xi ((zigPsiData p d.D z).lEta t)
                      (ZigProof.yZig (zigPsiData p d.D z) t) k <
                  (zigPsiData p d.D z).avRatio i t (VS.vsBandFin p t x)} ≤
            ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D))

theorem pathH_coe (p : BlockBand.Parameters) (x : RingSample p) (t : ℝ≥0) :
    pathH p x t = VS.vsBandFin p t x := by
  simp [pathH]

/-- **the master inequality ⇒ `ZigProof.MasterIneqPhi`**, from the saturated part `MasterIneqSat`
(proved as `SatLin.masterIneqSat`), with `N₀ = max N₀^{sat} ⌈miN0 d D⌉`. Every isotropic index
(`masterIneq_iso`, `masterIneq_iso_one`) and every non-saturated averaged index
(`masterIneq_av`, `masterIneq_av_one`) is proved here: the a priori bounds by `Apriori` and
`Apriori.mbounds_extra_uncond`, the absorption by `absorb_*` (`Λ_M` polylog), the tail by
`tail_le`. -/
theorem masterIneqPhi_of_MI (h : MasterIneqSat) : ZigProof.MasterIneqPhi := by
  intro d D hD
  obtain ⟨Ns, hs⟩ := h d D hD
  refine ⟨max Ns ⌈miN0 d D⌉₊, fun p hpb hN hζ hband model z hz t ht k hk => ?_⟩
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk8 : k ≤ 8 := (Finset.mem_Icc.mp hk).2
  have hNR : miN0 d D ≤ ((p.n * p.W : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hN)
  have hN1 : 1 ≤ p.n * p.W := by have := mi_N_two p; omega
  have htail := tail_ennreal d D hN1 hNR
  have hT1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have hb : d.b = p.b := hpb.symm
  have hA : ∀ {k'}, k' ≤ 8 → absorbN0 (miA d k') 757 d.epsP ≤ ((p.n * p.W : ℕ) : ℝ) :=
    fun hk' => (le_miN0 d D hk').1.trans hNR
  have hz' : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 (zigPsiData p d.D z).z := hz
  set μ : Measure p.SiteMatrix := (model.law : Measure p.SiteMatrix)
  constructor
  · rintro ⟨σ, a, b, u⟩
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      refine le_trans (measure_mono ?_) ((masterIneq_iso_one μ d hb rfl rfl rfl hz' hband t hT1
        σ a b u (absorb_iso_one d rfl hz' hT1 (hA (by norm_num)))).trans htail)
      intro x hx
      refine ⟨hx.1, ?_⟩
      have h2 := hx.2
      rw [← pathH_coe] at h2
      exact h2
    · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
      refine le_trans (measure_mono ?_) ((masterIneq_iso μ d hb rfl rfl rfl hz' hband t hT1 hk8
        σ a b u (absorb_iso d rfl hz' hT1 hk8 (hA hk8))).trans htail)
      intro x hx
      refine ⟨hx.1, ?_⟩
      have h2 := hx.2
      rw [← pathH_coe] at h2
      exact h2
  · rintro ⟨σ, u⟩
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      refine le_trans (measure_mono ?_) ((masterIneq_av_one μ d hb rfl rfl rfl hz' hband t hT1
        σ u (absorb_av_one d rfl hz' hT1 (hA (by norm_num)))).trans htail)
      intro x hx
      refine ⟨hx.1, ?_⟩
      have h2 := hx.2
      rw [← pathH_coe] at h2
      exact h2
    · by_cases hσ : HasDesatFactor σ
      · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
        refine le_trans (measure_mono ?_) ((masterIneq_av μ d hb rfl rfl rfl hz' hband t hT1 hk8
          σ hσ u (absorb_av d rfl hz' hT1 hk8 (hA hk8))).trans htail)
        intro x hx
        refine ⟨hx.1, ?_⟩
        have h2 := hx.2
        rw [← pathH_coe] at h2
        exact h2
      · exact hs p hpb (le_of_max_le_left hN) hζ hband model z hz t ht k hk (σ, u) hσ

/-- **The short-ring local law from the saturated part of MI** (from `MasterIneqSat`):
`masterIneqPhi_of_MI` and `ZigProof.shortRingLocalLaw_of_masterIneqPhi`. -/
theorem shortRingLocalLaw_of_masterIneqSat (h : MasterIneqSat) :
    BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw :=
  ZigProof.shortRingLocalLaw_of_masterIneqPhi (masterIneqPhi_of_MI h)

end BlockBand.Native.ErdosRiabov.MI
