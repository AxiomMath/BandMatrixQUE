module

public import BlockBand.Native.ErdosRiabov.MI.Final

/-!
# Master inequalities: the `N ≥ N₀` conditions

For `N` large the polylogarithmic constants of the master inequalities are absorbed into `N^ε`,
and the exponential tail is below `N^{-D}`. With `ℓ_N = 1 + log N` (`logL`), for `N ≥ 2`:
* `eMI_le_logL`: the extra `M`-bound constant `e_k ≤ A_E(k) ℓ^{252}`
  (`Apriori.extraConst_le_log_pow`);
* `intF_le_logL`: `iF(γ) ≤ A_I(γ) ℓ`, `A_I(γ) = c_m⁻¹ (2/γ + log(C₀+1) + 1)`;
* `cAv_le`, `cIso_le`: the forcing constants are `≤ c (1 + Λ + e)²`;
* the family bounds `fAvC, mAvC, … ≤ miA d k ℓ^{757}` (`absorb_av`, …: `Absorb` holds for
  `N ≥ absorbN0 (miA d k) 757 ε`);
* `absorb_of_logL`: `F, M ≤ A ℓ^q` and `N ≥ absorbN0 A q ε` give `F + N^{ε/2} M ≤ N^ε`
  (`log N ≤ N^δ/δ`, `δ = ε/(4(q+1))`), `absorbN0 A q ε = max 2 ((2A(1+4(q+1)/ε)^q)^{4/ε})`;
* `tail_le`: `4 e^{-N^ε/4} ≤ N^{-D}` for `N ≥ tailN0 ε D = 4 m! 4^m`, `m = ⌈(D+1)/ε⌉`.
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
open BlockBand.Native.ErdosRiabov.MBound
open BlockBand.Native.ErdosRiabov.Apriori (aprLamM extraConst extraLogC aprC7)
open Expo (lossAlpha lossBeta)

variable {p : BlockBand.Parameters}

/-!
## The log scale
-/

/-- `ℓ_N = 1 + log N`. -/
def logL (N : ℕ) : ℝ := 1 + Real.log N

theorem log_nonneg_nat {N : ℕ} (hN : 1 ≤ N) : 0 ≤ Real.log N :=
  Real.log_nonneg (by exact_mod_cast hN)

theorem one_le_logL {N : ℕ} (hN : 1 ≤ N) : 1 ≤ logL N := by
  unfold logL; linarith [log_nonneg_nat hN]

theorem log_le_logL (N : ℕ) : Real.log N ≤ logL N := by unfold logL; linarith

theorem logL_pow_mono {N : ℕ} (hN : 1 ≤ N) {m q : ℕ} (h : m ≤ q) : logL N ^ m ≤ logL N ^ q :=
  pow_le_pow_right₀ (one_le_logL hN) h

/-!
## `Λ_M`, `e_k`, `iF`
-/

/-- `C_log ≥ 0`. -/
theorem mbLogC_nonneg (d : VSData) : 0 ≤ mbLogC d := by
  unfold mbLogC
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 ≤ Real.log (d.C0 + 1) := Real.log_nonneg (by linarith [d.C0_ge_one])
  have h4 := d.cm_pos
  positivity

/-- **`Λ_M` is polylogarithmic**: for `N ≥ 2`, `Λ_M ≤ (1 + 18 c₈)(C_log log N)^{e_8}`,
`e_8 = 252`, `c₈ = mbPowC d (Σ_{j ≤ 8} mzeroConst d j) 8`. -/
theorem aprLamM_le_log (d : VSData) {N : ℕ} (hN : 2 ≤ N) :
    aprLamM d N ≤ (1 + 18 * mbPowC d (∑ j ∈ Finset.range (8 + 1), MZero.mzeroConst d j) 8) *
      (mbLogC d * Real.log N) ^ mbPowExp 8 := by
  obtain ⟨h0, h1, h2⟩ := mbLambda_le_log d hN
  obtain ⟨hB, hBk⟩ := Discharge.mzeroConst_le_sum d 8
  have hLe : 1 ≤ (mbLogC d * Real.log N) ^ mbPowExp 8 := one_le_pow₀ h2
  have hj : ∀ j ∈ Finset.range 9, mbConstA d (mbLambda d N) (MZero.mzeroConst d) j +
      mbConstI d (mbLambda d N) (MZero.mzeroConst d) j ≤
        2 * (mbPowC d (∑ j ∈ Finset.range (8 + 1), MZero.mzeroConst d j) 8 *
          (mbLogC d * Real.log N) ^ mbPowExp 8) := by
    intro j hj
    have hj8 : j ≤ 8 := by have := Finset.mem_range.mp hj; omega
    have h := mbConst_le_pow d (MZero.mzeroConst d) h0 h1 h2 hB (MZero.mzeroConst_nonneg d) 8
      hBk j hj8
    linarith [h.1, h.2]
  have hs := Finset.sum_le_sum hj
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  unfold aprLamM
  have e : (1 + 18 * mbPowC d (∑ j ∈ Finset.range (8 + 1), MZero.mzeroConst d j) 8) *
      (mbLogC d * Real.log N) ^ mbPowExp 8 = (mbLogC d * Real.log N) ^ mbPowExp 8 +
        9 * (2 * (mbPowC d (∑ j ∈ Finset.range (8 + 1), MZero.mzeroConst d j) 8 *
          (mbLogC d * Real.log N) ^ mbPowExp 8)) := by ring
  rw [e]
  push_cast at hs
  linarith

/-- `A_Λ = (1 + 18 c₈) C_log^{252}`. -/
def aLam (d : VSData) : ℝ :=
  (1 + 18 * mbPowC d (∑ j ∈ Finset.range (8 + 1), MZero.mzeroConst d j) 8) * mbLogC d ^ 252

theorem mbPowExp_eight : mbPowExp 8 = 252 := by norm_num [mbPowExp]

/-- `Λ_M ≤ A_Λ ℓ^{252}` (`N ≥ 2`). -/
theorem aprLamM_le_logL (d : VSData) {N : ℕ} (hN : 2 ≤ N) :
    aprLamM d N ≤ aLam d * logL N ^ 252 := by
  have h := aprLamM_le_log d hN
  rw [mbPowExp_eight, mul_pow] at h
  have hc8 := mbPowC_ge_one d (Discharge.mzeroConst_le_sum d 8).1 8
  have hlog := log_nonneg_nat (show 1 ≤ N by omega)
  refine h.trans ?_
  unfold aLam
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (pow_nonneg
    (mbLogC_nonneg d) _)) (by linarith)
  exact pow_le_pow_left₀ hlog (log_le_logL N) _

/-- `A_E(k) = extraLogC d (Σ_{j ≤ k} mzeroConst d j) k`. -/
def aExtra (d : VSData) (k : ℕ) : ℝ :=
  extraLogC d (∑ j ∈ Finset.range (k + 1), MZero.mzeroConst d j) k

theorem aExtra_nonneg (d : VSData) (k : ℕ) : 0 ≤ aExtra d k := by
  have hB := (Discharge.mzeroConst_le_sum d k).1
  have hc := fun j => zero_le_one.trans (mbPowC_ge_one d hB j)
  have hc7 : 0 ≤ aprC7 d := by
    unfold aprC7
    have := (vsCK_pos d).le; have := d.one_le_C1pp; have := d.cm_pos; positivity
  have hCS := Apriori.constS_nonneg d
  have hC0 : 0 ≤ d.C0 + 1 := by linarith [d.C0_ge_one]
  have hCwc : 0 ≤ d.Cwc := by linarith [d.one_le_Cwc]
  have hs := Finset.sum_nonneg fun i (_ : i ∈ Finset.Ioo 1 (k + 1)) =>
    mul_nonneg (hc i) (hc (k - i + 2))
  have hL := pow_nonneg (mbLogC_nonneg d) (mbPowExp k)
  unfold aExtra extraLogC
  have := hc k
  positivity

/-- `e_k ≤ A_E(k) ℓ^{252}` (`N ≥ 2`, `k ≤ 8`). -/
theorem eMI_le_logL (d : VSData) {N : ℕ} (hN : 2 ≤ N) {k : ℕ} (hk : k ≤ 8) :
    eMI d N k ≤ aExtra d k * logL N ^ 252 := by
  obtain ⟨hB, hBk⟩ := Discharge.mzeroConst_le_sum d k
  have h := Apriori.extraConst_le_log_pow d hN hB (MZero.mzeroConst d)
    (MZero.mzeroConst_nonneg d) hBk
  have hlog := log_nonneg_nat (show 1 ≤ N by omega)
  have hek : mbPowExp k ≤ 252 := by
    rw [← mbPowExp_eight]
    unfold mbPowExp
    have : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hk
    omega
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (aExtra_nonneg d k))
  exact (pow_le_pow_left₀ hlog (log_le_logL N) _).trans
    (logL_pow_mono (show 1 ≤ N by omega) hek)

/-- `A_I(γ) = c_m⁻¹ (2/γ + log(C₀+1) + 1)` (`2/0 = 0`). -/
def aInt (d : VSData) (γ : ℝ) : ℝ := d.cm⁻¹ * (2 / γ + Real.log (d.C0 + 1) + 1)

theorem aInt_nonneg (d : VSData) {γ : ℝ} (hγ : 0 ≤ γ) : 0 ≤ aInt d γ := by
  unfold aInt
  have := d.cm_pos
  have := Real.log_nonneg (show 1 ≤ d.C0 + 1 by linarith [d.C0_ge_one])
  have : 0 ≤ 2 / γ := div_nonneg (by norm_num) hγ
  positivity

/-- `iF(γ) ≤ A_I(γ) ℓ` (`γ ≥ 0`, `T ≤ 1`). -/
theorem intF_le_logL (d : VSData) (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {T γ : ℝ} (hT1 : T ≤ 1)
    (hγ : 0 ≤ γ) : intF d P γ T ≤ aInt d γ * logL (p.n * p.W) := by
  have hN := mi_N_pos p
  have hL := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) (hz.im_pos hN) hT1
  have hlog := log_nonneg_nat (show 1 ≤ p.n * p.W by omega)
  have hl1 := one_le_logL (show 1 ≤ p.n * p.W by omega)
  have hlC := Real.log_nonneg (show 1 ≤ d.C0 + 1 by linarith [d.C0_ge_one])
  have hcm := d.cm_pos
  have h2γ : 0 ≤ 2 / γ := div_nonneg (by norm_num) hγ
  have hkey : intF d P γ T ≤ d.cm⁻¹ * (2 / γ + Real.log (d.C0 + 1) +
      Real.log ((p.n * p.W : ℕ) : ℝ)) := by
    unfold intF qvIntRule
    have hcmd : imLower d.kappa d.C0 = d.cm := rfl
    rw [hcmd]
    split_ifs with h0
    · subst h0
      rw [Real.rpow_zero, one_mul, Real.log_mul (by linarith [d.C0_ge_one])
        (by exact_mod_cast hN.ne')]
      have : (0 : ℝ) ≤ 2 / 0 := by simp
      nlinarith [inv_pos.mpr hcm]
    · have e : P.lEta T ^ γ * (2 / (γ * d.cm) * P.lEta T ^ (-γ)) = d.cm⁻¹ * (2 / γ) := by
        rw [Real.rpow_neg hL.le]
        have : P.lEta T ^ γ ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hcm.le)
  refine hkey.trans ?_
  unfold aInt logL
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hcm.le)
  nlinarith

/-!
## The forcing constants
-/

theorem ibar_const (Λ : ℝ) : ibar (fun _ => Λ) = 1 + 9 * Λ := by
  simp [ibar, Finset.sum_const, Finset.card_range]

/-- `c_av` of the bound `cAv ≤ c_av (1 + Λ + e)²`. -/
def cAvZ (d : VSData) : ℝ :=
  10 * d.Cwc + 1 + constS d * Real.sqrt d.C1pp * (99 * (d.C0 + 1) + Real.sqrt d.C1pp)

/-- `c_iso` of the bound `cIso ≤ c_iso (1 + Λ)²`. -/
def cIsoZ (d : VSData) : ℝ :=
  d.C1pp + 99 * (d.C0 + 1) * Real.sqrt d.C1pp + 9 * d.Cwc + (d.C0 + 1 + vsCK d * d.Cwc)

theorem cAv_le (d : VSData) {Λ e : ℝ} (hΛ : 0 ≤ Λ) (he : 0 ≤ e) :
    cAv d (fun _ => Λ) e ≤ cAvZ d * (1 + Λ + e) ^ 2 := by
  unfold cAv cAvZ
  rw [ibar_const]
  set Z := 1 + Λ + e
  have hZ1 : 1 ≤ Z := by simp only [Z]; linarith
  have hZZ : Z ≤ Z ^ 2 := by nlinarith
  have hb : 1 + 9 * Λ ≤ 9 * Z := by simp only [Z]; linarith
  have hb0 : 0 ≤ 1 + 9 * Λ := by linarith
  have hb2 : (1 + 9 * Λ) * (1 + 9 * Λ) + 2 * (1 + 9 * Λ) ≤ 99 * Z ^ 2 := by nlinarith
  have hCwc : 0 ≤ d.Cwc := by linarith [d.one_le_Cwc]
  have hs := Real.sqrt_nonneg d.C1pp
  have hCS : 0 ≤ constS d := Apriori.constS_nonneg d
  have hC0 : 0 ≤ d.C0 + 1 := by linarith [d.C0_ge_one]
  have h1 : d.Cwc * (1 + 9 * Λ) ≤ 9 * d.Cwc * Z ^ 2 := by nlinarith
  have h2 : d.Cwc ≤ d.Cwc * Z ^ 2 := le_mul_of_one_le_right hCwc (by nlinarith)
  have h3 : e ≤ Z ^ 2 := by simp only [Z] at hZZ ⊢; nlinarith
  have h4 : (d.C0 + 1) * ((1 + 9 * Λ) * (1 + 9 * Λ) + 2 * (1 + 9 * Λ)) + Real.sqrt d.C1pp ≤
      (99 * (d.C0 + 1) + Real.sqrt d.C1pp) * Z ^ 2 := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hCS hs)
  nlinarith

theorem cIso_le (d : VSData) {Λ : ℝ} (hΛ : 0 ≤ Λ) {Z : ℝ} (hZ : 1 + Λ ≤ Z) :
    cIso d (fun _ => Λ) ≤ cIsoZ d * Z ^ 2 := by
  unfold cIso cIsoZ
  rw [ibar_const]
  have hZ1 : 1 ≤ Z := by linarith
  have hZ2 : 1 ≤ Z ^ 2 := by nlinarith
  have hb : 1 + 9 * Λ ≤ 9 * Z := by linarith
  have hb2 : 2 * (1 + 9 * Λ) + (1 + 9 * Λ) * (1 + 9 * Λ) ≤ 99 * Z ^ 2 := by nlinarith
  have hCwc : 0 ≤ d.Cwc := by linarith [d.one_le_Cwc]
  have hs := Real.sqrt_nonneg d.C1pp
  have hC1 : 0 ≤ d.C1pp := by linarith [d.one_le_C1pp]
  have hC0 : 0 ≤ d.C0 + 1 := by linarith [d.C0_ge_one]
  have hK : 0 ≤ d.C0 + 1 + vsCK d * d.Cwc := by have := (vsCK_pos d).le; positivity
  have h1 := mul_le_mul_of_nonneg_left hb2 (mul_nonneg hC0 hs)
  have hZZ : Z ≤ Z ^ 2 := by nlinarith
  have h2 : d.Cwc * (1 + 9 * Λ) ≤ 9 * d.Cwc * Z ^ 2 := by
    have := mul_le_mul_of_nonneg_left (hb.trans (by linarith : 9 * Z ≤ 9 * Z ^ 2)) hCwc
    linarith
  have h3 : d.C1pp ≤ d.C1pp * Z ^ 2 := le_mul_of_one_le_right hC1 hZ2
  have h4 : d.C0 + 1 + vsCK d * d.Cwc ≤ (d.C0 + 1 + vsCK d * d.Cwc) * Z ^ 2 :=
    le_mul_of_one_le_right hK hZ2
  nlinarith

/-!
## Absorption and the tail
-/

/-- `N₀` of the absorption: `max 2 ((2A(1 + 4(q+1)/ε)^q)^{4/ε})`. -/
def absorbN0 (A : ℝ) (q : ℕ) (ε : ℝ) : ℝ :=
  max 2 ((2 * A * (1 + 4 * ((q : ℝ) + 1) / ε) ^ q) ^ (4 / ε))

/-- **Absorption**: if `F, M ≤ A ℓ_N^q` (`A ≥ 0`, `ε > 0`) and
`N ≥ absorbN0 A q ε`, then `F + N^{ε/2} M ≤ N^ε`.
-/
theorem absorb_of_logL {F M A ε : ℝ} {q N : ℕ} (hε : 0 < ε) (hA : 0 ≤ A)
    (hF : F ≤ A * logL N ^ q) (hM : M ≤ A * logL N ^ q) (hN : absorbN0 A q ε ≤ N) :
    Absorb F M N ε := by
  have hN2 : (2 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hn1 : (1 : ℝ) ≤ N := by linarith
  set δ := ε / (4 * ((q : ℝ) + 1)) with hδ
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hδ0 : 0 < δ := by positivity
  set c := 1 + 4 * ((q : ℝ) + 1) / ε with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ 4 * ((q : ℝ) + 1) / ε := by positivity
    simp only [c]; linarith
  have hinvδ : 1 / δ = 4 * ((q : ℝ) + 1) / ε := by simp only [δ]; field_simp
  have hNδ1 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hn1 hδ0.le
  -- `ℓ ≤ c N^δ`
  have hℓ : logL N ≤ c * (N : ℝ) ^ δ := by
    have h1 := Real.log_le_rpow_div hn0.le hδ0
    unfold logL
    have : (N : ℝ) ^ δ / δ = (1 / δ) * (N : ℝ) ^ δ := by ring
    rw [this, hinvδ] at h1
    simp only [c]
    nlinarith
  have hℓ0 : 0 ≤ logL N := le_trans zero_le_one (one_le_logL (by exact_mod_cast hn1))
  have hℓq : logL N ^ q ≤ c ^ q * (N : ℝ) ^ (ε / 4) := by
    have h1 := pow_le_pow_left₀ hℓ0 hℓ q
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ δ), ← Real.rpow_mul hn0.le] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 ?_)
      (pow_nonneg (by linarith) _))
    simp only [δ]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set K := 2 * A * c ^ q with hK
  have hK0 : 0 ≤ K := by positivity
  have hNK : K ≤ (N : ℝ) ^ (ε / 4) := by
    have h1 : K ^ (4 / ε) ≤ N := (le_max_right _ _).trans hN
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) h1 (show 0 ≤ ε / 4 by positivity)
    rwa [← Real.rpow_mul hK0, show 4 / ε * (ε / 4) = 1 by field_simp, Real.rpow_one] at h2
  have hA' : A * logL N ^ q ≤ A * c ^ q * (N : ℝ) ^ (ε / 4) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hℓq hA
  have hh : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; congr 1; ring
  have hN2' : 1 ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hn1 (by positivity)
  have hN4 : 0 ≤ (N : ℝ) ^ (ε / 4) := Real.rpow_nonneg hn0.le _
  unfold Absorb
  rw [hh]
  have hM' : (N : ℝ) ^ (ε / 2) * M ≤ (N : ℝ) ^ (ε / 2) * (A * c ^ q * (N : ℝ) ^ (ε / 4)) :=
    mul_le_mul_of_nonneg_left (hM.trans hA') (by linarith)
  have hF' := hF.trans hA'
  have hAc : 0 ≤ A * c ^ q := by positivity
  have h3 : A * c ^ q * (N : ℝ) ^ (ε / 4) ≤
      A * c ^ q * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 2) :=
    le_mul_of_one_le_right (by positivity) hN2'
  have h4 : 2 * (A * c ^ q) * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 2) ≤
      (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 2) := by
    have := mul_le_mul_of_nonneg_right hNK (mul_nonneg hN4 (by linarith : (0:ℝ) ≤ _))
    simp only [K] at this
    nlinarith
  nlinarith

/-- `m_D = ⌈(D+1)/ε⌉` and `tailN0 ε D = 4 m! 4^m`. -/
def tailM (ε D : ℝ) : ℕ := ⌈(D + 1) / ε⌉₊

def tailN0 (ε D : ℝ) : ℝ := 4 * (tailM ε D).factorial * 4 ^ tailM ε D

/-- **The tail** `4 e^{-N^ε/4} ≤ N^{-D}` for `N ≥ tailN0 ε D`, `ε > 0`. -/
theorem tail_le {ε D : ℝ} (hε : 0 < ε) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : tailN0 ε D ≤ N) :
    4 * Real.exp (-((N : ℝ) ^ ε / 4)) ≤ (N : ℝ) ^ (-D) := by
  set m := tailM ε D
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hm : D + 1 ≤ ε * m := by
    have := Nat.le_ceil ((D + 1) / ε)
    rw [div_le_iff₀ hε] at this
    simp only [m, tailM]
    linarith
  set y := (N : ℝ) ^ ε / 4
  have hy : 0 < y := by positivity
  have hexp := Real.pow_div_factorial_le_exp y hy.le m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hym : y ^ m = (N : ℝ) ^ (ε * m) / 4 ^ m := by
    simp only [y]
    rw [div_pow, ← Real.rpow_natCast ((N : ℝ) ^ ε), ← Real.rpow_mul hn0.le]
  have hNm : (N : ℝ) ^ (D + 1) ≤ (N : ℝ) ^ (ε * m) := Real.rpow_le_rpow_of_exponent_le hn1 hm
  have h1 : Real.exp (-y) ≤ m.factorial * 4 ^ m / (N : ℝ) ^ (D + 1) := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos y)]
    have hpos : 0 < (N : ℝ) ^ (D + 1) := Real.rpow_pos_of_pos hn0 _
    rw [hym, div_le_iff₀ hf] at hexp
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul]
    have h4 : (0 : ℝ) < 4 ^ m := by positivity
    calc (N : ℝ) ^ (D + 1) ≤ (N : ℝ) ^ (ε * m) := hNm
      _ = (N : ℝ) ^ (ε * m) / 4 ^ m * 4 ^ m := by field_simp
      _ ≤ Real.exp y * m.factorial * 4 ^ m := mul_le_mul_of_nonneg_right hexp h4.le
      _ = _ := by ring
  have hND : (N : ℝ) ^ (D + 1) = (N : ℝ) ^ D * N := by
    rw [Real.rpow_add hn0, Real.rpow_one]
  have hT : (4 : ℝ) * ((m.factorial : ℝ) * 4 ^ m) ≤ N := by
    have : tailN0 ε D = 4 * (m.factorial * 4 ^ m) := by simp only [tailN0, m]; ring
    linarith
  rw [Real.rpow_neg hn0.le]
  calc 4 * Real.exp (-y) ≤ 4 * (m.factorial * 4 ^ m / (N : ℝ) ^ (D + 1)) := by linarith
    _ = 4 * (m.factorial * 4 ^ m) / N * ((N : ℝ) ^ D)⁻¹ := by
        rw [hND]; field_simp
    _ ≤ 1 * ((N : ℝ) ^ D)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (Real.rpow_nonneg hn0.le _))
        rw [div_le_one hn0]; exact hT
    _ = _ := one_mul _

end BlockBand.Native.ErdosRiabov.MI
