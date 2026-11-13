module

public import BlockBand.Native.ErdosRiabov.Evol.TermList
public import BlockBand.Native.ErdosRiabov.Contr.MoreLocal
public import BlockBand.Native.ErdosRiabov.Contr.MoreEdge
public import BlockBand.Native.ErdosRiabov.Contr.Local
public import BlockBand.Native.ErdosRiabov.Prop.Single
public import BlockBand.Native.ErdosRiabov.Psi.TauFacts

/-!
# Forcing bounds: hypotheses, scalars, exponent facts, a priori bounds

The setting of the forcing bounds.

* The hypotheses as `Prop`s: `IsoBAt` (the isotropic `M`-bound at one time), `ExtraBAt` (the
  extra `M`-bound), `APriori` (`Ψ ≤ ψ` for `n ∈ kRange`); the single-time context `FCtx d P t`
  (positivity and symmetry of `Υ`, the properties (U2), (U4) both clauses, (U6), (U7) of
  `LemmaK.ups_U2_U8_vs`, `1 ≤ ℓη ≤ Nη`, `η ≤ C₀+1`, the profile facts and `SΥ ≤ C_S Υ`, the
  kernel bound for all patterns); `FCtx` is built from VS data by `fctx_of`.
* Scalars: `(ℓη)^{-1/2} ≤ Y` and `(ℓη)^{-1} ≤ Y`, `Y = √(Nη)/(ℓη)`.
* Loss exponent facts at `K = 8`.
* Pointwise a priori bounds from `APriori`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Forcing

open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo (lossAlpha lossBeta)

variable {N : ℕ}

/-!
## Hypotheses
-/

/-- The isotropic `M`-bound at one time `t`: `|(M^{(t)}_{[1,n]}(x'))_{aa}| ≤ I √(ℓη) s^iso_n(a,x',a)`
for every
pattern and all sites. -/
def IsoBAt (P : PsiData N) (t : ℝ) (n : ℕ) (I : ℝ) : Prop :=
  ∀ (σ : Fin n → Bool) (x : Fin n → Fin N) (a : Fin N),
    ‖P.mChain σ x t a‖ ≤ I * Real.sqrt (P.lEta t) * P.sIso a a x t

/-- The extra `M`-bound at one time `t`: for patterns of length `k+1` whose first
and last entries agree, `Σ_q |M_qq| ≤ E η⁻¹ ℓη s^av_k(w_0, …, w_{k-1})`. -/
def ExtraBAt (P : PsiData N) (t : ℝ) (k : ℕ) (E : ℝ) : Prop :=
  ∀ (σ : Fin (k + 1) → Bool), σ 0 = σ (Fin.last k) → ∀ w : Fin (k + 1) → Fin N,
    ∑ q, ‖P.mChain σ w t q‖ ≤
      E / vsHeight P.z t * P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t

/-- The a priori bound: the control quantities are below `ψ` for `1 ≤ n ≤ 8`. -/
def APriori (P : PsiData N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) (psiI psiA : ℕ → ℝ) :
    Prop :=
  ∀ n ∈ kRange, P.bigPsiIso n t H ≤ psiI n ∧ P.bigPsiAv n t H ≤ psiA n

/-- `C_S = (1 + 2√(C₀+1))^D`, the constant of the profile bound `S Υ ≤ C_S Υ`. -/
def constS (d : VSData) : ℝ := (1 + 2 * Real.sqrt (d.C0 + 1)) ^ d.D

/-- The single-time context of the forcing bounds at VS data `d`: all deterministic inputs used by
the family
bounds, as named fields. -/
structure FCtx (d : VSData) (P : PsiData N) (t : ℝ) : Prop where
  pos : ∀ x y, 0 < P.ups t x y
  symm : ∀ x y, P.ups t x y = P.ups t y x
  lEta_pos : 0 < P.lEta t
  height_pos : 0 < vsHeight P.z t
  height_le : vsHeight P.z t ≤ d.C0 + 1
  one_le_lEta : 1 ≤ P.lEta t
  lEta_le : P.lEta t ≤ (N : ℝ) * vsHeight P.z t
  maxU : ∀ x y, P.ups t x y ≤ d.C1pp / P.lEta t
  triangle : ∀ x a y, P.ups t x a * P.ups t a y ≤ d.C1pp / P.lEta t * P.ups t x y
  sqrtConvol : ∀ x y, ∑ a, Real.sqrt (P.ups t x a * P.ups t a y) ≤
    d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t * P.ups t x y)
  schwarz : ∀ x₁ x₂ y₁ y₂, ∑ q, Real.sqrt (P.ups t x₁ q * P.ups t x₂ q * P.ups t q y₁ *
    P.ups t q y₂) ≤ d.Cwc / vsHeight P.z t * Real.sqrt (P.ups t x₁ y₁ * P.ups t x₂ y₂)
  sqrtConvolN : ∀ x y, ∑ q, Real.sqrt (P.ups t x q * P.ups t q y) ≤
    d.C1pp / vsHeight P.z t * Real.sqrt ((N : ℝ) * vsHeight P.z t) * Real.sqrt (P.ups t x y)
  stoch : StochasticSymm P.S
  sUps : ∀ x y, ∑ a, P.S x a * P.ups t a y ≤ constS d * P.ups t x y
  kernel : ∀ {k : ℕ} (σ : Fin k → Bool) (j : Fin k) (a q : Fin N),
    ‖aKer P σ j t a q‖ ≤ Propagator.vsCK d * P.ups t a q
  z_im : 0 < P.z.im
  t_nonneg : 0 ≤ t
  t_le_one : t ≤ 1

/-!
## Scalars
-/

section Scalars

variable {d : VSData} {P : PsiData N} {t : ℝ}

/-- `Y = √(Nη)/(ℓη)`. -/
def yScale (P : PsiData N) (t : ℝ) : ℝ := Real.sqrt ((N : ℝ) * vsHeight P.z t) / P.lEta t

theorem yScale_pos (c : FCtx d P t) : 0 < yScale P t := by
  unfold yScale
  have h : 0 < (N : ℝ) * vsHeight P.z t := c.lEta_pos.trans_le c.lEta_le
  exact div_pos (Real.sqrt_pos.mpr h) c.lEta_pos

/-- `(ℓη)^{-1/2} ≤ Y` (from `ℓη ≤ Nη`). -/
theorem rpow_neg_half_le_yScale (c : FCtx d P t) : P.lEta t ^ (-(1 / 2 : ℝ)) ≤ yScale P t := by
  have hL := c.lEta_pos
  have e : P.lEta t ^ (-(1 / 2 : ℝ)) = Real.sqrt (P.lEta t) / P.lEta t := by
    rw [show (-(1 / 2 : ℝ)) = 1 / 2 - 1 by norm_num, Real.rpow_sub hL, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [e, yScale]
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt c.lEta_le) hL.le

/-- `(ℓη)^{-1} ≤ Y` (from `1 ≤ ℓη ≤ Nη`). -/
theorem inv_lEta_le_yScale (c : FCtx d P t) : (P.lEta t)⁻¹ ≤ yScale P t := by
  have hL := c.lEta_pos
  have h1 : 1 ≤ Real.sqrt ((N : ℝ) * vsHeight P.z t) :=
    Real.one_le_sqrt.mpr (c.one_le_lEta.trans c.lEta_le)
  rw [yScale, inv_eq_one_div]
  exact div_le_div_of_nonneg_right h1 hL.le

/-- `L^a ≤ L^b` for `a ≤ b` and `L ≥ 1`. -/
theorem lEta_rpow_le (c : FCtx d P t) {a b : ℝ} (h : a ≤ b) :
    P.lEta t ^ a ≤ P.lEta t ^ b :=
  Real.rpow_le_rpow_of_exponent_le c.one_le_lEta h

theorem lEta_rpow_pos (c : FCtx d P t) (a : ℝ) : 0 < P.lEta t ^ a :=
  Real.rpow_pos_of_pos c.lEta_pos a

theorem lEta_rpow_add (c : FCtx d P t) (a b : ℝ) :
    P.lEta t ^ a * P.lEta t ^ b = P.lEta t ^ (a + b) :=
  (Real.rpow_add c.lEta_pos a b).symm

end Scalars

/-!
## Loss exponents at `K = 8`
-/

theorem lossAlpha_nonneg (k : ℕ) : 0 ≤ lossAlpha k := by
  unfold lossAlpha
  split_ifs
  · exact le_rfl
  · positivity

theorem lossAlpha_eq_zero {k : ℕ} (hk : k ≤ 4) : lossAlpha k = 0 := by
  unfold lossAlpha
  rw [ite_eq_left hk]

theorem lossAlpha_five : lossAlpha 5 = 1 / 4 := by
  unfold lossAlpha
  rw [ite_eq_right (by norm_num), show 2 * ((5 : ℕ) : ℝ) / 8 - 1 = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

theorem lossAlpha_eight : lossAlpha 8 = 1 / 2 := by
  unfold lossAlpha
  rw [ite_eq_right (by norm_num), show 2 * ((8 : ℕ) : ℝ) / 8 - 1 = 1 by norm_num, Real.sqrt_one]

theorem lossAlpha_mono {j k : ℕ} (h : j ≤ k) : lossAlpha j ≤ lossAlpha k := by
  by_cases hj : j ≤ 4
  · rw [lossAlpha_eq_zero hj]
    exact lossAlpha_nonneg k
  · unfold lossAlpha
    rw [ite_eq_right hj, ite_eq_right (by omega)]
    have : (j : ℝ) ≤ k := by exact_mod_cast h
    gcongr

theorem lossBeta_eq {k : ℕ} (hk : k ≤ 7) : lossBeta k = lossAlpha (k + 1) := by
  unfold lossBeta
  rw [ite_eq_left hk]

theorem lossBeta_eight : lossBeta 8 = 3 / 4 := by
  unfold lossBeta
  rw [ite_eq_right (by norm_num), lossAlpha_five]
  norm_num

/-- `α_j + α_{k-j+1} ≤ α_k` for `1 ≤ j ≤ k ≤ 8`. -/
theorem lossAlpha_add_le_X3 {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (hk : k ≤ 8) :
    lossAlpha j + lossAlpha (k - j + 1) ≤ lossAlpha k := by
  by_cases h1 : j ≤ 4
  · rw [lossAlpha_eq_zero h1, zero_add]
    exact lossAlpha_mono (by omega)
  · rw [lossAlpha_eq_zero (show k - j + 1 ≤ 4 by omega), add_zero]
    exact lossAlpha_mono hjk

/-- `α_p + α_{k+2-p} ≤ α_k` for `2 ≤ p ≤ k ≤ 8` (tight at `k = 8`, `p = 5`). -/
theorem lossAlpha_add_le_X4 {p k : ℕ} (hp : 2 ≤ p) (hpk : p ≤ k) (hk : k ≤ 8) :
    lossAlpha p + lossAlpha (k + 2 - p) ≤ lossAlpha k := by
  by_cases h1 : p ≤ 4
  · rw [lossAlpha_eq_zero h1, zero_add]
    exact lossAlpha_mono (by omega)
  · by_cases h2 : k + 2 - p ≤ 4
    · rw [lossAlpha_eq_zero h2, add_zero]
      exact lossAlpha_mono hpk
    · have hk8 : k = 8 := by omega
      have hp5 : p = 5 := by omega
      subst hk8 hp5
      rw [show 8 + 2 - 5 = 5 by norm_num, lossAlpha_five, lossAlpha_eight]
      norm_num

/-!
## Pointwise a priori bounds
-/

section APriori

variable {d : VSData} {P : PsiData N} {t : ℝ}

theorem sIso_pos (c : FCtx d P t) {k : ℕ} (a b : Fin N) (x : Fin k → Fin N) :
    0 < P.sIso a b x t := by
  unfold PsiData.sIso
  refine mul_pos (Real.rpow_pos_of_pos c.lEta_pos _) (Real.sqrt_pos.mpr ?_)
  exact Finset.prod_pos fun i _ => c.pos _ _

theorem sAv_pos (c : FCtx d P t) {k : ℕ} (x : Fin k → Fin N) : 0 < P.sAv x t := by
  unfold PsiData.sAv
  split_ifs
  · exact inv_pos.mpr c.lEta_pos
  · refine mul_pos (Real.rpow_pos_of_pos c.lEta_pos _) (Real.sqrt_pos.mpr ?_)
    exact Finset.prod_pos fun i _ => c.pos _ _

theorem norm_isoErr_le (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ} {psiI psiA : ℕ → ℝ}
    (hAP : APriori P t H psiI psiA) {n : ℕ} (hn : n ∈ kRange) (σ : Fin n → Bool)
    (a b : Fin N) (x : Fin n → Fin N) :
    ‖P.isoErr σ a b x t H‖ ≤ psiI n * P.lEta t ^ lossAlpha n * P.sIso a b x t := by
  have hd : 0 < P.lEta t ^ lossAlpha n * P.sIso a b x t :=
    mul_pos (lEta_rpow_pos c _) (sIso_pos c a b x)
  have h := (P.isoRatio_le_bigPsiIso (σ, a, b, x) t H).trans (hAP n hn).1
  unfold PsiData.isoRatio at h
  rw [div_le_iff₀ hd] at h
  calc ‖P.isoErr σ a b x t H‖ ≤ psiI n * (P.lEta t ^ lossAlpha n * P.sIso a b x t) := h
    _ = _ := by ring

theorem norm_avErr_le (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ} {psiI psiA : ℕ → ℝ}
    (hAP : APriori P t H psiI psiA) {n : ℕ} (hn : n ∈ kRange) (σ : Fin n → Bool)
    (x : Fin n → Fin N) :
    ‖P.avErr σ x t H‖ ≤ psiA n * P.lEta t ^ lossBeta n * P.sAv x t := by
  have hd : 0 < P.lEta t ^ lossBeta n * P.sAv x t :=
    mul_pos (lEta_rpow_pos c _) (sAv_pos c x)
  have h := (P.avRatio_le_bigPsiAv (σ, x) t H).trans (hAP n hn).2
  unfold PsiData.avRatio at h
  rw [div_le_iff₀ hd] at h
  calc ‖P.avErr σ x t H‖ ≤ psiA n * (P.lEta t ^ lossBeta n * P.sAv x t) := h
    _ = _ := by ring

/-- The resolvent chain entry: `G = 𝒴 + δ M` (`isoErr` subtracts the diagonal `M`-term). -/
theorem gChain_iso_eq (P : PsiData N) {n : ℕ} (σ : Fin n → Bool) (a b : Fin N)
    (x : Fin n → Fin N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    gChain (patZ P.z σ t) (isoSlots P.S x) H a b =
      P.isoErr σ a b x t H + if a = b then P.mChain σ x t a else 0 := by
  rw [PsiData.isoErr]
  ring

/-- `|G_{ab}| ≤ ψ L^α s^iso + δ_ab I √L s^iso` -/
theorem norm_gChain_le (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ} {psiI psiA : ℕ → ℝ}
    (hAP : APriori P t H psiI psiA) {n : ℕ} (hn : n ∈ kRange) {I : ℝ} (hI : IsoBAt P t n I)
    (σ : Fin n → Bool) (a b : Fin N) (x : Fin n → Fin N) :
    ‖gChain (patZ P.z σ t) (isoSlots P.S x) H a b‖ ≤
      psiI n * P.lEta t ^ lossAlpha n * P.sIso a b x t +
        (if a = b then I * Real.sqrt (P.lEta t) * P.sIso a b x t else 0) := by
  rw [gChain_iso_eq]
  refine (norm_add_le _ _).trans (add_le_add (norm_isoErr_le c hAP hn σ a b x) ?_)
  split_ifs with hab
  · subst hab
    exact hI σ x a
  · simp

/-- `|𝒳¹(p)| ≤ ψ^av_1 / (ℓη)` (`β_1 = 0`, `s^av_1 = 1/(ℓη)`). -/
theorem norm_avErr_one_le (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ}
    {psiI psiA : ℕ → ℝ} (hAP : APriori P t H psiI psiA) (σ : Fin 1 → Bool) (x : Fin 1 → Fin N) :
    ‖P.avErr σ x t H‖ ≤ psiA 1 * (P.lEta t)⁻¹ := by
  have h := norm_avErr_le c hAP (by simp [kRange, vsK]) σ x
  have hb : lossBeta 1 = 0 := by
    rw [lossBeta_eq (by norm_num), lossAlpha_eq_zero (by norm_num)]
  rwa [hb, Real.rpow_zero, mul_one, Contr.contr_sAv_one P rfl] at h

end APriori

end BlockBand.Native.ErdosRiabov.Forcing
