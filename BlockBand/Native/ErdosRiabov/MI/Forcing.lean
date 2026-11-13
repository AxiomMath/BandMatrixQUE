module

public import BlockBand.Native.ErdosRiabov.MI.Phi
public import BlockBand.Native.ErdosRiabov.Discharge.Forcing
public import BlockBand.Native.ErdosRiabov.Circ.BoundBase

/-!
# Master inequalities: the integration factor and the core forcing integral

Deterministic integral estimates for the forcing terms of the master inequalities.

* `intF d P γ T = L_T^γ · y_γ` (`y_γ = QV.qvIntRule d P γ T`): `2/(γ c_m)` for `γ > 0`,
  `c_m⁻¹ log((C₀+1)N)` for `γ = 0`; `rpow_mul_qvIntRule`: `L_T^a y_γ = L_T^{a-γ} iF(γ)`.
* `mi_int_rate`: the integration rule `∫_0^T A L_s^{-γ} η_s⁻¹ ds ≤ A y_γ` (`Circ.circ_intRule`)
  and the interval integrability of the rate.
* **`forcingInt_core`**: if `η_s |f_s(u)| ≤ D L_s^e (L_T/L_s)^c` on `(0,T]` (`D ≥ 0`, `c ≥ e`),
  then `|(∫_0^T f)(u)| ≤ D iF(c-e) L_T^e` (no integrability of `f` needed:
  `Circ.circ_norm_integral_apply_le`).
* `norm_propOp_apply_le`, `pt_propOp`: the pointwise bound of `(U F)(u)` from a bound on `F` and
  the propagator bound `Σ_α |U(u,α)| w(α) ≤ Q`.
* `fAPriori_of`, `isoBAt_of`: the quadratic-variation a priori hypothesis `QV.APriori` at one
  time gives the forcing hypotheses `Forcing.APriori` and `Forcing.IsoBAt` with `I_n = Λ_M`.
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
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open Expo (lossAlpha lossBeta)
open scoped ComplexConjugate

variable {p : BlockBand.Parameters}

/-!
## The integration factor and the integral of the rate
-/

/-- The integration factor `iF(γ) = L_T^γ · y_γ` (`y_γ = qvIntRule d P γ T`). -/
def intF (d : VSData) (P : PsiData (p.n * p.W)) (γ T : ℝ) : ℝ :=
  P.lEta T ^ γ * qvIntRule d P γ T

/-- `‖(M f)(u)‖ ≤ B Q` from `‖f α‖ ≤ B w α` and `Σ_α ‖M u α‖ w α ≤ Q` (`B ≥ 0`). -/
theorem norm_propOp_apply_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (f : ι → ℂ) (u : ι)
    (w : ι → ℝ) {B Q : ℝ} (hB : 0 ≤ B) (hf : ∀ α, ‖f α‖ ≤ B * w α)
    (hQ : ∑ α, ‖M u α‖ * w α ≤ Q) : ‖propOp M f u‖ ≤ B * Q := by
  rw [propOp_apply]
  calc ‖∑ α, M u α * f α‖ ≤ ∑ α, ‖M u α‖ * (B * w α) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hf α) (norm_nonneg _))
    _ = B * ∑ α, ‖M u α‖ * w α := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ => by ring
    _ ≤ B * Q := mul_le_mul_of_nonneg_left hQ hB

section Rate

variable (d : VSData) (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
include hPW hz

/-- The integration rule as an interval integral: `∫_0^T A L_s^{-γ} η_s⁻¹ ds ≤ A y_γ`, and the
rate is interval integrable (`QV.qv_int_rate`, `QV.qv_rate_integrableOn`). -/
theorem mi_int_rate {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) {γ A : ℝ} (hγ : 0 ≤ γ) (hA : 0 ≤ A) :
    IntervalIntegrable (fun s => A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹) volume 0 T ∧
      ∫ s in (0 : ℝ)..T, A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹ ≤ A * qvIntRule d P γ T := by
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr
    (qv_rate_integrableOn d P hPW hz γ A hT1), ?_⟩
  exact Circ.circ_intRule d P hPW hz hγ hA hT0 hT1

theorem mi_rate_nonneg {T : ℝ} (hT1 : T ≤ 1) {γ A : ℝ} (hA : 0 ≤ A) :
    ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹ := by
  intro s hs
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have h1 := vsHeight_pos hη (hs.2.trans hT1)
  have h2 := Real.rpow_nonneg (P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hη
    (hs.2.trans hT1)).le (-γ)
  positivity

/-- `L_T^a y_γ = L_T^{a-γ} iF(γ)`. -/
theorem rpow_mul_qvIntRule {T : ℝ} (hT1 : T ≤ 1) (a γ : ℝ) :
    P.lEta T ^ a * qvIntRule d P γ T = P.lEta T ^ (a - γ) * intF d P γ T := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hL := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) (hz.im_pos hN) hT1
  unfold intF
  rw [← mul_assoc, ← Real.rpow_add hL]
  congr 2
  ring

theorem intF_nonneg {T γ : ℝ} (hT1 : T ≤ 1) (hγ : 0 ≤ γ) : 0 ≤ intF d P γ T := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hL := P.lEta_pos hN (by rw [hPW]; exact p.W_pos) (hz.im_pos hN) hT1
  exact mul_nonneg (Real.rpow_nonneg hL.le _) (qvIntRule_pos d hPW hz hγ hT1).le

/-- **The core forcing integral**: if on `(0, T]`
`η_s |f_s(u)| ≤ D L_s^e (L_T/L_s)^c` with `D ≥ 0`, `0 ≤ c - e`, then
`|(∫_0^T f)(u)| ≤ D iF(c-e) L_T^e`. -/
theorem forcingInt_core {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℝ → ι → ℂ) (u : ι) {T : ℝ}
    (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) {D e c : ℝ} (hD : 0 ≤ D) (hce : 0 ≤ c - e)
    (h : ∀ s ∈ Ioc (0 : ℝ) T,
      vsHeight P.z s * ‖f s u‖ ≤ D * P.lEta s ^ e * (P.lEta T / P.lEta s) ^ c) :
    ‖(∫ s in (0 : ℝ)..T, f s) u‖ ≤ D * intF d P (c - e) T * P.lEta T ^ e := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hη := hz.im_pos hN
  have hLT := P.lEta_pos hN hW hη hT1
  have hA0 : 0 ≤ D * P.lEta T ^ c := mul_nonneg hD (Real.rpow_nonneg hLT.le _)
  obtain ⟨hgi, hgle⟩ := mi_int_rate d P hPW hz hT0 hT1 hce hA0
  refine (Circ.circ_norm_integral_apply_le f u hT0 hgi (mi_rate_nonneg d P hPW hz hT1 hA0)
    fun s hs => ?_).trans ?_
  · have hs1 : s ≤ 1 := hs.2.trans hT1
    have hηs := vsHeight_pos hη hs1
    have hLs := P.lEta_pos hN hW hη hs1
    have e1 : D * P.lEta s ^ e * (P.lEta T / P.lEta s) ^ c =
        D * P.lEta T ^ c * P.lEta s ^ (-(c - e)) := by
      rw [Real.div_rpow hLT.le hLs.le, show -(c - e) = e - c by ring, Real.rpow_sub hLs]
      ring
    have h' := h s hs
    rw [← le_div_iff₀' hηs, e1, div_eq_mul_inv] at h'
    exact h'
  · refine hgle.trans (le_of_eq ?_)
    rw [mul_assoc, rpow_mul_qvIntRule d P hPW hz hT1 c (c - e), show c - (c - e) = e by ring]
    ring

end Rate

/-!
## The a priori input at one time
-/

section AP

variable {N : ℕ} {P : PsiData N} {psiI psiA : ℕ → ℝ} {LamM s : ℝ}
  {H : Matrix (Fin N) (Fin N) ℂ}

/-- `QV.APriori` gives `Forcing.APriori`: `Ψ^{iso/av}_{n,s}(H) ≤ ψ_n` for `n ∈ [1,8]`. -/
theorem fAPriori_of (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) (hs1 : s ≤ 1)
    (hpsi : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) (hA : QV.APriori P psiI psiA LamM s H) :
    Forcing.APriori P s H psiI psiA := by
  intro n hn
  obtain ⟨hn1, hn8⟩ := Finset.mem_Icc.mp hn
  have hL := P.lEta_pos hN hW hz hs1
  constructor
  · unfold PsiData.bigPsiIso
    rw [← Real.coe_toNNReal (psiI n) (by linarith [(hpsi n).1]), NNReal.coe_le_coe]
    refine Finset.sup_le fun i _ => Real.toNNReal_le_toNNReal ?_
    unfold PsiData.isoRatio
    rw [div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hL _) (P.sIso_pos hN hW hz hs1 _ _ _))]
    calc _ ≤ _ := hA.iso n hn1 hn8 i.1 i.2.1 i.2.2.1 i.2.2.2
      _ = _ := by ring
  · unfold PsiData.bigPsiAv
    rw [← Real.coe_toNNReal (psiA n) (by linarith [(hpsi n).2]), NNReal.coe_le_coe]
    refine Finset.sup_le fun i _ => Real.toNNReal_le_toNNReal ?_
    unfold PsiData.avRatio
    rw [div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hL _) (P.sAv_pos hN hW hz hs1 _))]
    calc _ ≤ _ := hA.av n hn1 hn8 i.1 i.2
      _ = _ := by ring

/-- `QV.APriori` gives the isotropic `M`-bound `Forcing.IsoBAt` with `I_n = Λ`. -/
theorem isoBAt_of (hA : QV.APriori P psiI psiA LamM s H) :
    ∀ n ∈ kRange, IsoBAt P s n LamM := by
  intro n hn σ x a
  obtain ⟨hn1, hn8⟩ := Finset.mem_Icc.mp hn
  exact hA.mIso n hn1 hn8 σ a x

end AP

/-!
## The pointwise integrands
-/

/-- `η |(M F)(u)| ≤ C L^e Φ Q` from `η |F(α)| ≤ C (L^e w(α)) Φ` and `Σ_α |M(u,α)| w(α) ≤ Q`. -/
theorem pt_propOp {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (F : ι → ℂ)
    (w : ι → ℝ) (u : ι)
    {η C Le Φ Q : ℝ} (hη : 0 < η) (hC : 0 ≤ C * Le * Φ)
    (hF : ∀ α, η * ‖F α‖ ≤ C * (Le * w α) * Φ) (hG : ∑ α, ‖M u α‖ * w α ≤ Q) :
    η * ‖propOp M F u‖ ≤ C * Le * Φ * Q := by
  have hB : 0 ≤ C * Le * Φ / η := div_nonneg hC hη.le
  have h := norm_propOp_apply_le M F u w hB (fun α => by
    rw [div_mul_eq_mul_div, le_div_iff₀' hη]
    linarith [hF α]) hG
  calc η * ‖propOp M F u‖ ≤ η * (C * Le * Φ / η * Q) := mul_le_mul_of_nonneg_left h hη.le
    _ = C * Le * Φ * Q := by field_simp

end BlockBand.Native.ErdosRiabov.MI
