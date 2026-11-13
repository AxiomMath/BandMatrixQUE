module

public import BlockBand.Native.ErdosRiabov.MI.Main

/-!
# The averaged master inequality for saturated chains: the general-`r` form

For a saturated pattern the Duhamel form is `Circ.duhamel_av_sat_combMg` (`U = I`,
forcing `T̂^{⊕k}_s[𝒳_s] + 𝓕^av_s`, noise `combMg(δ_u)`). The linear term
`T̂^{⊕k}_s[𝒳_s]` is controlled by the linear-term bounds; the master inequality needs it
**uniformly in `s ∈ (0, T]`** on `{T ≤ τ}`, which is the named hypothesis
* `SatLinBound μ P ψ σ u T B q`: outside an event of probability `≤ q`, on `{T ≤ τ}`,
  `η_s |T̂^{⊕k}_s[𝒳_s](u)| ≤ B L_s^{β_k} s^av_s(u)` for every `s ∈ (0, T]`.
  The linear-term bounds `Circ.linTerm_short`/`linTerm_long` are fixed-time tails at the single
  time `T` and for the last slot; the uniform-in-`s` form needs a grid/continuity step and the sum
  over the `k` slots of `T̂^{⊕k} = Σ_j T̂^{(j)}`.
* **`masterIneq_sat_gen`** (saturated, `k = n+1`):
  `P(T ≤ τ, (B + C_av Φ^{av,f}_k) iF(k/2-β_k) + r mSatC φ^{av,qv}_k ≤ R_T) ≤ 4 e^{-r²/4} + q`.
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
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open BlockBand.SourceProcess.FiniteDriverIntegration
open Expo (lossAlpha lossBeta)
open scoped NNReal ENNReal ComplexConjugate

variable {p : BlockBand.Parameters}

/-- **The saturated linear-term input of the master inequality** (uniformly in
`s ∈ (0, T]`): the `driverLaw μ`-probability that `T ≤ τ` and
`η_s |T̂^{⊕k}_s[𝒳^k_s](u)| > B L_s^{β_k} s^av_{k,s}(u)` for some `s ∈ (0, T]` is at most `q`
(`T̂^{⊕k}_s = propOp (vsTensorGen P.S m m̄ s)`, `τ = tau p P ψ ψ^av`, `k = n+1`). -/
def SatLinBound (μ : Measure p.SiteMatrix) (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ)
    {n : ℕ} (σ : Fin (n + 1) → Bool) (u : Fin (n + 1) → Fin (p.n * p.W)) (T : ℝ≥0)
    (B q : ℝ) : Prop :=
  driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
    ¬ ∀ s ∈ Ioc (0 : ℝ) T, vsHeight P.z s *
      ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s)
        (fun y => P.avErr σ y s (pathH p x s)) u‖ ≤
      B * (P.lEta s ^ lossBeta (n + 1) * P.sAv u s)} ≤ ENNReal.ofReal q

section Main

variable (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (d : VSData)
  {P : PsiData (p.n * p.W)} (hb : d.b = p.b) (hPS : P.S = shortRingProfile p.b p.n p.W)
  (hPW : P.W = p.W) (hPD : P.D = d.D) (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2)
  {psiI psiA : ℕ → ℝ} (hpsi : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) (T : ℝ≥0) (hT1 : (T : ℝ) ≤ 1)
include hb hPS hPW hPD hz hP6 hpsi hT1

/-- **The master inequality, saturated averaged chains** (general-`r` form; `k = n+1 ≤ 8`,
`¬ HasDesatFactor σ`): under `SatLinBound μ P ψ σ u T B q` (`B ≥ 0`),
`P(T ≤ τ, (B + C_av Φ^{av,f}_k) iF(k/2-β_k) + r mSatC φ^{av,qv}_k ≤ |𝒳^k_T(u)|/(L_T^{β_k}
s^av_T(u))) ≤ 4 e^{-r²/4} + q` (martingale part by `QV.martingaleEstimate_sat`).
-/
theorem masterIneq_sat_gen {n : ℕ} (hn : n + 1 ≤ 8) (σ : Fin (n + 1) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 1) → Fin (p.n * p.W)) {B q : ℝ} (hB : 0 ≤ B)
    (hlin : SatLinBound μ P psiI psiA σ u T B q) {r : ℝ} (hr : 0 ≤ r) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
        (B + avConst d (fun _ => Apriori.aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 1))
              (n + 1) * phiAvF psiI psiA (P.lEta T) (yScale P T) (n + 1)) *
            intF d P (((n : ℝ) + 1) / 2 - lossBeta (n + 1)) T +
          r * (mSatC d P (Apriori.aprLamM d (p.n * p.W)) n T *
            qvPhiAv psiI psiA (n + 1) (P.lEta T)) ≤
        ‖P.avErr σ u T (pathH p x T)‖ / (P.lEta T ^ lossBeta (n + 1) * P.sAv u T)} ≤
      4 * ENNReal.ofReal (Real.exp (-(r ^ 2 / 4))) + ENNReal.ofReal q := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hc := Apriori.mbCtx_of_params d hb hPS hPW hPD hz
  have hLam := (Apriori.aprLamM_mBounds hc).1
  set Λ := Apriori.aprLamM d (p.n * p.W)
  set e := eMI d (p.n * p.W) (n + 1)
  have he0 : 0 ≤ e := eMI_nonneg d hN _
  have hτ := tau_isStoppingTime μ hN hW hzi hS psiI psiA
  have hI : ∀ j, 1 ≤ psiI j := fun j => (hpsi j).1
  have hAv : ∀ j, 0 ≤ psiA j := fun j => by linarith [(hpsi j).2]
  have hAPae := Apriori.qvAPriori_ae μ d hc (psiI := psiI) (psiA := psiA)
    (fun k _ => by linarith [(hpsi k).1]) (fun k _ => by linarith [(hpsi k).2]) T
  have hLT := P.lEta_pos hN hW hzi hT1
  set β := lossBeta (n + 1)
  set den := P.lEta T ^ β * P.sAv u T
  have hden : 0 < den := mul_pos (Real.rpow_pos_of_pos hLT _) (P.sAv_pos hN hW hzi hT1 u)
  set φq := qvPhiAv psiI psiA (n + 1) (P.lEta T)
  have hφq : 0 < φq := qvPhiAv_pos hI hAv (n + 1) hLT
  set M := mSatC d P Λ n T
  have hγM : 0 ≤ (n : ℝ) + 1 - 2 * β := by
    have h1 := qv_beta_le_one (k := n + 1) hn
    by_cases h0 : n = 0
    · subst h0
      have : β = 0 := by
        simp only [β]
        rw [lossBeta_eq (by norm_num), qv_alpha_of_le_four (by norm_num)]
      rw [this]; norm_num
    · have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      linarith
  have hQI := qvC_mul_intF_pos d P hPW hz hT1 hγM hLam
  have hM : 0 < M := by
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact mul_pos h1 (Real.sqrt_pos.mpr hQI)
  set lam := r * (M * φq * den)
  have hlam : 0 ≤ lam := mul_nonneg hr (by positivity)
  have hAy : qvMartSat d P psiI psiA Λ T u * qvIntRule d P ((n : ℝ) + 1 - 2 * β) T =
      (M * φq * den) ^ 2 := by
    have h := sq_noise (K := (n : ℝ) + 1) (Q := qvC d * Λ ^ 3) (φ := φq)
      (Lp := P.lEta T ^ (n + 1)) (s := P.sAv u T) (y := qvIntRule d P ((n : ℝ) + 1 - 2 * β) T)
      (I := intF d P ((n : ℝ) + 1 - 2 * β) T) (Lb := P.lEta T ^ β)
      (by have := hQI; positivity) (lp_y d P hPW hz hT1 (n + 1) (by push_cast; ring))
    calc _ = ((n : ℝ) + 1) ^ 2 * (qvC d * Λ ^ 3) * φq ^ 2 *
          P.lEta T ^ (n + 1) * P.sAv u T ^ 2 * qvIntRule d P ((n : ℝ) + 1 - 2 * β) T := by
          unfold qvMartSat; ring
      _ = _ := by rw [h]; unfold M mSatC; ring
  have hmart := martingaleEstimate_sat μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAPae hn σ
    u hlam
  have hexp : lam ^ 2 / (4 * (M * φq * den) ^ 2) = r ^ 2 / 4 := by
    have : 0 < M * φq * den := by positivity
    simp only [lam]
    field_simp
  rw [hAy, hexp] at hmart
  refine le_trans (mi_event_le' _ _ T (fun x => ‖P.avErr σ u T (pathH p x T)‖)
    (fun t x => ‖combMg 0 (Evol.zfam P.z σ) (fun y => avSlots P.S y) (fun _ => 1)
      (fun α _ => if α = u then (1 : ℂ) else 0) t x‖)
    (fun x => ∀ s ∈ Ioc (0 : ℝ) T, vsHeight P.z s *
      ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s)
        (fun y => P.avErr σ y s (pathH p x s)) u‖ ≤
      B * (P.lEta s ^ lossBeta (n + 1) * P.sAv u s))
    (F := (B + avConst d (fun _ => Λ) e (n + 1) *
      phiAvF psiI psiA (P.lEta T) (yScale P T) (n + 1)) *
        intF d P (((n : ℝ) + 1) / 2 - β) T) (lam := lam) hden (le_of_eq ?_) ?_)
    (add_le_add hmart hlin)
  · rw [show lam / den = r * (M * φq) by simp only [lam]; field_simp]
  · filter_upwards [Discharge.duhamel_av_sat_combMg_uncond μ hzi hPS (by omega) σ hσ]
      with x hx hTτ hG
    rw [hx T hT1 u]
    have hFi := forcingInt_sat d hb hPS hPW hPD hz hP6 T.2 hT1 hpsi hLam (pathH p x)
      (mi_ap_path d hb hPS hPW hPD hz hpsi T x hTτ) hn he0
      (fun h2 _ s hs => Apriori.mbounds_extra_uncond hc hs.1.le (hs.2.trans hT1) h2) σ u hB hG
    exact (norm_add_le _ _).trans (add_le_add (hFi.trans (le_of_eq rfl))
      le_rfl)

end Main

end BlockBand.Native.ErdosRiabov.MI
