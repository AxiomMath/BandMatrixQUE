module

public import BlockBand.Native.ErdosRiabov.Apriori.Extra
public import BlockBand.Native.ErdosRiabov.QV.Mart
public import BlockBand.Native.ErdosRiabov.Discharge.Psi

/-!
# The a priori bounds up to the stopping time

The a priori hypotheses of the quadratic-variation and forcing estimates hold along the flow up to
the stopping time `τ`.

* thresholds `aprPsiI d N k = ψ_k = N^{ξ+kν}`, `aprPsiA d N k = ψ^av_k = N^{ξ+(k+3/2)ν}`
  (`VSData.psiIso`, `VSData.psiAv`) with `1 ≤ ψ`;
* `aprLamM d N = 1 + Σ_{k ≤ 8} (A_k + I_k)` (the `M`-bound constants, with `mzeroConst`);
  `aprLamM_mBounds`: `AvB(k, Λ_M) ∧ IsoB(k, Λ_M)` for `1 ≤ k ≤ 8` under `MBCtx` only;
* **Forcing**: `forcingAPriori_of_le_tau`: `Forcing.APriori P s (pathH p x s) ψ ψ^av` (a
  `def`: `Ψ ≤ ψ` on `kRange`);
* **Quadratic variation**: `qvAPriori_of_le_tau`: the structure
  `QV.APriori P ψ ψ^av Λ_M s (pathH p x s)`
  (pointwise `G - M` bounds and the `M`-bounds with `Λ_M`); `qvAPriori_ae`: the hypothesis `hAP`
  of `QV.martingaleEstimate_*` with `τ = Psi.tau p P ψ ψ^av`;
* `aprioriBounds` (both structures at the thresholds `ψ`, `ψ^av`, `H = Evol.pathH p x s`) and
  `aprioriBounds_ae`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Apriori

open MeasureTheory Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.MBound
open BlockBand.SourceProcess BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open Expo (lossAlpha lossBeta)
open scoped NNReal

/-!
## Thresholds and the `M`-bound constant
-/

/-- `ψ_k = N^{ξ+kν}` (`VSData.psiIso`). -/
def aprPsiI (d : VSData) (N : ℕ) : ℕ → ℝ := fun k => d.psiIso N k

/-- `ψ^av_k = N^{ξ+(k+3/2)ν}` (`VSData.psiAv`). -/
def aprPsiA (d : VSData) (N : ℕ) : ℕ → ℝ := fun k => d.psiAv N k

/-- `1 ≤ ψ_k` for `N ≥ 1`. -/
theorem one_le_aprPsiI (d : VSData) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) : 1 ≤ aprPsiI d N k :=
  Real.one_le_rpow (by exact_mod_cast hN)
    (add_nonneg d.xi_pos.le (mul_nonneg (Nat.cast_nonneg k) d.nu_pos.le))

/-- `1 ≤ ψ^av_k` for `N ≥ 1`. -/
theorem one_le_aprPsiA (d : VSData) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) : 1 ≤ aprPsiA d N k :=
  Real.one_le_rpow (by exact_mod_cast hN)
    (add_nonneg d.xi_pos.le (mul_nonneg (by positivity) d.nu_pos.le))

/-- `Λ_M = 1 + Σ_{k ≤ 8} (A_k + I_k)`, `A_k = mbConstA d Λ (mzeroConst d) k`,
`I_k = mbConstI d Λ (mzeroConst d) k`, `Λ = mbLambda d N`. -/
def aprLamM (d : VSData) (N : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range 9, (mbConstA d (mbLambda d N) (MZero.mzeroConst d) j +
    mbConstI d (mbLambda d N) (MZero.mzeroConst d) j)

section M

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in

/-- The `M`-bounds with the single constant `Λ_M` for `1 ≤ k ≤ 8`, from
`Discharge.mbBounds_joint_uncond` (only `MBCtx`):
`1 ≤ Λ_M`, `AvB(k, Λ_M)` and `IsoB(k, Λ_M)`.
-/
theorem aprLamM_mBounds : 1 ≤ aprLamM d (m * W) ∧ ∀ k, 1 ≤ k → k ≤ 8 →
    MBAvB P k (aprLamM d (m * W)) ∧ MBIsoB P k (aprLamM d (m * W)) := by
  have hN : 0 < m * W := Nat.mul_pos (by have := hc.hm; omega) hc.hW
  have hΛ0 : 0 ≤ mbLambda d (m * W) := mbLambda_nonneg d hN
  have hB0 := MZero.mzeroConst_nonneg d
  have hterm : ∀ k ∈ Finset.range 9,
      0 ≤ mbConstA d (mbLambda d (m * W)) (MZero.mzeroConst d) k +
        mbConstI d (mbLambda d (m * W)) (MZero.mzeroConst d) k := fun k _ =>
    add_nonneg (mbConstA_nonneg d _ _ hΛ0 hB0 k) (mbConstI_nonneg d _ _ hΛ0 hB0 k)
  have hsum := Finset.sum_nonneg hterm
  refine ⟨by unfold aprLamM; linarith, fun k hk1 hk8 => ?_⟩
  have hle := Finset.single_le_sum hterm (Finset.mem_range.mpr (by omega : k < 9))
  have hA := mbConstA_nonneg d _ _ hΛ0 hB0 k
  have hI := mbConstI_nonneg d _ _ hΛ0 hB0 k
  obtain ⟨hAv, hIso⟩ := Discharge.mbBounds_joint_uncond hc k hk1
  refine ⟨fun t ht σ x => (hAv t ht σ x).trans (mul_le_mul_of_nonneg_right ?_
    (mb_LsAv_pos_nonneg hc ht x)), fun t ht σ a x => (hIso t ht σ a x).trans
      (mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.sqrt_nonneg _)
        (mb_sIso_nonneg P (hc.inputs ht) _ _ _)))⟩
  · unfold aprLamM
    linarith
  · unfold aprLamM
    linarith

end M

variable {p : BlockBand.Parameters}

/-- `MBCtx d P` from the parameter form of the VS hypotheses (as used by
`QV.martingaleEstimate_*`). -/
theorem mbCtx_of_params (d : VSData) {P : PsiData (p.n * p.W)} (hb : d.b = p.b)
    (hPS : P.S = shortRingProfile p.b p.n p.W) (hPW : P.W = p.W) (hPD : P.D = d.D)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) : MBCtx d P :=
  ⟨p.n_ge_four, p.W_pos, by rw [hPS, hb], hPW, hPD, hz⟩

/-!
## The Forcing a priori hypothesis
-/

/-- **Forcing `APriori` up to `τ`**: for every sample `x` and `s ≥ 0` with
`s ≤ τ(x)`, `Forcing.APriori P s (Evol.pathH p x s) ψ ψ^av` (`Ψ^iso_k ≤ ψ_k`,
`Ψ^av_k ≤ ψ^av_k` for `k ∈ kRange`).
Includes `s = 0`.
-/
theorem forcingAPriori_of_le_tau {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W) (hW : 0 < P.W)
    (hz : 0 < P.z.im) (hS : StochasticSymm P.S) {psiI psiA : ℕ → ℝ}
    (hI : ∀ k ∈ kRange, 0 < psiI k) (hA : ∀ k ∈ kRange, 0 < psiA k) (x : RingSample p)
    {s : ℝ} (hs0 : 0 ≤ s) (hsτ : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ tau p P psiI psiA x) :
    Forcing.APriori P s (Evol.pathH p x s) psiI psiA := by
  have hb := Discharge.bigPsi_le_of_le_tau_of_zero_uncond hN hW hz hS hI hA x hsτ
  have hcoe : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs0
  rw [hcoe] at hb
  exact hb

/-!
## The QV a priori hypothesis
-/

theorem apr_le_one_of_le_tau (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (x : RingSample p)
    {s : ℝ} (hs0 : 0 ≤ s) (hsτ : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ tau p P psiI psiA x) :
    s ≤ 1 := by
  have h := WithTop.coe_le_coe.mp (hsτ.trans (tau_le_one P psiI psiA x))
  have h' : ((s.toNNReal : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast h
  rwa [Real.coe_toNNReal s hs0] at h'

/-- **QV `APriori` up to `τ`**: under `MBCtx d P`, for `ψ, ψ^av > 0` on `kRange`, every sample
`x` and `s ≥ 0` with `s ≤ τ(x)`: `QV.APriori P ψ ψ^av Λ_M s (Evol.pathH p x s)` with
`Λ_M = aprLamM d (n W)`. -/
theorem qvAPriori_of_le_tau (d : VSData) {P : PsiData (p.n * p.W)} (hc : MBCtx d P)
    {psiI psiA : ℕ → ℝ} (hI : ∀ k ∈ kRange, 0 < psiI k) (hA : ∀ k ∈ kRange, 0 < psiA k)
    (x : RingSample p) {s : ℝ} (hs0 : 0 ≤ s)
    (hsτ : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ tau p P psiI psiA x) :
    QV.APriori P psiI psiA (aprLamM d (p.n * p.W)) s (Evol.pathH p x s) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := hc.hm; omega) hc.hW
  have hW : 0 < P.W := by rw [hc.hPW]; exact hc.hW
  have hz := hc.zpos
  have hs1 := apr_le_one_of_le_tau P psiI psiA x hs0 hsτ
  have hb := forcingAPriori_of_le_tau hN hW hz hc.stoch hI hA x hs0 hsτ
  have hL := P.lEta_pos hN hW hz hs1
  have hkr : ∀ k, 1 ≤ k → k ≤ 8 → k ∈ kRange := fun k h1 h8 => by
    simp only [kRange, vsK, Finset.mem_Icc]
    exact ⟨h1, h8⟩
  obtain ⟨-, hM⟩ := aprLamM_mBounds hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk1 hk8 σ a b y
    have h1 := (P.isoRatio_le_bigPsiIso (σ, a, b, y) s _).trans (hb k (hkr k hk1 hk8)).1
    have hden : 0 < P.lEta s ^ lossAlpha k * P.sIso a b y s :=
      mul_pos (Real.rpow_pos_of_pos hL _) (P.sIso_pos hN hW hz hs1 a b y)
    have h2 := (div_le_iff₀ hden).mp h1
    calc _ ≤ _ := h2
      _ = _ := by ring
  · intro k hk1 hk8 σ y
    have h1 := (P.avRatio_le_bigPsiAv (σ, y) s _).trans (hb k (hkr k hk1 hk8)).2
    have hden : 0 < P.lEta s ^ lossBeta k * P.sAv y s :=
      mul_pos (Real.rpow_pos_of_pos hL _) (P.sAv_pos hN hW hz hs1 y)
    have h2 := (div_le_iff₀ hden).mp h1
    calc _ ≤ _ := h2
      _ = _ := by ring
  · intro k hk1 hk8 σ a y
    have h := (hM k hk1 hk8).2 s ⟨hs0, hs1⟩ σ a y
    calc _ ≤ _ := h
      _ = _ := by ring
  · intro k hk1 hk8 σ y
    have h := (hM k hk1 hk8).1 s ⟨hs0, hs1⟩ σ y
    unfold Evol.avM at h
    calc _ ≤ _ := h
      _ = _ := by ring

/-- **QV `APriori`, almost-sure form**: the hypothesis `hAP` of
`QV.martingaleEstimate_*` with `τ = Psi.tau p P ψ ψ^av` and `Λ_M = aprLamM`
(it holds for every sample).
-/
theorem qvAPriori_ae (μ : Measure p.SiteMatrix) (d : VSData) {P : PsiData (p.n * p.W)}
    (hc : MBCtx d P) {psiI psiA : ℕ → ℝ} (hI : ∀ k ∈ kRange, 0 < psiI k)
    (hA : ∀ k ∈ kRange, 0 < psiA k) (T : ℝ≥0) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ tau p P psiI psiA x →
        QV.APriori P psiI psiA (aprLamM d (p.n * p.W)) s (Evol.pathH p x s) :=
  Filter.Eventually.of_forall fun x _ hs hsτ =>
    qvAPriori_of_le_tau d hc hI hA x hs.1.le hsτ

/-!
## Both a priori hypotheses at the thresholds
-/

theorem aprPsi_pos (d : VSData) {N : ℕ} (hN : 1 ≤ N) :
    (∀ k ∈ kRange, 0 < aprPsiI d N k) ∧ ∀ k ∈ kRange, 0 < aprPsiA d N k :=
  ⟨fun k _ => lt_of_lt_of_le one_pos (one_le_aprPsiI d hN k),
    fun k _ => lt_of_lt_of_le one_pos (one_le_aprPsiA d hN k)⟩

/-- **Both a priori structures at the thresholds `ψ`, `ψ^av`**: under `MBCtx d P`,
for every sample `x` and `s ≥ 0` with `s ≤ τ(x)`, `τ = Psi.tau p P ψ ψ^av`,
`ψ = aprPsiI d (n W)`, `ψ^av = aprPsiA d (n W)`, at `H = Evol.pathH p x s`:
`Forcing.APriori P s H ψ ψ^av` and `QV.APriori P ψ ψ^av Λ_M s H`, `Λ_M = aprLamM d (n W) ≥ 1`.
Deterministic; unconditional.
-/
theorem aprioriBounds (d : VSData) {P : PsiData (p.n * p.W)} (hc : MBCtx d P)
    (x : RingSample p) {s : ℝ} (hs0 : 0 ≤ s)
    (hsτ : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤
      tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) x) :
    Forcing.APriori P s (Evol.pathH p x s) (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) ∧
      QV.APriori P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) (aprLamM d (p.n * p.W)) s
        (Evol.pathH p x s) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := hc.hm; omega) hc.hW
  have hW : 0 < P.W := by rw [hc.hPW]; exact hc.hW
  obtain ⟨hI, hA⟩ := aprPsi_pos d (N := p.n * p.W) hN
  exact ⟨forcingAPriori_of_le_tau hN hW hc.zpos hc.stoch hI hA x hs0 hsτ,
    qvAPriori_of_le_tau d hc hI hA x hs0 hsτ⟩

/-- **Almost-sure form of `aprioriBounds`**: for every `T`, almost surely, for all `s ∈ (0, T]` with
`s ≤ τ(x)`, both `Forcing.APriori` and `QV.APriori` hold at the thresholds (the QV component is the
hypothesis `hAP` of `QV.martingaleEstimate_*`). -/
theorem aprioriBounds_ae (μ : Measure p.SiteMatrix) (d : VSData) {P : PsiData (p.n * p.W)}
    (hc : MBCtx d P) (T : ℝ≥0) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤
        tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) x →
      Forcing.APriori P s (Evol.pathH p x s) (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) ∧
        QV.APriori P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) (aprLamM d (p.n * p.W)) s
          (Evol.pathH p x s) :=
  Filter.Eventually.of_forall fun x _ hs hsτ => aprioriBounds d hc x hs.1.le hsτ

end BlockBand.Native.ErdosRiabov.Apriori
