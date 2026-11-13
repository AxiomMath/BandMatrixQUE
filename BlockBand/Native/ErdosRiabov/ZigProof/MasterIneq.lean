module

public import BlockBand.Native.ErdosRiabov.Assembly.Zig
public import BlockBand.Native.ErdosRiabov.Psi.TauFacts

/-!
# The fixed-time master-inequality hypothesis of the zig step

The thresholds, the stopping time and the master-inequality levels of the zig step, the
fixed-time hypothesis `MasterIneqConclusion`, and counting and margin lemmas for the bootstrap.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.ZigProof

open MeasureTheory Set Filter
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Assembly
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

/-!
### Thresholds, stopping time, master-inequality levels
-/

/-- The isotropic thresholds `k ↦ ψ^iso_k = N^{ξ+kν}` as an `ℕ`-indexed family. -/
def zigPsiI (d : VSData) (N : ℕ) : ℕ → ℝ := fun k => d.psiIso N k

/-- The averaged thresholds `k ↦ ψ^av_k = N^{ξ+(k+3/2)ν}` as an `ℕ`-indexed family. -/
def zigPsiA (d : VSData) (N : ℕ) : ℕ → ℝ := fun k => d.psiAv N k

/-- The stopping time `τ` of the zig step: `Psi.tau` for the control data
`zigPsiData p d.D z` and the thresholds `zigPsiI`, `zigPsiA`. -/
def zigTau (p : BlockBand.Parameters) (d : VSData) (z : ℂ) (x : RingSample p) : WithTop ℝ≥0 :=
  tau p (zigPsiData p d.D z) (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) x

/-- The isotropic master-inequality level `N^{ε'} C (N^ξ + N^{-ν/2} ψ^iso_k)` (`ε' = d.epsP`). -/
def miLevelIso (d : VSData) (C : ℝ) (N k : ℕ) : ℝ :=
  (N : ℝ) ^ d.epsP * (C * ((N : ℝ) ^ d.xi + (N : ℝ) ^ (-d.nu / 2) * d.psiIso N k))

/-- The averaged master-inequality level `N^{ε'} C (N^ξ + N^{-ν/2} ψ^av_k)` (`ε' = d.epsP`). -/
def miLevelAv (d : VSData) (C : ℝ) (N k : ℕ) : ℝ :=
  (N : ℝ) ^ d.epsP * (C * ((N : ℝ) ^ d.xi + (N : ℝ) ^ (-d.nu / 2) * d.psiAv N k))

/-- **The fixed-time master inequalities after the exponent inequality (statement only).**
For every `d : VSData` and `D > 0` there are `C > 0` and `N₀: ℕ` (depending only on `d`, `D`)
such that for every ring `p` with `p.b = d.b`, `N = p.n * p.W ≥ N₀`, `ζ₀ < 1` and
`N^{1+ζ₀} ≤ W²`, every `GaussianRingModel`, every `z ∈ 𝒟`, every deterministic `t ∈ [0,1]`,
every `k ∈ kRange = [1,8]`, every isotropic index `i` (pattern, sites) and every averaged index,
under `driverLaw model.law`:
`P(t ≤ τ ∧ N^{ε'} C (N^ξ + N^{-ν/2} ψ^iso_k) < isoRatio i t H_t) ≤ N^{-D}` and
`P(t ≤ τ ∧ N^{ε'} C (N^ξ + N^{-ν/2} ψ^av_k) < avRatio i t H_t) ≤ N^{-D}`, with
`τ = zigTau p d z`, `H_t = VS.vsBandFin p t`, `ε' = d.epsP`.
This is the fixed-time master inequality combined with the exponent inequality
`Flow.Expo.phi_le`; it is the input of `zigConclusion_of_masterIneq`, and it follows from
`masterIneqConclusion_of_phi`, `MI.masterIneqPhi_of_MI` and `SatLin.masterIneqSat`.
-/
def MasterIneqConclusion : Prop :=
  ∀ (d : VSData) (D : ℝ), 0 < D → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W → d.zeta0 < 1 →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ),
        BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z →
        ∀ t : ℝ≥0, t ≤ 1 → ∀ k ∈ kRange,
          (∀ i : IsoIdx (p.n * p.W) k,
            driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
                {x | (t : WithTop ℝ≥0) ≤ zigTau p d z x ∧
                  miLevelIso d C (p.n * p.W) k <
                    (zigPsiData p d.D z).isoRatio i t (VS.vsBandFin p t x)} ≤
              ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D))) ∧
          ∀ i : AvIdx (p.n * p.W) k,
            driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
                {x | (t : WithTop ℝ≥0) ≤ zigTau p d z x ∧
                  miLevelAv d C (p.n * p.W) k <
                    (zigPsiData p d.D z).avRatio i t (VS.vsBandFin p t x)} ≤
              ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D))

/-!
### `ζ₀ ≥ 1` contradicts `N^{1+ζ₀} ≤ W²` (so w.l.o.g. `ζ₀ < 1`)
-/

/-- **For `ζ₀ ≥ 1` the band hypothesis never holds**: `N = nW ≥ 4W`, so
`N^{1+ζ₀} ≥ N² ≥ 16 W² > W²`. -/
theorem band_hyp_false_of_one_le_zeta0 (p : BlockBand.Parameters) {ζ₀ : ℝ} (h : 1 ≤ ζ₀) :
    ¬ ((p.n * p.W : ℕ) : ℝ) ^ (1 + ζ₀) ≤ (p.W : ℝ) ^ 2 := by
  intro hb
  have hn : (4 : ℝ) ≤ p.n := by exact_mod_cast p.n_ge_four
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hN1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by push_cast; nlinarith
  have h2 : ((p.n * p.W : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) ^ (1 + ζ₀) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [Real.rpow_two] at h2
  push_cast at h2 hb
  have h16 : (16 : ℝ) ≤ (p.n : ℝ) ^ 2 := by nlinarith
  have hsq : ((p.n : ℝ) * p.W) ^ 2 = (p.n : ℝ) ^ 2 * (p.W : ℝ) ^ 2 := by ring
  have hW2 : (1 : ℝ) ≤ (p.W : ℝ) ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h16 (by positivity : (0 : ℝ) ≤ (p.W : ℝ) ^ 2)
  linarith

/-!
### Counting
-/

/-- `|IsoIdx N k| = 2^k N^{k+2} ≤ 256 N^{10}` for `k ≤ 8`. -/
theorem card_isoIdx_le {N k : ℕ} (hN : 0 < N) (hk : k ≤ 8) :
    (Fintype.card (IsoIdx N k) : ℝ) ≤ 256 * (N : ℝ) ^ (10 : ℝ) := by
  have h : Fintype.card (IsoIdx N k) = 2 ^ k * (N * (N * N ^ k)) := by
    simp only [IsoIdx, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h2 : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hk
  have h3 : N ^ k ≤ N ^ 8 := Nat.pow_le_pow_right hN hk
  have h4 : 2 ^ k * (N * (N * N ^ k)) ≤ 256 * N ^ 10 := by
    calc 2 ^ k * (N * (N * N ^ k)) ≤ 2 ^ 8 * (N * (N * N ^ 8)) := by gcongr
      _ = 256 * N ^ 10 := by ring
  rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, h]
  exact_mod_cast h4

/-- `|AvIdx N k| = 2^k N^k ≤ 256 N^{10}` for `k ≤ 8`. -/
theorem card_avIdx_le {N k : ℕ} (hN : 0 < N) (hk : k ≤ 8) :
    (Fintype.card (AvIdx N k) : ℝ) ≤ 256 * (N : ℝ) ^ (10 : ℝ) := by
  have h : Fintype.card (AvIdx N k) = 2 ^ k * N ^ k := by
    simp only [AvIdx, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h2 : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hk
  have h3 : N ^ k ≤ N ^ 10 := Nat.pow_le_pow_right hN (by omega)
  have h4 : 2 ^ k * N ^ k ≤ 256 * N ^ 10 := by
    calc 2 ^ k * N ^ k ≤ 2 ^ 8 * N ^ 10 := by gcongr
      _ = 256 * N ^ 10 := by norm_num
  rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, h]
  exact_mod_cast h4

/-- `|kRange| = 8`. -/
theorem card_kRange : kRange.card = 8 := by
  simp [kRange, vsK]

/-!
### The strict maximum
-/

/-- For `X ≥ 0`, `X < Ψ^iso_{k,t}(H)` gives an isotropic index with `X < isoRatio i t H`. -/
theorem exists_lt_isoRatio {N k : ℕ} (P : PsiData N) {t : ℝ} {H : Matrix (Fin N) (Fin N) ℂ}
    {X : ℝ} (hX : 0 ≤ X) (h : X < P.bigPsiIso k t H) :
    ∃ i : IsoIdx N k, X < P.isoRatio i t H := by
  unfold PsiData.bigPsiIso at h
  have h1 : X.toNNReal < Finset.univ.sup fun i : IsoIdx N k => (P.isoRatio i t H).toNNReal :=
    (Real.toNNReal_lt_iff_lt_coe hX).2 h
  obtain ⟨i, -, hi⟩ := Finset.lt_sup_iff.1 h1
  refine ⟨i, ?_⟩
  by_contra hc
  exact absurd hi (not_lt.2 (Real.toNNReal_le_toNNReal (not_lt.1 hc)))

/-- For `X ≥ 0`, `X < Ψ^av_{k,t}(H)` gives an averaged index with `X < avRatio i t H`. -/
theorem exists_lt_avRatio {N k : ℕ} (P : PsiData N) {t : ℝ} {H : Matrix (Fin N) (Fin N) ℂ}
    {X : ℝ} (hX : 0 ≤ X) (h : X < P.bigPsiAv k t H) :
    ∃ i : AvIdx N k, X < P.avRatio i t H := by
  unfold PsiData.bigPsiAv at h
  have h1 : X.toNNReal < Finset.univ.sup fun i : AvIdx N k => (P.avRatio i t H).toNNReal :=
    (Real.toNNReal_lt_iff_lt_coe hX).2 h
  obtain ⟨i, -, hi⟩ := Finset.lt_sup_iff.1 h1
  refine ⟨i, ?_⟩
  by_contra hc
  exact absurd hi (not_lt.2 (Real.toNNReal_le_toNNReal (not_lt.1 hc)))

/-!
### The margin (exponent check of the bootstrap)
-/

/-- **Margin.** For `N ≥ 1`, `ξ ≥ 0`, `ν > 0`, `C > 0`, `ψ ≥ N^{ξ+ν}` and
`4C + 1 < N^{7ν/16}`:
`2 N^{ν/16} C (N^ξ + N^{-ν/2} ψ) + N^{-1} < ψ`.
With `ν/16 = ε'` this is
`2X + N^{-1} < ψ_k` for the MI level `X` (the grid form `2X + N^{-1}`).
-/
theorem margin_lt {N ξ ν C ψ : ℝ} (hN : 1 ≤ N) (hξ : 0 ≤ ξ) (hν : 0 < ν) (hC : 0 < C)
    (hψ : N ^ (ξ + ν) ≤ ψ) (hbig : 4 * C + 1 < N ^ (7 * ν / 16)) :
    2 * (N ^ (ν / 16) * (C * (N ^ ξ + N ^ (-ν / 2) * ψ))) + N⁻¹ < ψ := by
  have hN0 : 0 < N := by linarith
  have hψ0 : 0 < ψ := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hψ
  have hq0 : 0 < N ^ (-(7 * ν / 16)) := Real.rpow_pos_of_pos hN0 _
  have ha0 : 0 ≤ N ^ (ν / 16) := (Real.rpow_pos_of_pos hN0 _).le
  have hA : N ^ ξ ≤ N ^ (-ν) * ψ := by
    have h : N ^ ξ = N ^ (-ν) * N ^ (ξ + ν) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    rw [h]
    exact mul_le_mul_of_nonneg_left hψ (Real.rpow_nonneg hN0.le _)
  have hr : N ^ (-ν) ≤ N ^ (-(7 * ν / 16)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have har : N ^ (ν / 16) * N ^ (-ν) ≤ N ^ (-(7 * ν / 16)) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have haB : N ^ (ν / 16) * N ^ (-ν / 2) = N ^ (-(7 * ν / 16)) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hinv : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  have h1 : 1 ≤ N ^ ξ := Real.one_le_rpow hN hξ
  have hqQ : N ^ (-(7 * ν / 16)) * N ^ (7 * ν / 16) = 1 := by
    rw [← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero]
  have e1 : N ^ (ν / 16) * N ^ ξ ≤ N ^ (-(7 * ν / 16)) * ψ := by
    calc N ^ (ν / 16) * N ^ ξ ≤ N ^ (ν / 16) * (N ^ (-ν) * ψ) :=
          mul_le_mul_of_nonneg_left hA ha0
      _ = (N ^ (ν / 16) * N ^ (-ν)) * ψ := by ring
      _ ≤ N ^ (-(7 * ν / 16)) * ψ := mul_le_mul_of_nonneg_right har hψ0.le
  have e2 : N⁻¹ ≤ N ^ (-(7 * ν / 16)) * ψ := by
    calc N⁻¹ ≤ 1 := hinv
      _ ≤ N ^ ξ := h1
      _ ≤ N ^ (-ν) * ψ := hA
      _ ≤ N ^ (-(7 * ν / 16)) * ψ := mul_le_mul_of_nonneg_right hr hψ0.le
  have e3 : 2 * (N ^ (ν / 16) * (C * (N ^ ξ + N ^ (-ν / 2) * ψ))) =
      2 * C * (N ^ (ν / 16) * N ^ ξ) + 2 * C * ((N ^ (ν / 16) * N ^ (-ν / 2)) * ψ) := by ring
  have key : 2 * (N ^ (ν / 16) * (C * (N ^ ξ + N ^ (-ν / 2) * ψ))) + N⁻¹ ≤
      (4 * C + 1) * N ^ (-(7 * ν / 16)) * ψ := by
    rw [e3, haB]
    nlinarith [mul_le_mul_of_nonneg_left e1 (by linarith : (0 : ℝ) ≤ 2 * C)]
  calc _ ≤ (4 * C + 1) * N ^ (-(7 * ν / 16)) * ψ := key
    _ < N ^ (7 * ν / 16) * N ^ (-(7 * ν / 16)) * ψ := by
        apply mul_lt_mul_of_pos_right _ hψ0
        exact mul_lt_mul_of_pos_right hbig hq0
    _ = ψ := by rw [mul_comm (N ^ (7 * ν / 16)), hqQ, one_mul]

/-- The size condition of `margin_lt` holds for all large `N`: there is `R` with
`4C + 1 < N^{7ν/16}` for `N ≥ R` (`ν > 0`). -/
theorem exists_margin_threshold (C : ℝ) {ν : ℝ} (hν : 0 < ν) :
    ∃ R : ℝ, ∀ N : ℝ, R ≤ N → 4 * C + 1 < N ^ (7 * ν / 16) :=
  Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < 7 * ν / 16)).eventually_gt_atTop (4 * C + 1))

/-- The thresholds at levels `k ≥ 1` are at least `N^{ξ+ν}`. -/
theorem rpow_le_psi {d : VSData} {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : 1 ≤ k) :
    (N : ℝ) ^ (d.xi + d.nu) ≤ d.psiIso N k ∧ (N : ℝ) ^ (d.xi + d.nu) ≤ d.psiAv N k := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnu := d.nu_pos
  unfold VSData.psiIso VSData.psiAv
  refine ⟨Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith),
    Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)⟩

end BlockBand.Native.ErdosRiabov.ZigProof
