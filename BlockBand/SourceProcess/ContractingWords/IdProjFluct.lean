module

public import BlockBand.SourceProcess.ContractingWords.IdProjMean
public import BlockBand.SourceProcess.ContractingWords.LayerFreshHolds

/-!
# `SepFluctIdProj`: centered bilinear bounds of `NN*`, `NPN*`, bulk-uniform

**`sepFluctIdProj_holds hGA hLp : SepFluctIdProj`.** Measure `freshLaw W b`, deterministic
Hermitian `𝕏`, `L^Q` norm (`eLpNorm`, `Q ≥ 1`), constants depending on `b, κ, Q` only.
* `crude_fluct`: for every separator, `‖u*(T_σ - ET_σ)v‖_Q ≤ K‖u‖‖v‖` (`‖T_σ‖ ≤ ‖N‖²` a.s.,
  `‖ET_σ‖ ≤ μ` from `fresh_basic`, `‖‖N‖‖_{2Q} ≤ C` from `fullSourceMoments_field_holds`);
* `σ = I`: on `δ₀ ≤ d₀`, `FullSourceEstimates.fluct` (`bilinear_id`); off it, `crude_fluct`
  and `1 ≤ min(1,δ₀)/min(1,d₀)`;
* `σ = P`: `bilinear_proj` and `PassiveBoundsStatement.bilinear` at `w = z_∂` (`uAt_boundaryZ`),
  `‖ιu‖ ≤ ‖u‖`; no domain restriction.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem crude_pointwise {T M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {n μ : ℝ}
    (hT : ‖T‖ ≤ n ^ 2) (hM : ‖M‖ ≤ μ) (hn : 0 ≤ n) (u v : Fin 2 × Fin W → ℂ) :
    ‖bilinear u (T - M) v‖ ≤ (vecNorm u * vecNorm v * (1 + μ)) * (1 + n + 0) ^ 2 := by
  have hu := vecNorm_nonneg u
  have hv := vecNorm_nonneg v
  have hμ : 0 ≤ μ := (norm_nonneg _).trans hM
  refine (norm_bilinear_le u _ v).trans ?_
  have h1 : ‖T - M‖ ≤ (1 + μ) * (1 + n + 0) ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    nlinarith [mul_nonneg hμ hn, mul_nonneg hμ (sq_nonneg n)]
  calc vecNorm u * ‖T - M‖ * vecNorm v ≤ vecNorm u * ((1 + μ) * (1 + n + 0) ^ 2) * vecNorm v := by
        gcongr
    _ = _ := by ring

/-- **Crude centered bound**, every separator, bulk-uniform. -/
theorem crude_fluct (hGA : GaussianAbsorptionContract) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ σ : Separator, ∀ u v : Fin 2 × Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (transportedSep b E XX σ ω -
            matrixExpect (freshLaw W b) (transportedSep b E XX σ)) v) (ENNReal.ofReal Q)
            (freshLaw W b) ≤ ENNReal.ofReal (K * vecNorm u * vecNorm v) := by
  obtain ⟨μ, W₁, hμ, hB⟩ := fresh_basic hGA hb0 hb hκ
  obtain ⟨C, W₂, hC⟩ :=
    FullSource.fullSourceMoments_field_holds hGA b hb0 hb κ hκ ((2 : ℕ) * Q)
      (by push_cast; linarith)
  refine ⟨(1 + μ) * (1 + 2 * max C 0) ^ 2, max (max W₁ W₂) 1, by positivity,
    fun W hW E hE XX hXX σ u v => ?_⟩
  simp only [max_le_iff] at hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hNm : Measurable fun y => freshTransport b E XX y :=
    FullSource.measurable_freshTransport_comp b E measurable_const measurable_id
  have hN : eLpNorm (fun y => ‖freshTransport b E XX y‖) (ENNReal.ofReal ((2 : ℕ) * Q))
      (freshLaw W b) ≤ ENNReal.ofReal (max C 0) :=
    (hC W hW.1.2 E hE XX hXX).1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hG := eLpNorm_G_pow_le (ν := freshLaw W b) hNm.norm.aestronglyMeasurable
    (aestronglyMeasurable_const (b := (0 : ℝ))) (fun y => norm_nonneg _) (fun _ => le_rfl)
    (k := 2) (by norm_num) hQ (le_max_right C 0) hN (by simp)
  set c := vecNorm u * vecNorm v * (1 + μ)
  have hc : 0 ≤ c := by
    have := vecNorm_nonneg u; have := vecNorm_nonneg v; positivity
  have hM := (hB W hW.1.1 E hE XX hXX σ).2
  have hS := ae_sepOf_le hb0 hW.2 hη hXX
  have hmono : eLpNorm (fun ω => bilinear u (transportedSep b E XX σ ω -
      matrixExpect (freshLaw W b) (transportedSep b E XX σ)) v) (ENNReal.ofReal Q)
      (freshLaw W b) ≤ eLpNorm (c • fun y => (1 + ‖freshTransport b E XX y‖ + 0) ^ 2)
      (ENNReal.ofReal Q) (freshLaw W b) := by
    have hcont : Continuous fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
        bilinear u (M - matrixExpect (freshLaw W b) (transportedSep b E XX σ)) v := by
      unfold bilinear; fun_prop
    refine eLpNorm_mono_ae
      (hcont.measurable.comp (measurable_transportedSep b E XX σ)).aestronglyMeasurable ?_
    filter_upwards [hS] with y hy
    rw [Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
    exact crude_pointwise (norm_transportedSep_le (hy σ)) hM (norm_nonneg _) u v
  refine hmono.trans ?_
  rw [eLpNorm_const_smul c fun y => (1 + ‖freshTransport b E XX y‖ + 0) ^ 2,
    Real.enorm_eq_ofReal hc]
  calc ENNReal.ofReal c * eLpNorm (fun y => (1 + ‖freshTransport b E XX y‖ + 0) ^ 2)
        (ENNReal.ofReal Q) (freshLaw W b) ≤ ENNReal.ofReal c * ENNReal.ofReal
          ((1 + 2 * max C 0) ^ 2) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul hc]
        congr 1
        simp only [c]; ring

end BlockBand.SourceProcess.ContractingWords
