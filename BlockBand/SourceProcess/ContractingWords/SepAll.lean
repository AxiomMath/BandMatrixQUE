module

public import BlockBand.SourceProcess.ContractingWords.StepSep
public import BlockBand.SourceProcess.ContractingWords.LayerStep
public import BlockBand.SourceProcess.ContractingWords.LayerMeas
public import BlockBand.SourceProcess.ContractingWords.LayerFresh
public import BlockBand.SourceProcess.FullSource.MomentsHolds
public import BlockBand.Transmission.PassiveLayer.PoissonLayer
public import BlockBand.Transmission.PassiveCovarianceBulk.Scalars

/-!
# All six transported separators at one fresh layer

Two bulk-uniform statements for **every** separator `σ` (contracting, `I`, `P`), at a Hermitian
old two-port `𝕏` and `T_σ = N·sepOf(𝕏₊)σ·N*`:
* `SepMeanAll`: `‖ET_σ - gapFactor(σ)·sepOf(𝕏)σ‖ ≤ C(δ₀ + δ₁ + g/W + W⁻²)`;
* `SepFluctAll`: `‖u*(T_σ - ET_σ)v‖_Q ≤ C(W^{-1/2} + min(1,δ₀))‖u‖‖v‖`.
For contracting `σ` they are `SeparatorMeanUniform`/`SeparatorFluctUniform`; for `I`
(`NN* = I + 𝓔`) and `P` (`NPN* = ι LL* ι*`) they are `SepMeanIdProj`/`SepFluctIdProj`, proved
through `FullSourceEstimates` and the bulk passive bounds.
`min(1,δ₀)` pays the scalar domain of `FullSourceEstimates.fluct`.

Also here: `fresh_basic` (`‖sepOf 𝕏₊ σ‖ ≤ 1` a.s., `‖T_σ‖ ≤ ‖N‖²`, integrable entries,
`‖ET_σ‖ ≤ C`) from the bulk moments of `N` (`fullSourceMoments_field_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource
open scoped ENNReal Matrix.Norms.L2Operator

/-- **Means of all six transported separators** (bulk-uniform). -/
def SepMeanAll : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s →
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian → ∀ σ : Separator,
        let X := nearSchur (boundaryZ b E) XX
        ‖matrixExpect (freshLaw W b) (transportedSep b E XX σ) -
            gapFactor b E s σ • sepOf b E XX σ‖ ≤
          C * (jetDistance0 b E X + jetDistance1 b E s X +
            conductanceOf (passiveTransmission b E X) / W + ((W : ℝ)⁻¹) ^ 2)

/-- **Centered bilinear bounds of all six transported separators** (bulk-uniform). -/
def SepFluctAll : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ Q : ℝ, 1 ≤ Q →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian → ∀ σ : Separator,
      ∀ u v : Fin 2 × Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (transportedSep b E XX σ ω -
            matrixExpect (freshLaw W b) (transportedSep b E XX σ)) v) (ENNReal.ofReal Q)
            (freshLaw W b) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W +
            min 1 (jetDistance0 b E (nearSchur (boundaryZ b E) XX))) * vecNorm u * vecNorm v)

variable {W : ℕ}

theorem ae_sepOf_le {b E : ℝ} (hb0 : 0 < b) (hW : 1 ≤ W) (hη : 0 < etaZ b E)
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : XX.IsHermitian) :
    ∀ᵐ y ∂freshLaw W b, ∀ σ, ‖sepOf b E (freshTwoPortSchur E XX y) σ‖ ≤ 1 := by
  filter_upwards [BlockBand.Transmission.PassiveLayer.ae_good W hb0 hW] with y hy σ
  exact norm_sepOf_le b E (freshTwoPortSchur_isHermitian E hXX hy.1) hη σ

theorem norm_transportedSep_le {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {σ : Separator} {y : LayerSample W .oneBlockOnePort}
    (hS : ‖sepOf b E (freshTwoPortSchur E XX y) σ‖ ≤ 1) :
    ‖transportedSep b E XX σ y‖ ≤ ‖freshTransport b E XX y‖ ^ 2 := by
  have h1 := norm_mul_le (freshTransport b E XX y * sepOf b E (freshTwoPortSchur E XX y) σ)
    (freshTransport b E XX y)ᴴ
  have h2 := norm_mul_le (freshTransport b E XX y) (sepOf b E (freshTwoPortSchur E XX y) σ)
  rw [Matrix.l2_opNorm_conjTranspose] at h1
  have hN := norm_nonneg (freshTransport b E XX y)
  calc ‖transportedSep b E XX σ y‖ ≤ ‖freshTransport b E XX y‖ * 1 * ‖freshTransport b E XX y‖ :=
        h1.trans (mul_le_mul_of_nonneg_right (h2.trans (by gcongr)) hN)
    _ = _ := by ring

/-- **Integrability and the size of the means**, bulk-uniform. -/
theorem fresh_basic (hGA : GaussianAbsorptionContract) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (μ : ℝ) (W₀ : ℕ), 0 ≤ μ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian → ∀ σ : Separator,
        (∀ i j, Integrable (fun y => transportedSep b E XX σ y i j) (freshLaw W b)) ∧
        ‖matrixExpect (freshLaw W b) (transportedSep b E XX σ)‖ ≤ μ := by
  obtain ⟨C, W₀, hC⟩ := fullSourceMoments_field_holds hGA b hb0 hb κ hκ 2 (by norm_num)
  refine ⟨max C 0 ^ 2, max W₀ 1, by positivity, fun W hW E hE XX hXX σ => ?_⟩
  simp only [max_le_iff] at hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hN2 := (hC W hW.1 E hE XX hXX).1
  have hNm : Measurable fun y => freshTransport b E XX y :=
    measurable_freshTransport_comp b E measurable_const measurable_id
  have hmb : BlockBand.Transmission.PassiveLayer.MomBd (freshLaw W b) (fun y => ‖freshTransport b E XX y‖) (2 : ℕ) (max C 0) :=
    ⟨hNm.norm.aestronglyMeasurable, by
      simpa using hN2.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))⟩
  obtain ⟨hsq0, hsqI⟩ := integral_abs_pow_le (ν := freshLaw W b) (n := 2) (by norm_num)
    (le_max_right C 0) hmb
  simp only [abs_norm] at hsq0 hsqI
  have hsq : Integrable (fun y => ‖freshTransport b E XX y‖ ^ 2) (freshLaw W b) := hsq0
  have hTm := measurable_transportedSep b E XX σ
  have hS := ae_sepOf_le hb0 hW.2 hη hXX
  have hTn : Integrable (fun y => ‖transportedSep b E XX σ y‖) (freshLaw W b) :=
    hsq.mono' hTm.norm.aestronglyMeasurable (by
      filter_upwards [hS] with y hy
      rw [norm_norm]; exact norm_transportedSep_le (hy σ))
  have hent : ∀ i j, Integrable (fun y => transportedSep b E XX σ y i j) (freshLaw W b) :=
    fun i j => hTn.mono' hTm.eval_matrix.aestronglyMeasurable
      (Eventually.of_forall fun y => norm_entry_le_op _ i j)
  refine ⟨hent, (norm_matrixExpect_le _ hent hTn).trans ((integral_mono_ae hTn hsq ?_).trans hsqI)⟩
  filter_upwards [hS] with y hy
  exact norm_transportedSep_le (hy σ)

end BlockBand.SourceProcess.ContractingWords
