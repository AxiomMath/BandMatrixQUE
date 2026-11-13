module

public import BlockBand.SourceProcess.ContractingWords.IdProjAlg
public import BlockBand.Transmission.Generator.MeanPassive
public import BlockBand.Transmission.PassiveLayer.TMMain
public import BlockBand.SourceProcess.FullSource.DeltaHolds
public import BlockBand.Transmission.SourceMixingBulk.OneStepStrict

/-!
# `SepMeanIdProj`: the means of `NN*` and `NPN*`, bulk-uniform

**`sepMeanIdProj_holds hGA hLp : SepMeanIdProj`.** Measure `freshLaw W b` (one fresh layer),
deterministic Hermitian old two-port `𝕏`, operator norm, constants depending on `b, κ` only.
* `σ = I`: `‖E[NN*] - I‖ = ‖E𝓔‖ ≤ C(δ₀ + W⁻²)` (`FullSourceEstimates.mean`,
  `fullSourceEstimates_holds`), integrability from `fresh_basic`;
* `σ = P`: `‖E[NPN*] - P‖ ≤ ‖EU - I‖` (`norm_mean_proj_le`), and `ubarMean_bulk`
  (`‖EU - cI‖ ≤ C(δ₀ + W⁻² + q/W)`, `c = (1 + αq/W)⁻¹`), `0 ≤ 1 - c ≤ αq/W`,
  `q = g/(4η) ≤ η_L⁻¹g`, `α ≤ (1-b)²/(bη_L)` on `bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.Bridge
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem one_sub_inv_le {t : ℝ} (ht : 0 ≤ t) : |(1 + t)⁻¹ - 1| ≤ t := by
  have h1 : 0 < 1 + t := by linarith
  have e : (1 + t)⁻¹ - 1 = -(t / (1 + t)) := by field_simp; ring
  rw [e, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ h1]
  nlinarith

/-- `q/W ≤ η_L⁻¹·g/W` on the bulk. -/
theorem mass_le_conductance {b κ E : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    passiveMass b E X / W ≤
        (BlockBand.Transmission.PathScalar.etaLow b κ)⁻¹ *
        (conductanceOf (passiveTransmission b E X) / W) := by
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hi := BlockBand.Transmission.CovarianceBulk.inv_etaZ_le_bulk hb hκ hE
  have hq := BlockBand.Transmission.PassiveCovariance.passiveMass_nonneg b E hY
  have hgq : conductanceOf (passiveTransmission b E X) = 4 * etaZ b E * passiveMass b E X := by
    simp [conductanceOf, passiveTransmission, passiveMass, Matrix.trace_smul]
  rw [hgq, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg W)
  have e : passiveMass b E X = (etaZ b E)⁻¹ * (etaZ b E * passiveMass b E X) := by field_simp
  calc passiveMass b E X = (etaZ b E)⁻¹ * (etaZ b E * passiveMass b E X) := e
    _ ≤ (BlockBand.Transmission.PathScalar.etaLow b κ)⁻¹ * (etaZ b E * passiveMass b E X) := by
        gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hη.le hq])
        (inv_pos.mpr (BlockBand.Transmission.PathScalar.etaLow_pos (by linarith) hκ)).le

theorem arith_proj {CU A K δ w q g : ℝ} (hCU : 0 ≤ CU) (hA : 0 ≤ A) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hw : 0 ≤ w) (hg : 0 ≤ g) (hqg : q ≤ K * g) {x : ℝ} (hx : x ≤ A * q) :
    CU * (δ + w + q) + x ≤ (CU + (CU + A) * K) * (δ + g + w) := by
  have h1 : (CU + A) * q ≤ (CU + A) * (K * g) := mul_le_mul_of_nonneg_left hqg (by positivity)
  have h2 : 0 ≤ (CU + A) * K * (δ + w) := by positivity
  nlinarith

/-- The `P` case of `SepMeanIdProj`. -/
theorem mean_proj_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        let X := nearSchur (boundaryZ b E) XX
        ‖matrixExpect (freshLaw W b) (transportedSep b E XX .proj) - sepOf b E XX .proj‖ ≤
          C * (jetDistance0 b E X + conductanceOf (passiveTransmission b E X) / W +
            ((W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨CU, W₀, hCU, hU⟩ :=
    Transmission.Generator.ubarMean_bulk
      (BlockBand.Transmission.PassiveLayer.passiveBounds_holds hGA hLp) hb0 hb hκ
  have hηL := BlockBand.Transmission.PathScalar.etaLow_pos (b := b) (by linarith) hκ
  set A := (1 - b) ^ 2 / (b * BlockBand.Transmission.PathScalar.etaLow b κ)
  set K := (BlockBand.Transmission.PathScalar.etaLow b κ)⁻¹
  have hA : 0 ≤ A := by positivity
  have hK : 0 ≤ K := by positivity
  refine ⟨CU + (CU + A) * K, W₀, by positivity, fun W hW E hE XX hXX => ?_⟩
  intro X
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hY : (passiveY X).PosSemidef := FullSource.nearSchur_passive hη hXX
  have hq := BlockBand.Transmission.PassiveCovariance.passiveMass_nonneg b E hY
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le hY
  have hα0 : 0 ≤ alphaCoef b E := by rw [alphaCoef]; have := mul_pos hb0 hη; positivity
  have hαA : alphaCoef b E ≤ A :=
    BlockBand.Transmission.SourceMixingBulk.alphaCoef_le_bulk hb0 hb hκ hE
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hqW : 0 ≤ passiveMass b E X / W := by positivity
  have hc : ‖((Transmission.Generator.meanC b E X : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) -
      1‖ ≤ A * (passiveMass b E X / W) := by
    have e : ((Transmission.Generator.meanC b E X : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) -
        1 = (((Transmission.Generator.meanC b E X - 1 : ℝ)) : ℂ) • 1 := by
      rw [Complex.ofReal_sub, sub_smul, Complex.ofReal_one, one_smul]
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Transmission.Generator.meanC b E X - 1| ≤ alphaCoef b E * passiveMass b E X / W := by
      unfold Transmission.Generator.meanC
      rw [mul_div_assoc]; exact one_sub_inv_le (by positivity)
    calc |Transmission.Generator.meanC b E X - 1| * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤
        (alphaCoef b E * passiveMass b E X / W) * 1 :=
          mul_le_mul h1 BlockBand.Transmission.PassiveCovariance.norm_one_matrix_le
            (norm_nonneg _) (by positivity)
      _ ≤ A * (passiveMass b E X / W) := by
          rw [mul_one, mul_div_assoc]; exact mul_le_mul_of_nonneg_right hαA hqW
  refine (norm_mean_proj_le b E XX).trans ?_
  refine (norm_sub_le_norm_sub_add_norm_sub _
    (((Transmission.Generator.meanC b E X : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) _).trans ?_
  refine (add_le_add (hU W hW E hE X hY).1 hc).trans ?_
  exact arith_proj hCU hA hK (norm_nonneg _) (by positivity) (by positivity)
    (mass_le_conductance hb hκ hE hY) le_rfl

/-- The `I` case of `SepMeanIdProj`. -/
theorem mean_id_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        let X := nearSchur (boundaryZ b E) XX
        ‖matrixExpect (freshLaw W b) (transportedSep b E XX .id) - sepOf b E XX .id‖ ≤
          C * (jetDistance0 b E X + conductanceOf (passiveTransmission b E X) / W +
            ((W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨C, W₁, hC⟩ := (FullSource.fullSourceEstimates_holds hGA hLp).mean b hb0 hb κ hκ
  obtain ⟨μ, W₂, -, hB⟩ := fresh_basic hGA hb0 hb hκ
  refine ⟨max C 0, max W₁ W₂, le_max_right _ _, fun W hW E hE XX hXX => ?_⟩
  intro X
  simp only [max_le_iff] at hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  have hδ : 0 ≤ jetDistance0 b E X := norm_nonneg _
  rw [sepOf, matrixExpect_sub_one (hB W hW.2 E hE XX hXX .id).1]
  refine (hC W hW.1 E hE XX hXX).trans ?_
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have : 0 ≤ conductanceOf (passiveTransmission b E X) / W := by positivity
  calc C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) ≤
      max C 0 * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by gcongr; exact le_max_left _ _
    _ ≤ _ := by gcongr; linarith

/-- **`SepMeanIdProj`** from the Gaussian inputs. -/
theorem sepMeanIdProj_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    SepMeanIdProj := by
  intro b hb0 hb κ hκ
  obtain ⟨C₁, W₁, hC₁, h₁⟩ := mean_id_bulk hGA hLp hb0 hb hκ
  obtain ⟨C₂, W₂, hC₂, h₂⟩ := mean_proj_bulk hGA hLp hb0 hb hκ
  refine ⟨C₁ + C₂, max W₁ W₂, by positivity, fun W hW E hE XX hXX σ hσ => ?_⟩
  intro X
  simp only [max_le_iff] at hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hR : 0 ≤ jetDistance0 b E X + conductanceOf (passiveTransmission b E X) / W +
      ((W : ℝ)⁻¹) ^ 2 := by
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    positivity
  cases σ <;> simp [Separator.unconj, Separator.conj] at hσ
  · exact (h₁ W hW.1 E hE XX hXX).trans (by gcongr; linarith)
  · exact (h₂ W hW.2 E hE XX hXX).trans (by gcongr; linarith)

end BlockBand.SourceProcess.ContractingWords
