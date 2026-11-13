module

public import BlockBand.SourceProcess.CompleteSourceGapBulk.GapMeanBulk
public import BlockBand.Transmission.SourceMixingBulk.OneStepMean
public import BlockBand.SourceProcess.ContractingWords.StepSep

/-!
# `SeparatorMeanUniform` is proved

Hypotheses: `GaussianAbsorptionContract`, `GaussianLpGradient` (through `passiveBounds_holds`).

Bulk-uniform copy of `mean_holds`:
* separator `P𝕊`: `mean_projS_le` (pointwise) and `gapLetterMean_bulk` (`q/W = g/(4ηW)`);
* separator `P𝕊P`: `mean_projSProj_le` (pointwise) and `SourceMixingBulk.oneStepMean_bulk`; the factor
  `(1 + αq/W)⁻¹` is absorbed as in `mean_holds`;
* separators `𝕊*P`, `P𝕊*P`: adjoints.
The constants of `mean_holds`, `K₁ = C₁⁺a`, `K₂ = 2η(C₂⁺a + ‖θ_*‖α(4η)⁻¹·3/(2η))` (`a = 1 + (4η)⁻¹`) are
bounded by `KL = C₁⁺a_L + 6C₂⁺a_L + α_L(4η_L)⁻¹·3`, using `η_L = etaLow b κ ≤ η ≤ 3`,
`a_L = 1 + (4η_L)⁻¹`, `α ≤ α_L = (1-b)²/(bη_L)` (`alphaCoef_le_bulk`) and `‖θ_*‖ ≤ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGapBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ComplexConjugate

variable {W : ℕ}

/-- The constants of `mean_holds` are majorized uniformly on `bulkInterval κ`. -/
theorem mean_consts_le_bulk {b κ E C₁ C₂ : ℝ} {θ : ℂ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) (hθ1 : ‖θ‖ ≤ 1) :
    max C₁ 0 * (1 + (4 * etaZ b E)⁻¹) + 2 * etaZ b E * (max C₂ 0 * (1 + (4 * etaZ b E)⁻¹) +
        ‖θ‖ * alphaCoef b E * (4 * etaZ b E)⁻¹ * (3 / (2 * etaZ b E))) ≤
      max C₁ 0 * (1 + (4 * PathScalar.etaLow b κ)⁻¹) +
        (6 * (max C₂ 0 * (1 + (4 * PathScalar.etaLow b κ)⁻¹)) +
          (1 - b) ^ 2 / (b * PathScalar.etaLow b κ) * (4 * PathScalar.etaLow b κ)⁻¹ * 3) := by
  obtain ⟨hE1, hE2, hηL, hηle, hη3, -, -⟩ := bulk_scalars hb0 hb hκ hE
  have hη := BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  set η := etaZ b E
  set ηL := PathScalar.etaLow b κ
  set α := alphaCoef b E
  set αL := (1 - b) ^ 2 / (b * ηL)
  set a := 1 + (4 * η)⁻¹
  set aL := 1 + (4 * ηL)⁻¹
  have hα : 0 ≤ α := div_nonneg (sq_nonneg _) (mul_nonneg hb0.le hη.le)
  have ha : 1 ≤ a := by have : 0 ≤ (4 * η)⁻¹ := by positivity
                        linarith
  have hinv : (4 * η)⁻¹ ≤ (4 * ηL)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have haL : a ≤ aL := by simp only [a, aL]; linarith
  have hαL : α ≤ αL := SourceMixingBulk.alphaCoef_le_bulk hb0 hb hκ hE
  have e2 : 2 * η * (max C₂ 0 * a + ‖θ‖ * α * (4 * η)⁻¹ * (3 / (2 * η))) =
      2 * η * (max C₂ 0 * a) + ‖θ‖ * α * (4 * η)⁻¹ * 3 := by
    field_simp
  have hm1 : max C₁ 0 * a ≤ max C₁ 0 * aL := mul_le_mul_of_nonneg_left haL (le_max_right _ _)
  have hm2 : max C₂ 0 * a ≤ max C₂ 0 * aL := mul_le_mul_of_nonneg_left haL (le_max_right _ _)
  have hm2' : 2 * η * (max C₂ 0 * a) ≤ 6 * (max C₂ 0 * aL) :=
    mul_le_mul (by linarith) hm2 (by positivity) (by norm_num)
  have h1' : ‖θ‖ * α ≤ αL := by
    calc ‖θ‖ * α ≤ 1 * α := mul_le_mul_of_nonneg_right hθ1 hα
      _ ≤ αL := by rw [one_mul]; exact hαL
  have h2' : ‖θ‖ * α * (4 * η)⁻¹ ≤ αL * (4 * ηL)⁻¹ :=
    mul_le_mul h1' hinv (by positivity) (hα.trans hαL)
  rw [e2]
  linarith

/-- **`ContractingWords.SeparatorMeanUniform`**:
`CompleteSourceGapStatement.mean` with constants
uniform on `bulkInterval κ` (bulk-uniform copy of `mean_holds`), from
`GaussianAbsorptionContract` and `GaussianLpGradient`.
-/
theorem separatorMeanUniform_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) : ContractingWords.SeparatorMeanUniform := by
  intro b hb0 hb κ hκ
  obtain ⟨C₁, W₁, -, h1⟩ := gapLetterMean_bulk (passiveBounds_holds hGA hLp) hb0 hb hκ
  obtain ⟨C₂, W₂, -, h2⟩ :=
    SourceMixingBulk.oneStepMean_bulk (passiveBounds_holds hGA hLp) hb0 hb hκ
  obtain ⟨W₃, hI⟩ := integrable_gapLetter_bulk hGA hb0 hb hκ
  set ηL := PathScalar.etaLow b κ
  set aL := 1 + (4 * ηL)⁻¹
  set αL := (1 - b) ^ 2 / (b * ηL)
  set KL := max C₁ 0 * aL + (6 * (max C₂ 0 * aL) + αL * (4 * ηL)⁻¹ * 3)
  refine ⟨KL, max (max W₁ W₂) (max W₃ 1), fun W hW E hE s hs XX hXX σ hσ => ?_⟩
  intro X
  obtain ⟨hE1, hE2, hηL, hηle, hη3, -, -⟩ := bulk_scalars hb0 hb hκ hE
  have hη := BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  set η := etaZ b E
  set θ := thetaStar b E s
  set α := alphaCoef b E
  have hα : 0 ≤ α := div_nonneg (sq_nonneg _) (mul_nonneg hb0.le hη.le)
  set a := 1 + (4 * η)⁻¹
  have ha : 1 ≤ a := by have : 0 ≤ (4 * η)⁻¹ := by positivity
                        linarith
  set K₁ := max C₁ 0 * a
  set K₂ := 2 * η * (max C₂ 0 * a + ‖θ‖ * α * (4 * η)⁻¹ * (3 / (2 * η)))
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  have hθ1 : ‖θ‖ ≤ 1 := (SourceMixing.norm_thetaStar_le hb0 hb hE1 hE2 hs).1
  have hKL : K₁ + K₂ ≤ KL := mean_consts_le_bulk hb0 hb hκ hE hθ1
  have hW1 : 1 ≤ W := le_of_max_le_right (le_of_max_le_right hW)
  have hY : (passiveY X).PosSemidef := nearSchur_passive hη hXX
  set q := passiveMass b E X
  set g := conductanceOf (passiveTransmission b E X)
  have hq0 : 0 ≤ q := BlockBand.Transmission.PassiveCovariance.passiveMass_nonneg b E hY
  have hg : g = 4 * η * q := by
    simp [g, q, η, conductanceOf, passiveTransmission, passiveMass, Matrix.trace_smul]
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hqW : q / W = (4 * η)⁻¹ * (g / W) := by rw [hg]; field_simp
  set err := jetDistance0 b E X + jetDistance1 b E s X + g / W + ((W : ℝ)⁻¹) ^ 2
  have hd0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hd1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  have hgW : 0 ≤ g / W := by rw [hg]; positivity
  have herr : 0 ≤ err := by positivity
  have hbase : jetDistance0 b E X + jetDistance1 b E s X + q / W + ((W : ℝ)⁻¹) ^ 2 ≤ a * err := by
    rw [hqW]
    have : (4 * η)⁻¹ * (g / W) ≤ a * (g / W) := by
      apply mul_le_mul_of_nonneg_right _ hgW; simp only [a]; linarith
    nlinarith [sq_nonneg ((W : ℝ)⁻¹)]
  have hbase0 : 0 ≤ jetDistance0 b E X + jetDistance1 b E s X + q / W + ((W : ℝ)⁻¹) ^ 2 := by
    positivity
  -- the two basic cases
  have caseS : ‖matrixExpect (freshLaw W b) (transportedSep b E XX .projS) -
      θ • sepOf b E XX .projS‖ ≤ (K₁ + K₂) * err := by
    refine (mean_projS_le hb0 hb hE1 hE2 hW1 hXX
      (hI W (le_of_max_le_left (le_of_max_le_right hW)) E hE X hY) θ).trans ?_
    refine (h1 W (le_of_max_le_left (le_of_max_le_left hW)) E hE s hs X hY).trans ?_
    calc C₁ * _ ≤ max C₁ 0 * (jetDistance0 b E X + jetDistance1 b E s X + q / W +
          ((W : ℝ)⁻¹) ^ 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) hbase0
      _ ≤ max C₁ 0 * (a * err) := mul_le_mul_of_nonneg_left hbase (le_max_right _ _)
      _ = K₁ * err := by simp only [K₁]; ring
      _ ≤ (K₁ + K₂) * err := by rw [add_mul]; linarith [mul_nonneg hK₂ herr]
  have caseSP : ‖matrixExpect (freshLaw W b) (transportedSep b E XX .projSProj) -
      θ • sepOf b E XX .projSProj‖ ≤ (K₁ + K₂) * err := by
    refine (mean_projSProj_le hb0 hb hE1 hE2 hW1 hXX θ).trans ?_
    set F := matrixExpect (freshLaw W b) (freshTransportedF b E X)
    set f := passiveF b E X
    set θ' := θ / (1 + alphaCoef b E * passiveMass b E X / W)
    have hf : ‖f‖ ≤ 3 / (2 * η) :=
      BlockBand.Transmission.PassiveCovariance.norm_passiveF_le hb0 hb hE1 hE2 hY
    have hθ : ‖θ' - θ‖ ≤ ‖θ‖ * (α * q / W) := by
      have := div_one_add_sub_le θ (t := α * q / W) (by positivity)
      convert this using 3; push_cast; ring
    have hsplit : ‖F - θ • f‖ ≤ ‖F - θ' • f‖ + ‖θ' - θ‖ * ‖f‖ := by
      rw [show F - θ • f = (F - θ' • f) + (θ' - θ) • f by rw [sub_smul]; abel]
      refine (norm_add_le _ _).trans ?_
      gcongr
      exact norm_smul_le _ _
    have hgE : g / W ≤ err := by
      simp only [err]; nlinarith [sq_nonneg ((W : ℝ)⁻¹)]
    have hαq : α * q / W ≤ α * (4 * η)⁻¹ * err := by
      rw [mul_div_assoc, hqW, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hgE (by positivity)
    have hmain := h2 W (le_of_max_le_right (le_of_max_le_left hW)) E hE s hs X hY
    calc 2 * η * ‖F - θ • f‖ ≤ 2 * η * (‖F - θ' • f‖ + ‖θ' - θ‖ * ‖f‖) := by gcongr
      _ ≤ 2 * η * (max C₂ 0 * (a * err) + ‖θ‖ * (α * (4 * η)⁻¹ * err) * (3 / (2 * η))) := by
          gcongr
          · exact hmain.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hbase0).trans
              (mul_le_mul_of_nonneg_left hbase (le_max_right _ _)))
          · exact hθ.trans (mul_le_mul_of_nonneg_left hαq (norm_nonneg _))
      _ = K₂ * err := by simp only [K₂]; ring
      _ ≤ (K₁ + K₂) * err := by rw [add_mul]; linarith [mul_nonneg hK₁ herr]
  have hfin : (K₁ + K₂) * err ≤ KL * err := mul_le_mul_of_nonneg_right hKL herr
  have hfac : ∀ σ' : Separator, σ'.unconj = 1 → σ'.conj = 0 → gapFactor b E s σ' = θ := by
    intro σ' h1' h2'; simp [gapFactor, h1', h2', θ]
  have hfac' : ∀ σ' : Separator, σ'.unconj = 0 → σ'.conj = 1 → gapFactor b E s σ' = star θ := by
    intro σ' h1' h2'; simp [gapFactor, h1', h2', θ]
  cases σ <;> simp [Separator.unconj, Separator.conj] at hσ
  · rw [hfac _ rfl rfl]; exact caseS.trans hfin
  · rw [hfac' _ rfl rfl, show transportedSep b E XX .sStarProj =
      fun ω => (transportedSep b E XX .projS ω)ᴴ from funext (transportedSep_sStarProj b E XX),
      matrixExpect_conjTranspose, sepOf_sStarProj, norm_conj_err]
    exact caseS.trans hfin
  · rw [hfac _ rfl rfl]; exact caseSP.trans hfin
  · rw [hfac' _ rfl rfl, show transportedSep b E XX .projSStarProj =
      fun ω => (transportedSep b E XX .projSProj ω)ᴴ from
        funext (transportedSep_projSStarProj b E XX),
      matrixExpect_conjTranspose, sepOf_projSStarProj, norm_conj_err]
    exact caseSP.trans hfin

end BlockBand.SourceProcess.CompleteSourceGapBulk
