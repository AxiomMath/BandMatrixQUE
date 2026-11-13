module

public import BlockBand.SourceProcess.CompleteSourceGap.MeanCases
public import BlockBand.Transmission.SourceMixing.OneStepMean
public import BlockBand.Transmission.PassiveLayer.TMMain
public import BlockBand.SourceProcess.FullSourceCovariance.Assembly

/-!
# The mean clause of `CompleteSourceGapStatement` from the one-port gap-letter mean

Hypotheses: `GaussianAbsorptionContract`, `GaussianLpGradient` (through `passiveBounds_holds` and
`SourceMixing.oneStepMean_holds`) and the one-port node `GapLetterMean` (proved as
`gapLetterMean_holds`).

`mean_holds` proves the mean clause separator by separator:
* separator `P𝕊`: `mean_projS_le` and `GapLetterMean` (`q/W = g/(4ηW)`);
* separator `P𝕊P`: `mean_projSProj_le` and `SourceMixing.oneStepMean_holds` (the near-source
  gap); its factor `(1 + αq/W)⁻¹` is absorbed (`|θ_*/(1+t) - θ_*| ≤ |θ_*| t`, `‖f‖ ≤ 3/(2η)`);
* separators `𝕊*P`, `P𝕊*P`: adjoints.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ComplexConjugate

variable {W : ℕ}

/-- Integrable entries of the gap letter (passive moments at `p = 2`). -/
theorem integrable_gapLetter (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ x y, Integrable (fun ω => gapLetter b E X ω x y) (freshLaw W b) := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C, W₀, hM⟩ := moments_holds hGA b hb0 hb _ hκ 2 (by norm_num)
  refine ⟨max W₀ 1, fun W hW X hY x y => ?_⟩
  set z := boundaryZ b E
  obtain ⟨-, hG, -, hL⟩ := hM W (le_of_max_le_left hW) E (mem_bulkInterval_min E) z
    (BlockBand.Transmission.PassiveLayer.boundaryZ_mem_paramDisk (by linarith) hE1 hE2) X hY
  set C' := max C 0
  set k := ‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖
  have hGm : MomBd (freshLaw W b) (fun ω => ‖layerAt E z X ω‖) (2 * 1) C' :=
    ⟨(continuous_norm.measurable.comp (measurable_layerAt E z X)).aestronglyMeasurable,
      by rw [show (2 : ℝ) * 1 = 2 by norm_num]
         exact hG.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hLm : MomBd (freshLaw W b) (fun ω => ‖lAt E z X ω‖) (2 * 1) C' :=
    ⟨(continuous_norm.measurable.comp (measurable_lAt E z X)).aestronglyMeasurable,
      by rw [show (2 : ℝ) * 1 = 2 by norm_num]
         exact hL.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hP := MomBd.mul (p := 1) one_pos hLm (hGm.const_mul (c := k) (norm_nonneg _)) (le_max_right _ _)
  have hm : Measurable (gapLetter b E X) :=
    measurable_matrix_mul' (measurable_matrix_mul' (measurable_lAt E z X) (measurable_g21 E z X))
      measurable_const
  refine integrable_entries_of_momBd hm (by positivity) (hP.mono hm.norm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)) x y
  rw [norm_norm]
  calc ‖gapLetter b E X ω‖ ≤ ‖lAt E z X ω‖ * ‖g21 E z X ω‖ * k :=
        (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
          (norm_nonneg _))
    _ ≤ ‖lAt E z X ω‖ * (k * ‖layerAt E z X ω‖) := by
        rw [mul_assoc, mul_comm (‖g21 E z X ω‖)]
        gcongr
        exact norm_g21_le E z X ω

theorem div_one_add_sub_le (θ : ℂ) {t : ℝ} (ht : 0 ≤ t) : ‖θ / (1 + (t : ℂ)) - θ‖ ≤ ‖θ‖ * t := by
  have h1 : (1 + (t : ℂ)) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have e : θ / (1 + (t : ℂ)) - θ = -(θ * t) / (1 + (t : ℂ)) := by field_simp; ring
  rw [e, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
  have h2 : ‖(1 + (t : ℂ))‖ = 1 + t := by
    rw [show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [h2, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg (norm_nonneg θ) ht) ht]

/-- **`CompleteSourceGapStatement.mean`**, from the input hypotheses and the open `GapLetterMean`. -/
theorem mean_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hM : GapLetterMean) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    (∃ s : ℂ, IsStationaryJet b E s) ∧ ∀ s : ℂ, IsStationaryJet b E s →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        ∀ σ : Separator, σ.unconj + σ.conj = 1 →
          let X := nearSchur (boundaryZ b E) XX
          ‖matrixExpect (freshLaw W b) (transportedSep b E XX σ) -
              gapFactor b E s σ • sepOf b E XX σ‖ ≤
            C * (jetDistance0 b E X + jetDistance1 b E s X +
              conductanceOf (passiveTransmission b E X) / W + ((W : ℝ)⁻¹) ^ 2) := by
  intro b hb0 hb E hE1 hE2
  obtain ⟨hex, hM'⟩ := hM b hb0 hb E hE1 hE2
  obtain ⟨-, hO⟩ := BlockBand.Transmission.SourceMixing.oneStepMean_holds (passiveBounds_holds hGA hLp) b hb0 hb E hE1 hE2
  obtain ⟨W₃, hI⟩ := integrable_gapLetter hGA hb0 hb hE1 hE2
  refine ⟨hex, fun s hs => ?_⟩
  obtain ⟨C₁, W₁, h1⟩ := hM' s hs
  obtain ⟨C₂, W₂, h2⟩ := hO s hs
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
  refine ⟨K₁ + K₂, max (max W₁ W₂) (max W₃ 1), fun W hW XX hXX σ hσ => ?_⟩
  intro X
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
      (hI W (le_of_max_le_left (le_of_max_le_right hW)) X hY) θ).trans ?_
    refine (h1 W (le_of_max_le_left (le_of_max_le_left hW)) X hY).trans ?_
    calc C₁ * _ ≤ max C₁ 0 * (jetDistance0 b E X + jetDistance1 b E s X + q / W +
          ((W : ℝ)⁻¹) ^ 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) hbase0
      _ ≤ max C₁ 0 * (a * err) := mul_le_mul_of_nonneg_left hbase (le_max_right _ _)
      _ ≤ (K₁ + K₂) * err := by simp only [K₁]; nlinarith
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
    have hmain := h2 W (le_of_max_le_right (le_of_max_le_left hW)) X hY
    calc 2 * η * ‖F - θ • f‖ ≤ 2 * η * (‖F - θ' • f‖ + ‖θ' - θ‖ * ‖f‖) := by gcongr
      _ ≤ 2 * η * (max C₂ 0 * (a * err) + ‖θ‖ * (α * (4 * η)⁻¹ * err) * (3 / (2 * η))) := by
          gcongr
          · exact hmain.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hbase0).trans
              (mul_le_mul_of_nonneg_left hbase (le_max_right _ _)))
          · exact hθ.trans (mul_le_mul_of_nonneg_left hαq (norm_nonneg _))
      _ = K₂ * err := by simp only [K₂]; ring
      _ ≤ (K₁ + K₂) * err := by nlinarith
  have hfac : ∀ σ' : Separator, σ'.unconj = 1 → σ'.conj = 0 → gapFactor b E s σ' = θ := by
    intro σ' h1' h2'; simp [gapFactor, h1', h2', θ]
  have hfac' : ∀ σ' : Separator, σ'.unconj = 0 → σ'.conj = 1 → gapFactor b E s σ' = star θ := by
    intro σ' h1' h2'; simp [gapFactor, h1', h2', θ]
  cases σ <;> simp [Separator.unconj, Separator.conj] at hσ
  · rw [hfac _ rfl rfl]; exact caseS
  · rw [hfac' _ rfl rfl, show transportedSep b E XX .sStarProj =
      fun ω => (transportedSep b E XX .projS ω)ᴴ from funext (transportedSep_sStarProj b E XX),
      matrixExpect_conjTranspose, sepOf_sStarProj, norm_conj_err]
    exact caseS
  · rw [hfac _ rfl rfl]; exact caseSP
  · rw [hfac' _ rfl rfl, show transportedSep b E XX .projSStarProj =
      fun ω => (transportedSep b E XX .projSProj ω)ᴴ from
        funext (transportedSep_projSStarProj b E XX),
      matrixExpect_conjTranspose, sepOf_projSStarProj, norm_conj_err]
    exact caseSP

end BlockBand.SourceProcess.CompleteSourceGap
