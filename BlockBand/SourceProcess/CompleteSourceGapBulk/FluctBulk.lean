module

public import BlockBand.SourceProcess.CompleteSourceGapBulk.GapFlucBulk
public import BlockBand.Transmission.LengthUniform.BulkMassLayer
public import BlockBand.SourceProcess.ContractingWords.StepSep

/-!
# `SeparatorFluctUniform` is proved

Hypotheses: `GaussianAbsorptionContract`, `GaussianLpGradient`.

Bulk-uniform copy of `fluctuation_holds`:
* separators `P𝕊`, `𝕊*P`: `x*(U - EU)y = (ι*x)*(Γ - EΓ)(ι*𝕊y)` (a.s., pointwise) and `gapLetterFluctuation_bulk`;
* separators `P𝕊P`, `P𝕊*P`: `x*(U - EU)y = -2iη (ι*x)*(F - EF)(ι*y)` and
  `LengthUniform.oneStepFluctuation_bulk` (second clause).
The constant `K = C₁⁺ + 2ηC₂⁺` of `fluctuation_holds` is replaced by `C₁⁺ + 6C₂⁺` (`η ≤ 3`,
`bulk_scalars`).
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
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- **`ContractingWords.SeparatorFluctUniform`**:
`CompleteSourceGapStatement.fluctuation` with
constants uniform on `bulkInterval κ` (bulk-uniform copy of `fluctuation_holds`), from
`GaussianAbsorptionContract` and `GaussianLpGradient`.
-/
theorem separatorFluctUniform_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) : ContractingWords.SeparatorFluctUniform := by
  intro b hb0 hb κ hκ p hp
  obtain ⟨C₁, W₁, h1⟩ := gapLetterFluctuation_bulk hGA hLp hb0 hb hκ p hp
  obtain ⟨C₂, W₂, h2⟩ :=
    LengthUniform.oneStepFluctuation_bulk (passiveBounds_holds hGA hLp) hb0 hb hκ p hp
  obtain ⟨W₃, hI⟩ := integrable_gapLetter_bulk hGA hb0 hb hκ
  set K := max C₁ 0 + 2 * 3 * max C₂ 0
  have hK1 : max C₁ 0 ≤ K := by
    simp only [K]; have := le_max_right C₂ 0; linarith
  refine ⟨K, max (max W₁ W₂) (max W₃ 1), fun W hW E hE XX hXX σ hσ => ?_⟩
  obtain ⟨hE1, hE2, -, -, hη3, -, -⟩ := bulk_scalars hb0 hb hκ hE
  have hη := BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  set c : ℂ := (2 * Complex.I) * (etaZ b E : ℂ)
  have hc : ‖-c‖ = 2 * etaZ b E := by simp [c, Complex.norm_real, abs_of_pos hη]
  have hK2 : 2 * etaZ b E * max C₂ 0 ≤ K := by
    have := mul_le_mul_of_nonneg_right (by linarith : 2 * etaZ b E ≤ 2 * 3) (le_max_right C₂ 0)
    simp only [K]; have := le_max_right C₁ 0; linarith
  have hW1 : 1 ≤ W := le_of_max_le_right (le_of_max_le_right hW)
  set X := nearSchur (boundaryZ b E) XX
  have hY : (passiveY X).PosSemidef := nearSchur_passive hη hXX
  have hs : 0 ≤ 1 / Real.sqrt W := by positivity
  have hdiv : ∀ C' a c' : ℝ, C' / Real.sqrt W * a * c' = C' * (1 / Real.sqrt W) * a * c' := by
    intro C' a c'; ring
  -- `P𝕊`
  have caseS : ∀ u v : Fin 2 × Fin W → ℂ,
      eLpNorm (fun ω => bilinear u (transportedSep b E XX .projS ω -
          matrixExpect (freshLaw W b) (transportedSep b E XX .projS)) v) (ENNReal.ofReal p)
          (freshLaw W b) ≤ ENNReal.ofReal (K / Real.sqrt W * vecNorm u * vecNorm v) := by
    intro u v
    set T := nearSel W * twoPortScattering b E XX
    have hT : ‖T‖ ≤ 1 := (norm_nearSel_mul_le _).trans (norm_scat_le b E hXX hη)
    have hEU : matrixExpect (freshLaw W b) (transportedSep b E XX .projS) =
        (nearSel W)ᴴ * matrixExpect (freshLaw W b) (gapLetter b E X) * T := by
      rw [FullSourceCovariance.matrixExpect_congr_ae (ae_transportedSep_projS hb0 hb hE1 hE2 hW1 hXX),
        matrixExpect_rect _ _ _ (hI W (le_of_max_le_left (le_of_max_le_right hW)) E hE X hY)]
    rw [hEU]
    have hae : ∀ᵐ ω ∂freshLaw W b, bilinear u (transportedSep b E XX .projS ω -
        (nearSel W)ᴴ * matrixExpect (freshLaw W b) (gapLetter b E X) * T) v =
        bilinear (nearSel W *ᵥ u) (gapLetter b E X ω -
          matrixExpect (freshLaw W b) (gapLetter b E X)) (T *ᵥ v) := by
      filter_upwards [ae_transportedSep_projS hb0 hb hE1 hE2 hW1 hXX] with ω hω
      rw [hω, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_assoc, bilinear_sandwich']
    rw [eLpNorm_congr_ae hae]
    refine (h1 W (le_of_max_le_left (le_of_max_le_left hW)) E hE X hY _ _).trans ?_
    rw [hdiv, hdiv]
    refine (ofReal_bound_mono (c' := vecNorm v) _ hs
      (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _)
      (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _) (vecNorm_nearSel_mulVec_le u)
      ((vecNorm_mulVec_le' T v).trans (mul_le_of_le_one_left
        (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg v) hT))).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have := mul_nonneg (mul_nonneg hs (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg u))
      (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg v)
    nlinarith
  -- `P𝕊P`
  have caseSP : ∀ u v : Fin 2 × Fin W → ℂ,
      eLpNorm (fun ω => bilinear u (transportedSep b E XX .projSProj ω -
          matrixExpect (freshLaw W b) (transportedSep b E XX .projSProj)) v) (ENNReal.ofReal p)
          (freshLaw W b) ≤ ENNReal.ofReal (K / Real.sqrt W * vecNorm u * vecNorm v) := by
    intro u v
    have hEU : matrixExpect (freshLaw W b) (transportedSep b E XX .projSProj) =
        (-c) • ((nearSel W)ᴴ * matrixExpect (freshLaw W b) (freshTransportedF b E X) *
          nearSel W) := by
      rw [FullSourceCovariance.matrixExpect_congr_ae
        (ae_transportedSep_projSProj hb0 hb hE1 hE2 hW1 hXX), matrixExpect_smul, matrixExpect_lift]
    rw [hEU]
    have hae : ∀ᵐ ω ∂freshLaw W b, bilinear u (transportedSep b E XX .projSProj ω -
        (-c) • ((nearSel W)ᴴ * matrixExpect (freshLaw W b) (freshTransportedF b E X) *
          nearSel W)) v =
        (-c) * bilinear (nearSel W *ᵥ u) (freshTransportedF b E X ω -
          matrixExpect (freshLaw W b) (freshTransportedF b E X)) (nearSel W *ᵥ v) := by
      filter_upwards [ae_transportedSep_projSProj hb0 hb hE1 hE2 hW1 hXX] with ω hω
      rw [hω, ← smul_sub, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_assoc, bilinear_smul,
        bilinear_sandwich']
    rw [eLpNorm_congr_ae hae]
    rw [show (fun ω => -c * bilinear (nearSel W *ᵥ u) (freshTransportedF b E X ω -
        matrixExpect (freshLaw W b) (freshTransportedF b E X)) (nearSel W *ᵥ v)) =
        (-c) • (fun ω => bilinear (nearSel W *ᵥ u) (freshTransportedF b E X ω -
        matrixExpect (freshLaw W b) (freshTransportedF b E X)) (nearSel W *ᵥ v)) from rfl,
      eLpNorm_const_smul, ← ofReal_norm, hc]
    have hb2 := (h2 W (le_of_max_le_right (le_of_max_le_left hW)) E hE X hY
      (nearSel W *ᵥ u) (nearSel W *ᵥ v)).2
    calc ENNReal.ofReal (2 * etaZ b E) * eLpNorm _ (ENNReal.ofReal p) (freshLaw W b)
        ≤ ENNReal.ofReal (2 * etaZ b E) * ENNReal.ofReal (max C₂ 0 * (1 / Real.sqrt W) *
            vecNorm u * vecNorm v) := by
          gcongr
          refine hb2.trans ?_
          rw [hdiv]
          exact ofReal_bound_mono _ hs (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _) (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _)
            (vecNorm_nearSel_mulVec_le u) (vecNorm_nearSel_mulVec_le v)
      _ ≤ ENNReal.ofReal (K / Real.sqrt W * vecNorm u * vecNorm v) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have h0 := mul_nonneg (mul_nonneg hs (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg u)) (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg v)
          have : 2 * etaZ b E * max C₂ 0 ≤ K := hK2
          rw [hdiv]
          nlinarith [mul_nonneg (le_max_right C₂ 0) h0]
  cases σ <;> simp [Separator.unconj, Separator.conj] at hσ
  · exact caseS
  · intro u v
    rw [show transportedSep b E XX .sStarProj =
      fun ω => (transportedSep b E XX .projS ω)ᴴ from funext (transportedSep_sStarProj b E XX),
      matrixExpect_conjTranspose]
    simp only [← conjTranspose_sub, bilinear_conjTranspose, eLpNorm_star_eq]
    rw [mul_right_comm]
    exact caseS v u
  · exact caseSP
  · intro u v
    rw [show transportedSep b E XX .projSStarProj =
      fun ω => (transportedSep b E XX .projSProj ω)ᴴ from
        funext (transportedSep_projSStarProj b E XX), matrixExpect_conjTranspose]
    simp only [← conjTranspose_sub, bilinear_conjTranspose, eLpNorm_star_eq]
    rw [mul_right_comm]
    exact caseSP v u

end BlockBand.SourceProcess.CompleteSourceGapBulk
