module

public import BlockBand.SourceProcess.CompleteSourceGapBulk.GapMeanStrictBulk

/-!
# `GapLetterMean`, uniformly on `bulkInterval κ`

`gapLetterMean_bulk` is the version of `gapLetterMean_holds` whose constants are uniform in
`E ∈ bulkInterval κ`, the stationary jet, `W ≥ W₀` and the passive input `X`. Hypothesis:
`PassiveBoundsStatement`. The proof applies `gapMean_strict_bulk` at the regularization
`X_n = X - i(n+1)⁻¹` and lets `n → ∞` (Vitali, with a uniform `L²` bound from the passive moments
at `p = 4`, already uniform on `bulkInterval κ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGapBulk

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission
open BlockBand.Transmission.PassiveLayer (PassiveBoundsStatement layerAt lAt g21 pK pTwo
  layerMatrix_regX liftX MomBd letter_momBd paramDisk)
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **`GapLetterMean`, uniformly on `bulkInterval κ`** (bulk-uniform copy of `gapLetterMean_holds`;
constants uniform in `E ∈ bulkInterval κ`, the stationary jet `s`, `W ≥ W₀` and passive `X`). -/
theorem gapLetterMean_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        ‖matrixExpect (freshLaw W b) (gapLetter b E X) -
            thetaStar b E s • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤
          C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
            ((W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨C, W₀, hC, hst⟩ := gapMean_strict_bulk hA hb0 hb hκ
  obtain ⟨Cq, Wq, hmq⟩ := hA.moments b hb0 hb _ hκ (2 * 2) (by norm_num)
  refine ⟨C, max W₀ Wq, hC, fun W hW E hE s hs X hY => ?_⟩
  obtain ⟨h1, h2, -, -, -, -, hz⟩ := bulk_scalars hb0 hb hκ hE
  simp only [max_le_iff] at hW
  obtain ⟨hW0, hWq⟩ := hW
  set μ := freshLaw W b
  set z := boundaryZ b E
  set Xn := fun n : ℕ => PassiveCovariance.regX X n
  set Cm := max Cq 0
  have hCm : 0 ≤ Cm := le_max_right _ _
  set Kb := (‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ + 1) * (Cm * Cm)
  have hL2 : ∀ Y : Matrix (Fin W) (Fin W) ℂ, (passiveY Y).PosSemidef →
      ‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - Y‖ ≤ ‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ + 1 →
      ∀ i j, eLpNorm (fun ω => gapLetter b E Y ω i j) 2 μ ≤ ENNReal.ofReal Kb := by
    intro Y hY' hK i j
    obtain ⟨-, hg, hk, hl⟩ := hmq W hWq E hE z hz Y hY'
    obtain ⟨hgM, -, hlM⟩ := letter_momBd (b := b) ⟨hg, hk, hl⟩
    have hprod := (PassiveLayer.MomBd.mul (p := 2) two_pos hlM hgM hCm).const_mul
      (c := ‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ + 1) (by positivity)
    have hb2 : eLpNorm (fun ω => gapLetter b E Y ω i j) (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal Kb :=
      (eLpNorm_mono_ae_real (measurable_gapLetter b E Y).eval_matrix.aestronglyMeasurable
        (ae_of_all _ fun ω => (FullSource.norm_entry_le_op _ i j).trans ((norm_gapLetter_le b E Y ω).trans
          (mul_le_mul_of_nonneg_right hK (by positivity))))).trans hprod.2
    simpa using hb2
  have hdetX := (hmq W hWq E hE z hz X hY).1
  have hent : ∀ i j, Tendsto (fun n => ∫ ω, gapLetter b E (Xn n) ω i j ∂μ) atTop
      (𝓝 (∫ ω, gapLetter b E X ω i j ∂μ)) := by
    intro i j
    refine PassiveCovariance.tendsto_integral_of_ae_of_eLpNorm_two
      (fun n => (measurable_gapLetter b E (Xn n)).eval_matrix) ENNReal.ofReal_ne_top
      (fun n => hL2 _ (PassiveCovariance.passiveY_regX_posSemidef hY n) (norm_K_regX_le' z X n) i j)
      (hL2 X hY (by linarith) i j) ?_
    filter_upwards [hdetX] with ω hω
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (tendsto_gapLetter_regX b E X ω hω) i) j
  have hM : Tendsto (fun n => matrixExpect μ (gapLetter b E (Xn n))) atTop
      (𝓝 (matrixExpect μ (gapLetter b E X))) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hent i j
  have hL := (hM.sub_const (thetaStar b E s • (1 : Matrix (Fin W) (Fin W) ℂ))).norm
  have hR : Tendsto (fun n => C * (jetDistance0 b E (Xn n) + jetDistance1 b E s (Xn n) +
      passiveMass b E (Xn n) / W + ((W : ℝ)⁻¹) ^ 2)) atTop
      (𝓝 (C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
        ((W : ℝ)⁻¹) ^ 2))) :=
    ((((PassiveCovariance.tendsto_jet0_regX hb0 hb h1 h2 hY).add
      (PassiveCovariance.tendsto_jet1_regX hb0 hb h1 h2 hY s)).add
      ((PassiveCovariance.tendsto_mass_regX hb0 hb h1 h2 hY).div_const _)).add_const _).const_mul _
  exact le_of_tendsto_of_tendsto' hL hR fun n =>
    hst W hW0 E hE s hs (Xn n) (PassiveCovariance.passiveY_regX_posDef hY n)

end BlockBand.SourceProcess.CompleteSourceGapBulk
