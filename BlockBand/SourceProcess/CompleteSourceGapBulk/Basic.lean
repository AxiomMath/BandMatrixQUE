module

public import BlockBand.SourceProcess.CompleteSourceGap.GapMeanHolds
public import BlockBand.Transmission.SourceMixingBulk.MatchedScalars

/-!
# Bulk-uniform scalar bounds, integrability and covariances

Versions of the scalar bounds, of `integrable_gapLetter` and of `gap_covs` whose constants are
uniform for `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGapBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer (passiveLetter passiveWord PassiveBoundsStatement
  layerAt g21 lAt paramDisk MomBd moments_holds)
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Uniform scalar bounds on `bulkInterval κ`. -/
theorem bulk_scalars {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) :
    -2 < E ∧ E < 2 ∧ 0 < PathScalar.etaLow b κ ∧ PathScalar.etaLow b κ ≤ etaZ b E ∧
      etaZ b E ≤ 3 ∧ ‖boundaryZ b E + E‖ ≤ 5 ∧ boundaryZ b E ∈ paramDisk b E := by
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hz := PassiveLayer.boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  obtain ⟨-, hz3, -, -⟩ := PassiveLayer.disk_bounds hb0 hb hκ hE hz
  refine ⟨h1, h2, PathScalar.etaLow_pos (by linarith) hκ, PathScalar.etaLow_le (by linarith) hκ hE,
    (Complex.im_le_norm _).trans hz3, ?_, hz⟩
  have hE' : ‖(E : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact (norm_add_le _ _).trans (by linarith)

/-- Bulk-uniform copy of `integrable_gapLetter`. -/
theorem integrable_gapLetter_bulk (hGA : GaussianAbsorptionContract) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      ∀ x y, Integrable (fun ω => gapLetter b E X ω x y) (freshLaw W b) := by
  obtain ⟨C, W₀, hM⟩ := moments_holds hGA b hb0 hb _ hκ 2 (by norm_num)
  refine ⟨max W₀ 1, fun W hW E hE X hY x y => ?_⟩
  set z := boundaryZ b E
  obtain ⟨-, hG, -, hL⟩ := hM W (le_of_max_le_left hW) E hE z
    (bulk_scalars hb0 hb hκ hE).2.2.2.2.2.2 X hY
  set C' := max C 0
  set k := ‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖
  have hGm : MomBd (freshLaw W b) (fun ω => ‖layerAt E z X ω‖) (2 * 1) C' :=
    ⟨(continuous_norm.measurable.comp (PassiveLayer.measurable_layerAt E z X)).aestronglyMeasurable,
      by rw [show (2 : ℝ) * 1 = 2 by norm_num]
         exact hG.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hLm : MomBd (freshLaw W b) (fun ω => ‖lAt E z X ω‖) (2 * 1) C' :=
    ⟨(continuous_norm.measurable.comp (PassiveLayer.measurable_lAt E z X)).aestronglyMeasurable,
      by rw [show (2 : ℝ) * 1 = 2 by norm_num]
         exact hL.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hP := PassiveLayer.MomBd.mul (p := 1) one_pos hLm (hGm.const_mul (c := k) (norm_nonneg _))
    (le_max_right _ _)
  have hm : Measurable (gapLetter b E X) := measurable_gapLetter b E X
  refine integrable_entries_of_momBd hm (by positivity)
    (hP.mono hm.norm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)) x y
  rw [norm_norm]
  calc ‖gapLetter b E X ω‖ ≤ ‖lAt E z X ω‖ * ‖g21 E z X ω‖ * k :=
        (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
          (norm_nonneg _))
    _ ≤ ‖lAt E z X ω‖ * (k * ‖layerAt E z X ω‖) := by
        rw [mul_assoc, mul_comm (‖g21 E z X ω‖)]
        gcongr
        exact norm_g21_le E z X ω

/-- Bulk-uniform copy of `gap_covs` (the four covariances are `O(W⁻²)`). -/
theorem gap_covs_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      let μ := freshLaw W b
      (∀ x y, Integrable (fun ω => passiveLetter E (boundaryZ b E) X ω 0 x y) μ) ∧
      (∀ x y, Integrable (fun ω => passiveLetter E (boundaryZ b E) X ω 4 x y) μ) ∧
      (∀ x y, Integrable (fun ω => kfGap b E X ω x y) μ) ∧
      Integrable (tau0 b E X) μ ∧ Integrable (tau1 b E X) μ ∧
      Integrable (physTr b E X) μ ∧ Integrable (portTr b E X) μ ∧
      ‖covR μ (tau0 b E X) (fun ω => passiveLetter E (boundaryZ b E) X ω 4)‖ ≤ C / (W : ℝ) ^ 2 ∧
      ‖covR μ (physTr b E X) (kfGap b E X)‖ ≤ C / (W : ℝ) ^ 2 ∧
      ‖covR μ (tau1 b E X) (fun ω => passiveLetter E (boundaryZ b E) X ω 4)‖ ≤ C / (W : ℝ) ^ 2 ∧
      ‖covR μ (portTr b E X) (kfGap b E X)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₀, h⟩ := hA.traceMatrix b hb0 hb _ hκ 2 1
  refine ⟨max C 0, W₀, le_max_right _ _, fun W hW E hE X hX => ?_⟩
  intro μ
  have hz : boundaryZ b E ∈ paramDisk b E := (bulk_scalars hb0 hb hκ hE).2.2.2.2.2.2
  have hD1 : ∀ j : Fin 2, ‖(fun _ : Fin 2 => (1 : Matrix (Fin W) (Fin W) ℂ)) j‖ ≤ 1 :=
    fun _ => norm_one_matrix_le
  have hD2 : ∀ j : Fin 3, ‖(fun _ : Fin 3 => (1 : Matrix (Fin W) (Fin W) ℂ)) j‖ ≤ 1 :=
    fun _ => norm_one_matrix_le
  have hCW : C / (W : ℝ) ^ 2 ≤ max C 0 / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have c1 := h W hW E hE _ hz X hX 2 1 (by norm_num) (by norm_num) ![(1, false), (2, false)]
    (fun _ => 1) (fun _ => (4, false)) (fun _ => 1) hD2 hD1
  have c2 := h W hW E hE _ hz X hX 1 2 (by norm_num) (by norm_num) (fun _ => (0, false))
    (fun _ => 1) ![(5, false), (2, false)] (fun _ => 1) hD1 hD2
  have c3 := h W hW E hE _ hz X hX 2 1 (by norm_num) (by norm_num) ![(3, false), (3, false)]
    (fun _ => 1) (fun _ => (4, false)) (fun _ => 1) hD2 hD1
  have c4 := h W hW E hE _ hz X hX 1 2 (by norm_num) (by norm_num) (fun _ => (3, false))
    (fun _ => 1) ![(5, false), (2, false)] (fun _ => 1) hD1 hD2
  have c5 := h W hW E hE _ hz X hX 1 1 (by norm_num) (by norm_num) (fun _ => (0, false))
    (fun _ => 1) (fun _ => (0, false)) (fun _ => 1) hD1 hD1
  simp only [passiveWord_two, passiveWord_single_fun] at c1 c2 c3 c4 c5
  exact ⟨c5.2.1, c1.2.1, c2.2.1, c1.1, c3.1, c2.1, c4.1, c1.2.2.2.trans hCW, c2.2.2.2.trans hCW,
    c3.2.2.2.trans hCW, c4.2.2.2.trans hCW⟩

end BlockBand.SourceProcess.CompleteSourceGapBulk
