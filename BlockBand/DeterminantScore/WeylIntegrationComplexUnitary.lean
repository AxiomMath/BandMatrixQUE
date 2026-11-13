module

public import BlockBand.DeterminantScore.WeylIntegrationBorder

/-!
# Weyl integration: unitary invariance of Lebesgue measure on `ℂ^n`

`complexUnitaryInvariance` proves `ComplexUnitaryInvarianceStatement`: `∫ F(Wv) dv = ∫ F(v) dv`
for unitary `W` and measurable `F ≥ 0`. With it, `weylIntegration_of_diagonalBorderLaw` derives
the Weyl integration formula from the bordered-matrix law for a diagonal corner.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open MeasureTheory Matrix BlockBand.DeterminantScore.Sector
open scoped ENNReal NNReal

variable {n : ℕ}

/-- The conjugation-invariant Gaussian weight `c exp(-Re tr M²/2)` on the corner. -/
def cornerWeight (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (EigenDensity.hermGaussianConst n 1 * Real.exp (-(M * M).trace.re / 2))

theorem cornerWeight_hermOfCoord (y : HermCoord n → ℝ) :
    cornerWeight n (hermOfCoord y) = ENNReal.ofReal (EigenDensity.hermGaussianDensity n 1 y) := by
  rw [EigenDensity.hermGaussianDensity_eq one_pos]
  simp [cornerWeight]

theorem cornerWeight_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ * W = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) : cornerWeight n (W * M * Wᴴ) = cornerWeight n M := by
  unfold cornerWeight
  rw [show W * M * Wᴴ * (W * M * Wᴴ) = W * (M * (Wᴴ * W) * M * Wᴴ) by
    simp only [Matrix.mul_assoc], hW, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc,
    hW, Matrix.mul_one]

theorem measurable_cornerWeight : Measurable (cornerWeight n) := by
  refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
  exact continuous_const.mul (Real.continuous_exp.comp
    (((Complex.continuous_re.comp (continuous_id.matrix_mul continuous_id).matrix_trace).neg).div_const
      _))

theorem lintegral_cornerWeight : ∫⁻ y : HermCoord n → ℝ, cornerWeight n (hermOfCoord y) = 1 := by
  simp_rw [cornerWeight_hermOfCoord]
  have h := measure_univ (μ := hermGaussian n 1)
  rw [EigenDensity.hermGaussian_eq_withDensity one_pos, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h
  exact h

/-- The Gaussian weight on the corner entry. -/
def entryWeight (a : ℝ) : ℝ≥0∞ := ENNReal.ofReal (ProbabilityTheory.gaussianPDFReal 0 1 a)

theorem measurable_entryWeight : Measurable entryWeight :=
  ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_gaussianPDFReal _ _)

theorem lintegral_entryWeight : ∫⁻ a, entryWeight a = 1 :=
  ProbabilityTheory.lintegral_gaussianPDFReal_eq_one 0 one_ne_zero

/-- The test function `ρ(corner) · F(border) · γ(corner entry)`. -/
def borderTest (F : (Fin n → ℂ) → ℝ≥0∞) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℝ≥0∞ :=
  cornerWeight n (B.submatrix Fin.castSucc Fin.castSucc) * F (fun i => B i.castSucc (Fin.last n)) *
    entryWeight (B (Fin.last n) (Fin.last n)).re

theorem borderTest_borderHerm (F : (Fin n → ℂ) → ℝ≥0∞) (M : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (a : ℝ) :
    borderTest F (borderHerm M v a) = cornerWeight n M * F v * entryWeight a := by
  have h1 : (borderHerm M v a).submatrix Fin.castSucc Fin.castSucc = M := by
    ext i j; simp [borderHerm]
  simp only [borderTest, h1]
  simp [borderHerm]

theorem measurable_borderTest {F : (Fin n → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (borderTest F) := by
  unfold borderTest
  refine (measurable_cornerWeight.comp (Continuous.measurable ?_)).mul
    (hF.comp (Continuous.measurable ?_)) |>.mul
      (measurable_entryWeight.comp (Continuous.measurable ?_))
  · exact continuous_matrix fun i j => continuous_apply_apply _ _
  · exact continuous_pi fun i => continuous_apply_apply _ _
  · exact Complex.continuous_re.comp (continuous_apply_apply _ _)

theorem lintegral_triple {Φ : (Fin n → ℂ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ y : HermCoord n → ℝ, ∫⁻ v : Fin n → ℂ, ∫⁻ a : ℝ,
        cornerWeight n (hermOfCoord y) * Φ v * entryWeight a = ∫⁻ v, Φ v := by
  simp_rw [lintegral_const_mul _ measurable_entryWeight, lintegral_entryWeight, mul_one,
    lintegral_const_mul _ hΦ]
  rw [lintegral_mul_const (f := fun y : HermCoord n → ℝ => cornerWeight n (hermOfCoord y)) _
      (measurable_cornerWeight.comp continuous_hermOfCoord.measurable),
    lintegral_cornerWeight, one_mul]

/-- **Unitary invariance of Lebesgue measure on `ℂ^n`**: `∫ F(Wv) dv = ∫ F(v) dv`. -/
theorem complexUnitaryInvariance : ComplexUnitaryInvarianceStatement := by
  intro n W F hF
  set Wm : Matrix (Fin n) (Fin n) ℂ := (W : Matrix (Fin n) (Fin n) ℂ)
  have hWW : Wmᴴ * Wm = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.UnitaryGroup.star_mul_self W
  have hDD : (borderHerm Wm 0 1)ᴴ * borderHerm Wm 0 1 = 1 := borderHerm_unit_conjTranspose_mul hWW
  have hV : ((borderHerm Wm 0 1)ᴴ)ᴴ * (borderHerm Wm 0 1)ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.1 hDD
  have hG := measurable_borderTest hF
  have hinv := lintegral_unitaryCoord (hG.comp continuous_hermOfCoord.measurable) hV
  simp only [Function.comp_apply, BlockBand.Angular.DetFactor.hermOfCoord_unitaryCoord,
    Matrix.conjTranspose_conjTranspose] at hinv
  rw [cornerFubini n _ hG, cornerFubini n (fun B => borderTest F (borderHerm Wm 0 1 * B * (borderHerm Wm 0 1)ᴴ))
    (hG.comp (((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).measurable))] at hinv
  simp_rw [borderHerm_conj, borderTest_borderHerm, cornerWeight_conj hWW] at hinv
  have hFW : Measurable fun v : Fin n → ℂ => F (Wm *ᵥ v) :=
    hF.comp (Continuous.measurable (continuous_const.matrix_mulVec continuous_id))
  rw [lintegral_triple hFW, lintegral_triple hF] at hinv
  exact hinv

/-- **The Weyl integration formula from the diagonal-corner bordered law.** -/
theorem weylIntegration_of_diagonalBorderLaw (hD : DiagonalBorderLawStatement) :
    EigenDensity.WeylIntegrationStatement :=
  weylIntegration_of_diagonal complexUnitaryInvariance hD

end BlockBand.DeterminantScore.WeylIntegration
