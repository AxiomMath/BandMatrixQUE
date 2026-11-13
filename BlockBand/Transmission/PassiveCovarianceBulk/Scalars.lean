module

public import BlockBand.Transmission.PassiveCovariance.Step3
public import BlockBand.Transmission.PathScalar.MeanBulk

/-!
# Uniform scalar bounds on `bulkInterval κ`

Lower bounds on `η = etaZ b E` and upper bounds on `1/η`, `constB` and `constC`, uniform in
`E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar

variable {b κ E : ℝ}

theorem etaZ_pos_bulk (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) : 0 < etaZ b E :=
  etaZ_pos b E (by linarith) (bulk_bounds hκ hE).1 (bulk_bounds hκ hE).2

theorem inv_etaZ_le_bulk (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    (etaZ b E)⁻¹ ≤ (etaLow b κ)⁻¹ :=
  inv_anti₀ (etaLow_pos (by linarith) hκ) (etaLow_le (by linarith) hκ hE)

theorem inv_etaZ_pow_le_bulk (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) (n : ℕ) :
    1 / etaZ b E ^ n ≤ 1 / etaLow b κ ^ n := by
  have hl := etaLow_pos (b := b) (by linarith) hκ
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl.le
    (etaLow_le (by linarith) hκ hE) n)

/-- Uniform majorant of `constB b E = 2/η² + 1/η`. -/
def constBL (b κ : ℝ) : ℝ := 2 / etaLow b κ ^ 2 + 1 / etaLow b κ

/-- Uniform majorant of `constC b E = constB/η + 1/η³`. -/
def constCL (b κ : ℝ) : ℝ := constBL b κ / etaLow b κ + 1 / etaLow b κ ^ 3

theorem constBL_nonneg (hb : b < 1 / 2) (hκ : 0 < κ) : 0 ≤ constBL b κ := by
  have := etaLow_pos (b := b) (by linarith) hκ
  unfold constBL; positivity

theorem constCL_nonneg (hb : b < 1 / 2) (hκ : 0 < κ) : 0 ≤ constCL b κ := by
  have := etaLow_pos (b := b) (by linarith) hκ
  have := constBL_nonneg hb hκ
  unfold constCL; positivity

theorem constB_le_bulk (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    constB b E ≤ constBL b κ := by
  have h2 := inv_etaZ_pow_le_bulk hb hκ hE 2
  have h1 := inv_etaZ_pow_le_bulk hb hκ hE 1
  simp only [pow_one] at h1
  unfold constB constBL
  rw [div_eq_mul_one_div 2 (etaZ b E ^ 2), div_eq_mul_one_div 2 (etaLow b κ ^ 2)]
  linarith

theorem constC_le_bulk (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    constC b E ≤ constCL b κ := by
  have hη := etaZ_pos_bulk hb hκ hE
  have hl := etaLow_pos (b := b) (by linarith) hκ
  have h3 := inv_etaZ_pow_le_bulk hb hκ hE 3
  have hB := constB_le_bulk hb hκ hE
  have hB0 : 0 ≤ constB b E := by
    unfold constB; positivity
  have hi := inv_etaZ_le_bulk hb hκ hE
  have : constB b E / etaZ b E ≤ constBL b κ / etaLow b κ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul hB hi (inv_nonneg.mpr hη.le) (constBL_nonneg hb hκ)
  unfold constC constCL
  linarith

end BlockBand.Transmission.CovarianceBulk
