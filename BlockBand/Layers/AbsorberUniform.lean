module

public import BlockBand.Layers.AbsorberDeterministic

/-!
# Uniformity of the absorber constant in the spectral parameter

The constant `C₀ = absorberConstant (-z⁻¹)` of the deterministic absorber bound
(`absorber_lower`) is bounded uniformly for `Im z ≥ η₀ > 0` and `|z| ≤ M`, since
`Im(-z⁻¹) = Im z / |z|² ≥ η₀ / M²` and `|-z⁻¹| = |z|⁻¹ ≤ η₀⁻¹`. This gives the constants of the
Gaussian absorption lemma depending only on `b, η₀, M`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

/-- `Im(-z⁻¹) = Im z / |z|²`. -/
theorem im_neg_inv (z : ℂ) : (-z⁻¹).im = z.im / Complex.normSq z := by
  rw [Complex.neg_im, Complex.inv_im]; ring

/-- `Im(-z⁻¹) ≥ η₀ / M²` for `Im z ≥ η₀ > 0`, `|z| ≤ M`. -/
theorem im_neg_inv_ge {z : ℂ} {η₀ M : ℝ} (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hM : ‖z‖ ≤ M) :
    η₀ / M ^ 2 ≤ (-z⁻¹).im := by
  have hzpos : 0 < z.im := lt_of_lt_of_le hη hz
  have hnz : 0 < ‖z‖ := by
    have : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hzpos; exact lt_irrefl 0 hzpos
    exact norm_pos_iff.mpr this
  have hM0 : 0 < M := lt_of_lt_of_le hnz hM
  rw [im_neg_inv, ← Complex.sq_norm]
  have hsq : ‖z‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hM 2
  calc η₀ / M ^ 2 ≤ z.im / M ^ 2 := div_le_div_of_nonneg_right hz (by positivity)
    _ ≤ z.im / ‖z‖ ^ 2 := div_le_div_of_nonneg_left hzpos.le (by positivity) hsq

/-- `|-z⁻¹| ≤ η₀⁻¹` for `Im z ≥ η₀ > 0`. -/
theorem norm_neg_inv_le {z : ℂ} {η₀ : ℝ} (hη : 0 < η₀) (hz : η₀ ≤ z.im) : ‖-z⁻¹‖ ≤ η₀⁻¹ := by
  have hzn : η₀ ≤ ‖z‖ := hz.trans (Complex.im_le_norm z)
  rw [norm_neg, norm_inv]
  exact inv_anti₀ hη hzn

/-- The uniform absorber constant `M η₀^{-1/2} + 1 + M η₀^{-3/2}`. -/
def absorberBound (η₀ M : ℝ) : ℝ :=
  M * (Real.sqrt η₀)⁻¹ + 1 + η₀⁻¹ * (M * (Real.sqrt η₀)⁻¹)

/-- **Uniform absorber constant** (the Gaussian absorption lemma, constants depending only on
`η₀, M`): `absorberConstant (-z⁻¹) ≤ absorberBound η₀ M` whenever `Im z ≥ η₀ > 0` and
`|z| ≤ M`. -/
theorem absorberConstant_le {z : ℂ} {η₀ M : ℝ} (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hM : ‖z‖ ≤ M) :
    absorberConstant (-z⁻¹) ≤ absorberBound η₀ M := by
  have hzpos : 0 < z.im := lt_of_lt_of_le hη hz
  have hnz : 0 < ‖z‖ := by
    have : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hzpos; exact lt_irrefl 0 hzpos
    exact norm_pos_iff.mpr this
  have hM0 : 0 < M := lt_of_lt_of_le hnz hM
  have hγ := im_neg_inv_ge hη hz hM
  have hγpos : 0 < η₀ / M ^ 2 := by positivity
  -- `(√γ)⁻¹ ≤ M / √η₀`
  have hsq : (Real.sqrt (-z⁻¹).im)⁻¹ ≤ M * (Real.sqrt η₀)⁻¹ := by
    have h1 : Real.sqrt (η₀ / M ^ 2) ≤ Real.sqrt (-z⁻¹).im := Real.sqrt_le_sqrt hγ
    have h2 : Real.sqrt (η₀ / M ^ 2) = Real.sqrt η₀ / M := by
      rw [Real.sqrt_div hη.le, Real.sqrt_sq hM0.le]
    have h3 : 0 < Real.sqrt η₀ / M := by positivity
    calc (Real.sqrt (-z⁻¹).im)⁻¹ ≤ (Real.sqrt η₀ / M)⁻¹ := by
          rw [← h2]; exact inv_anti₀ (by rw [h2]; exact h3) h1
      _ = M * (Real.sqrt η₀)⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have hw := norm_neg_inv_le hη hz
  unfold absorberConstant absorberBound
  have h0 : 0 ≤ (Real.sqrt (-z⁻¹).im)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hprod : ‖-z⁻¹‖ * (Real.sqrt (-z⁻¹).im)⁻¹ ≤ η₀⁻¹ * (M * (Real.sqrt η₀)⁻¹) :=
    mul_le_mul hw hsq h0 (inv_nonneg.mpr hη.le)
  linarith

end BlockBand.Layers
