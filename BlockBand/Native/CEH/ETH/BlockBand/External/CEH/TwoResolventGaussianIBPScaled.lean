module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPBlockAdapter

/-!
# Coupling-scaled GUE two-resolvent cancellation

This module transports the normalized variance-`1/N` Gaussian loop identity to
a real coupling `lambda`.  The transport is algebraic: for nonzero `lambda`,
the pencil `H + lambda W - z` is factored by `lambda`; the zero-coupling case
is handled separately.  Thus no concentration or local-law input is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal

/-- The full-coordinate resolvent with a real coupling in front of the
reconstructed normalized GUE block. -/
def scaledFullGUEResolvent {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (lambda : ℝ) (z : ℂ)
    (y : HermitianCoordinateSpace N) : Matrix (Fin N) (Fin N) ℂ :=
  (H + (lambda : ℂ) • (hermitianGUEBlock N y).1 -
    z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- Factoring a nonzero real coupling out of the pencil transports the scaled
resolvent to the already constructed normalized GUE resolvent. -/
theorem scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
    {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    (lambda : ℝ) (hlambda : lambda ≠ 0) {z : ℂ} (hz : z.im ≠ 0)
    (y : HermitianCoordinateSpace N) :
    scaledFullGUEResolvent H lambda z y =
      ((lambda : ℂ)⁻¹) •
        fullGUEResolvent (((lambda : ℂ)⁻¹) • H)
          (((lambda : ℂ)⁻¹) * z) y := by
  let c : ℂ := (lambda : ℂ)
  let B : Matrix (Fin N) (Fin N) ℂ :=
    c⁻¹ • H + (hermitianGUEBlock N y).1 -
      (c⁻¹ * z) • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hc : c ≠ 0 := by simpa [c] using Complex.ofReal_ne_zero.mpr hlambda
  let _ : Invertible c := invertibleOfNonzero hc
  have hcim : (c⁻¹ * z).im ≠ 0 := by
    simp [c, Complex.mul_im, hlambda, hz]
  have hscaled : (c⁻¹ • H).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH]
    congr 1
    simp [c]
  have hBherm : (c⁻¹ • H + (hermitianGUEBlock N y).1).IsHermitian :=
    hscaled.add (hermitianGUEBlock N y).2
  have hBunit : IsUnit B.det := by
    have hu := CEHNative.BlockBand.isUnit_resolventPencil
      (c⁻¹ • H + (hermitianGUEBlock N y).1) hBherm hcim
    apply (Matrix.isUnit_iff_isUnit_det B).mp
    have hneg : IsUnit (-((c⁻¹ * z) •
        (1 : Matrix (Fin N) (Fin N) ℂ) -
          (c⁻¹ • H + (hermitianGUEBlock N y).1))) :=
      (IsUnit.neg_iff _).2 hu
    simpa [B] using hneg
  have hpencil :
      H + c • (hermitianGUEBlock N y).1 -
          z • (1 : Matrix (Fin N) (Fin N) ℂ) = c • B := by
    ext i j
    simp [B, c]
    field_simp [Complex.ofReal_ne_zero.mpr hlambda]
  unfold scaledFullGUEResolvent fullGUEResolvent
  rw [hpencil, Matrix.inv_smul B c hBunit]
  rfl

/-- At zero coupling, the scaled resolvent is deterministic. -/
@[simp] theorem scaledFullGUEResolvent_zero
    {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (y : HermitianCoordinateSpace N) :
    scaledFullGUEResolvent H 0 z y =
      (H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := by
  simp [scaledFullGUEResolvent]

/-- **Coupling-scaled normalized GUE master cancellation.**  The outside
random source carries one factor of `lambda`, while Gaussian covariance
produces the exact `lambda ^ 2` multiplying both trace contractions. -/
theorem scaledNormalizedGUE_literalBlock_masterCancellation
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    (lambda : ℝ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      (((lambda : ℂ) • (hermitianGUEBlock N y).1) *
        (scaledFullGUEResolvent H₁ lambda z₁ y * A *
          scaledFullGUEResolvent H₂ lambda z₂ y)) p q
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) +
      (∫ y : HermitianCoordinateSpace N,
        ((lambda : ℂ) ^ 2 *
            ((N : ℂ)⁻¹ *
              (scaledFullGUEResolvent H₁ lambda z₁ y).trace)) *
            (scaledFullGUEResolvent H₁ lambda z₁ y * A *
              scaledFullGUEResolvent H₂ lambda z₂ y) p q +
          ((lambda : ℂ) ^ 2 *
            ((N : ℂ)⁻¹ *
              (scaledFullGUEResolvent H₁ lambda z₁ y * A *
                scaledFullGUEResolvent H₂ lambda z₂ y).trace)) *
            scaledFullGUEResolvent H₂ lambda z₂ y p q
        ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) = 0 := by
  by_cases hlambda : lambda = 0
  · subst lambda
    simp
  · let c : ℂ := (lambda : ℂ)
    let H₁' : Matrix (Fin N) (Fin N) ℂ := c⁻¹ • H₁
    let H₂' : Matrix (Fin N) (Fin N) ℂ := c⁻¹ • H₂
    let z₁' : ℂ := c⁻¹ * z₁
    let z₂' : ℂ := c⁻¹ * z₂
    have hc : c ≠ 0 := by
      simpa [c] using Complex.ofReal_ne_zero.mpr hlambda
    have hH₁' : H₁'.IsHermitian := by
      change (c⁻¹ • H₁).IsHermitian
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH₁]
      congr 1
      simp [c]
    have hH₂' : H₂'.IsHermitian := by
      change (c⁻¹ • H₂).IsHermitian
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH₂]
      congr 1
      simp [c]
    have hz₁' : z₁'.im ≠ 0 := by
      simp [z₁', c, Complex.mul_im, hlambda, hz₁]
    have hz₂' : z₂'.im ≠ 0 := by
      simp [z₂', c, Complex.mul_im, hlambda, hz₂]
    have hG₁ (y : HermitianCoordinateSpace N) :
        fullGUEResolvent H₁' z₁' y =
          c • scaledFullGUEResolvent H₁ lambda z₁ y := by
      rw [scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
        H₁ hH₁ lambda hlambda hz₁ y]
      simp [H₁', z₁', c, smul_smul, hc]
    have hG₂ (y : HermitianCoordinateSpace N) :
        fullGUEResolvent H₂' z₂' y =
          c • scaledFullGUEResolvent H₂ lambda z₂ y := by
      rw [scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
        H₂ hH₂ lambda hlambda hz₂ y]
      simp [H₂', z₂', c, smul_smul, hc]
    have hmaster :=
      normalizedGUE_literalBlock_masterCancellation
        hN H₁' H₂' A hH₁' hH₂' hz₁' hz₂' p q
    have hleft :
        (∫ y : HermitianCoordinateSpace N,
          (((lambda : ℂ) • (hermitianGUEBlock N y).1) *
            (scaledFullGUEResolvent H₁ lambda z₁ y * A *
              scaledFullGUEResolvent H₂ lambda z₂ y)) p q
          ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) =
          c⁻¹ * (∫ y : HermitianCoordinateSpace N,
            ((hermitianGUEBlock N y).1 *
              (fullGUEResolvent H₁' z₁' y * A *
                fullGUEResolvent H₂' z₂' y)) p q
            ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ))
              (by positivity)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [hG₁, hG₂]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply]
      field_simp [c, Complex.ofReal_ne_zero.mpr hlambda]
      ring
    have hright :
        (∫ y : HermitianCoordinateSpace N,
          ((lambda : ℂ) ^ 2 *
              ((N : ℂ)⁻¹ *
                (scaledFullGUEResolvent H₁ lambda z₁ y).trace)) *
              (scaledFullGUEResolvent H₁ lambda z₁ y * A *
                scaledFullGUEResolvent H₂ lambda z₂ y) p q +
            ((lambda : ℂ) ^ 2 *
              ((N : ℂ)⁻¹ *
                (scaledFullGUEResolvent H₁ lambda z₁ y * A *
                  scaledFullGUEResolvent H₂ lambda z₂ y).trace)) *
              scaledFullGUEResolvent H₂ lambda z₂ y p q
          ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) =
          c⁻¹ * (∫ y : HermitianCoordinateSpace N,
            ((N : ℂ)⁻¹ * (fullGUEResolvent H₁' z₁' y).trace) *
                (fullGUEResolvent H₁' z₁' y * A *
                  fullGUEResolvent H₂' z₂' y) p q +
              ((N : ℂ)⁻¹ *
                (fullGUEResolvent H₁' z₁' y * A *
                  fullGUEResolvent H₂' z₂' y).trace) *
                fullGUEResolvent H₂' z₂' y p q
            ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ))
              (by positivity)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [hG₁, hG₂]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
        Matrix.trace_smul]
      field_simp [c, Complex.ofReal_ne_zero.mpr hlambda]
      ring
    rw [hleft, hright, ← mul_add]
    rw [hmaster, mul_zero]

end CEHNative.BlockBand.External.CEH
