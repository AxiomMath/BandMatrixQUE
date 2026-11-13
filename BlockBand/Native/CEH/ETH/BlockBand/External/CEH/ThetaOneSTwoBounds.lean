module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOnePublishedAdapter
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventStability

/-!
# Bounds for the theta-one CEH `s₂` terms

This file bounds both surviving terms in `sTwoSq_one_eq` using only operator
norms and the two-body feedback gap.  The result makes precise the
remaining obstruction in the published adapter: pointwise upper-half-plane
stability gives a strict gap, but the checked-in regular-window data does not
give a dimension-uniform positive lower bound for that gap at the canonical
heights.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
open CEHNative.BlockBand.CEH

/-- The base Gamma word is bounded by the product of its four operator norms.
This retains the exact normalized-trace normalization. -/
theorem re_NTrace_gamma_word_le {N : ℕ} (hN : 0 < N)
    (Γ₁ Γ₂ A : Matrix (Fin N) (Fin N) ℂ) :
    (NTrace (Γ₁ * A * Γ₂ * Aᴴ)).re ≤ ‖Γ₁‖ * ‖A‖ * ‖Γ₂‖ * ‖A‖ := by
  calc
    (NTrace (Γ₁ * A * Γ₂ * Aᴴ)).re
        ≤ ‖NTrace (Γ₁ * A * Γ₂ * Aᴴ)‖ := Complex.re_le_norm _
    _ ≤ ‖Γ₁ * A * Γ₂ * Aᴴ‖ :=
      norm_normalizedTrace_le_localETHNorm hN _
    _ ≤ ‖Γ₁‖ * ‖A‖ * ‖Γ₂‖ * ‖Aᴴ‖ := by
      calc
        ‖Γ₁ * A * Γ₂ * Aᴴ‖ ≤ ‖Γ₁ * A * Γ₂‖ * ‖Aᴴ‖ := norm_mul_le _ _
        _ ≤ (‖Γ₁ * A‖ * ‖Γ₂‖) * ‖Aᴴ‖ := by
          gcongr
          exact norm_mul_le _ _
        _ ≤ ((‖Γ₁‖ * ‖A‖) * ‖Γ₂‖) * ‖Aᴴ‖ := by
          gcongr
          exact norm_mul_le _ _
    _ = ‖Γ₁‖ * ‖A‖ * ‖Γ₂‖ * ‖A‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]

/-- Each normalized-trace numerator in the ordinary-stability quotient is
bounded by the corresponding product of operator norms. -/
theorem norm_NTrace_three_mul_le {N : ℕ} (hN : 0 < N)
    (X A Y : Matrix (Fin N) (Fin N) ℂ) :
    ‖NTrace (X * A * Y)‖ ≤ ‖X‖ * ‖A‖ * ‖Y‖ := by
  calc
    ‖NTrace (X * A * Y)‖ ≤ ‖X * A * Y‖ :=
      norm_normalizedTrace_le_localETHNorm hN _
    _ ≤ ‖X * A‖ * ‖Y‖ := norm_mul_le _ _
    _ ≤ (‖X‖ * ‖A‖) * ‖Y‖ := by
      gcongr
      exact norm_mul_le _ _

/-- Exact uniform estimate for the ordinary-stability quotient from the
strict feedback gap: `r < 1` bounds the feedback norm `‖λ² ⟨M₁ M₂⟩‖`. -/
theorem ordinaryStabilityQuotient_le_of_feedbackGap {N : ℕ} (hN : 0 < N)
    (lambda : ℂ) (M₁ M₂ Γ₁ Γ₂ A : Matrix (Fin N) (Fin N) ℂ)
    {r : ℝ} (hfeedback : ‖lambda ^ 2 * NTrace (M₁ * M₂)‖ ≤ r)
    (hr : r < 1) :
    ‖NTrace (M₁ * A * Γ₂) * NTrace (Γ₁ * Aᴴ * M₂) /
        stabilityDenominator lambda (NTrace (M₁ * M₂))‖ ≤
      (‖M₁‖ * ‖A‖ * ‖Γ₂‖) * (‖Γ₁‖ * ‖A‖ * ‖M₂‖) * (1 - r)⁻¹ := by
  rw [div_eq_mul_inv, norm_mul]
  calc
    ‖NTrace (M₁ * A * Γ₂) * NTrace (Γ₁ * Aᴴ * M₂)‖ *
          ‖(stabilityDenominator lambda (NTrace (M₁ * M₂)))⁻¹‖
        = (‖NTrace (M₁ * A * Γ₂)‖ * ‖NTrace (Γ₁ * Aᴴ * M₂)‖) *
          ‖(stabilityDenominator lambda (NTrace (M₁ * M₂)))⁻¹‖ := by
            rw [norm_mul]
    _ ≤ ((‖M₁‖ * ‖A‖ * ‖Γ₂‖) * (‖Γ₁‖ * ‖Aᴴ‖ * ‖M₂‖)) *
          (1 - r)⁻¹ := by
      gcongr
      · exact norm_NTrace_three_mul_le hN M₁ A Γ₂
      · exact norm_NTrace_three_mul_le hN Γ₁ Aᴴ M₂
      · apply (norm_stabilityInverse_le_gap lambda (NTrace (M₁ * M₂))
          (lt_of_le_of_lt hfeedback hr)).trans
        exact inv_anti₀ (sub_pos.mpr hr) (by linarith)
    _ = (‖M₁‖ * ‖A‖ * ‖Γ₂‖) * (‖Γ₁‖ * ‖A‖ * ‖M₂‖) *
          (1 - r)⁻¹ := by rw [Matrix.l2_opNorm_conjTranspose]

/-- Exact scalar scaling showing why the qualitative strict feedback gap in
the existing positive-height interface cannot itself imply a uniform bound:
at feedback `1-ε` the ordinary-stability inverse is exactly `ε⁻¹`. -/
theorem ordinaryStability_inverse_exact_scaling {ε : ℝ} (hε : 0 < ε) :
    ‖(stabilityDenominator (1 : ℂ) ((1 - ε : ℝ) : ℂ))⁻¹‖ = ε⁻¹ := by
  rw [show stabilityDenominator (1 : ℂ) ((1 - ε : ℝ) : ℂ) = (ε : ℂ) by
    simp [stabilityDenominator]]
  simp [norm_inv, abs_of_pos hε]

/-- Combined bound for exactly the two terms which survive at theta one. -/
theorem sTwoSq_one_le_of_feedbackGap {N : ℕ} (hN : 0 < N)
    (lambda : ℂ) (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ)
    {r : ℝ} (hfeedback : ‖lambda ^ 2 * NTrace (M₁ * M₂)‖ ≤ r)
    (hr : r < 1) :
    sTwoSq 1 lambda M₁ M₂ A ≤
      ‖gammaMatrix M₁‖ * ‖A‖ * ‖gammaMatrix M₂‖ * ‖A‖ +
      ‖lambda‖ ^ 2 *
        ((‖M₁‖ * ‖A‖ * ‖gammaMatrix M₂‖) *
          (‖gammaMatrix M₁‖ * ‖A‖ * ‖M₂‖) * (1 - r)⁻¹) := by
  rw [sTwoSq_one_eq]
  apply add_le_add
  · exact re_NTrace_gamma_word_le hN _ _ _
  · exact mul_le_mul_of_nonneg_left
      (ordinaryStabilityQuotient_le_of_feedbackGap hN lambda M₁ M₂
        (gammaMatrix M₁) (gammaMatrix M₂) A hfeedback hr)
      (sq_nonneg ‖lambda‖)

/-- The corresponding direct bound for `s₂`. -/
theorem sTwo_one_le_sqrt_of_feedbackGap {N : ℕ} (hN : 0 < N)
    (lambda : ℂ) (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ)
    {r : ℝ} (hfeedback : ‖lambda ^ 2 * NTrace (M₁ * M₂)‖ ≤ r)
    (hr : r < 1) :
    sTwo 1 lambda M₁ M₂ A ≤ Real.sqrt
      (‖gammaMatrix M₁‖ * ‖A‖ * ‖gammaMatrix M₂‖ * ‖A‖ +
        ‖lambda‖ ^ 2 *
          ((‖M₁‖ * ‖A‖ * ‖gammaMatrix M₂‖) *
            (‖gammaMatrix M₁‖ * ‖A‖ * ‖M₂‖) * (1 - r)⁻¹)) := by
  unfold sTwo
  exact Real.sqrt_le_sqrt
    (sTwoSq_one_le_of_feedbackGap hN lambda M₁ M₂ A hfeedback hr)

/-- The unconditional specialization to the Hermitian MDE branch.  It is finite for every fixed
positive pair of heights, but its right-hand side contains the inverse of the feedback gap of the
branch.  Thus a
dimension-uniform `s₂` conclusion requires a dimension-uniform lower bound on
this displayed gap; pointwise strictness alone cannot supply one. -/
theorem hermitianMDEBranch_sTwo_one_le_actualGap {N : ℕ}
    {F : CEHNative.BlockBand.LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) (lambda : ℝ) (hlambda : 0 < lambda)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let M₁ := hermitianMDEBranch hF hs z₁
    let M₂ := hermitianMDEBranch hF hs z₂
    sTwo 1 (lambda : ℂ) M₁ M₂ A ≤ Real.sqrt
      (‖gammaMatrix M₁‖ * ‖A‖ * ‖gammaMatrix M₂‖ * ‖A‖ +
        ‖(lambda : ℂ)‖ ^ 2 *
          ((‖M₁‖ * ‖A‖ * ‖gammaMatrix M₂‖) *
            (‖gammaMatrix M₁‖ * ‖A‖ * ‖M₂‖) *
              (1 - ‖(lambda : ℂ) ^ 2 * NTrace (M₁ * M₂)‖)⁻¹)) := by
  dsimp only
  apply sTwo_one_le_sqrt_of_feedbackGap hN
    (lambda : ℂ)
    (hermitianMDEBranch hF (sq_pos_of_pos hlambda) z₁)
    (hermitianMDEBranch hF (sq_pos_of_pos hlambda) z₂) A le_rfl
  exact hermitianMDEBranch_pair_feedback_norm_lt_one
    hF hN lambda hlambda hz₁ hz₂

end CEHNative.BlockBand.External.CEH
