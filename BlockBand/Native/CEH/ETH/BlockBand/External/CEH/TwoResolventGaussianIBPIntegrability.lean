module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPPaperAdapter

/-!
# Bochner integrability for the paper-facing CEH Gaussian loop

All results here are finite-dimensional consequences of nonreal Hermitian
resolvent bounds and Gaussian first moments.  They supply the analytic adapter
needed to merge the previously split integrals; no local law, concentration
estimate, or remainder bound is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal
open PencilAdapter

abbrev normalizedGUEMeasure (N : ℕ) :=
  hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)

/-- Every entry of a coupling-scaled full GUE resolvent is integrable. -/
theorem integrable_scaledFullGUEResolvent_entry
    {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) (i j : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      scaledFullGUEResolvent H lambda z y i j) (normalizedGUEMeasure N) := by
  by_cases hlambda : lambda = 0
  · subst lambda
    simp only [scaledFullGUEResolvent_zero]
    exact integrable_const _
  · let c : ℂ := (lambda : ℂ)
    let H' : Matrix (Fin N) (Fin N) ℂ := c⁻¹ • H
    let z' : ℂ := c⁻¹ * z
    have hH' : H'.IsHermitian := by
      change (c⁻¹ • H).IsHermitian
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH]
      congr 1
      simp [c]
    have hz' : z'.im ≠ 0 := by
      simp [z', c, Complex.mul_im, hlambda, hz]
    have h := (integrable_fullGUECoordinateResolventEntry
      H' hH' hz' i j).const_mul c⁻¹
    apply h.congr
    filter_upwards with y
    rw [scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
      H hH lambda hlambda hz y]
    rfl

/-- Every entry of a coupling-scaled two-resolvent word is integrable. -/
theorem integrable_scaledFullGUE_twoResolvent_entry
    {N : ℕ} (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    (lambda : ℝ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (i j : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      (scaledFullGUEResolvent H₁ lambda z₁ y * A *
        scaledFullGUEResolvent H₂ lambda z₂ y) i j)
      (normalizedGUEMeasure N) := by
  by_cases hlambda : lambda = 0
  · subst lambda
    simp only [scaledFullGUEResolvent_zero]
    exact integrable_const _
  · let c : ℂ := (lambda : ℂ)
    let H₁' : Matrix (Fin N) (Fin N) ℂ := c⁻¹ • H₁
    let H₂' : Matrix (Fin N) (Fin N) ℂ := c⁻¹ • H₂
    let z₁' : ℂ := c⁻¹ * z₁
    let z₂' : ℂ := c⁻¹ * z₂
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
    have h := (integrable_fullGUEPlainTwoResolventEntry
      H₁' H₂' A hH₁' hH₂' hz₁' hz₂' i j).const_mul (c⁻¹ ^ 2)
    apply h.congr
    filter_upwards with y
    rw [scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
      H₁ hH₁ lambda hlambda hz₁ y,
      scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
      H₂ hH₂ lambda hlambda hz₂ y]
    unfold fullGUEPlainTwoResolventEntry
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply]
    ring

/-- A real GUE coordinate times a scaled two-resolvent entry is integrable. -/
theorem integrable_coordinate_mul_scaledFullGUE_twoResolvent_entry
    {N : ℕ} (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    (lambda : ℝ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N))) (i j : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      (y k : ℂ) *
        (scaledFullGUEResolvent H₁ lambda z₁ y * A *
          scaledFullGUEResolvent H₂ lambda z₂ y) i j)
      (normalizedGUEMeasure N) := by
  by_cases hlambda : lambda = 0
  · subst lambda
    have hk : Integrable
        (fun y : HermitianCoordinateSpace N => ((y k : ℝ) : ℂ))
        (normalizedGUEMeasure N) :=
      (integrable_normalizedGUECoordinate k).ofReal
    convert hk.mul_const
      ((scaledFullGUEResolvent H₁ 0 z₁ 0 * A *
        scaledFullGUEResolvent H₂ 0 z₂ 0) i j) using 1
    funext y
    simp
  · let c : ℂ := (lambda : ℂ)
    let H₁' : Matrix (Fin N) (Fin N) ℂ := c⁻¹ • H₁
    let H₂' : Matrix (Fin N) (Fin N) ℂ := c⁻¹ • H₂
    let z₁' : ℂ := c⁻¹ * z₁
    let z₂' : ℂ := c⁻¹ * z₂
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
    have h := (integrable_coordinate_mul_fullGUEPlainTwoResolventEntry
      H₁' H₂' A hH₁' hH₂' hz₁' hz₂' k i j).const_mul (c⁻¹ ^ 2)
    apply h.congr
    filter_upwards with y
    rw [scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
      H₁ hH₁ lambda hlambda hz₁ y,
      scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
      H₂ hH₂ lambda hlambda hz₂ y]
    unfold fullGUEPlainTwoResolventEntry
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply]
    ring

/-- The random-source entry in the scaled underlined word is integrable. -/
theorem integrable_scaled_underlinedRandomSource
    {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    (lambda : ℝ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      underlinedRandomSource (lambda : ℂ) (hermitianGUEBlock N y).1
        (scaledFullGUEResolvent H₁ lambda z₁ y) A
        (scaledFullGUEResolvent H₂ lambda z₂ y) p q)
      (normalizedGUEMeasure N) := by
  have hsum : Integrable (fun y : HermitianCoordinateSpace N =>
      ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ∑ a : Fin N, ((lambda : ℂ) * gueCoordinateDirection N k p a) *
          ((y k : ℂ) *
            (scaledFullGUEResolvent H₁ lambda z₁ y * A *
              scaledFullGUEResolvent H₂ lambda z₂ y) a q))
      (normalizedGUEMeasure N) := by
    apply integrable_finsetSum Finset.univ
    intro k hk
    apply integrable_finsetSum Finset.univ
    intro a ha
    exact (integrable_coordinate_mul_scaledFullGUE_twoResolvent_entry
      H₁ H₂ A hH₁ hH₂ lambda hz₁ hz₂ k a q).const_mul _
  apply hsum.congr
  filter_upwards with y
  unfold underlinedRandomSource
  rw [Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.mul_assoc]
  rw [
    hermitianGUEBlock_mul_twoResolvent_apply]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- At unit coupling, the two trace-feedback terms are integrable.  The proof
uses the already established derivative contraction, so it needs no separate
three-resolvent estimate. -/
theorem integrable_normalizedGUE_underlinedTraceFeedback
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      underlinedTraceFeedback 1
        (fullGUEResolvent H₁ z₁ y) A (fullGUEResolvent H₂ z₂ y) p q)
      (normalizedGUEMeasure N) := by
  let v := fun k : Fin (Fintype.card (HermitianCoordinate N)) =>
    (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
      (by positivity) k : ℂ)
  have hsum : Integrable (fun y : HermitianCoordinateSpace N =>
      ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ∑ a : Fin N, v k * gueCoordinateDirection N k p a *
          fullGUEPlainTwoResolventDerivativeEntry
            H₁ H₂ A z₁ z₂ k a q y) (normalizedGUEMeasure N) := by
    apply integrable_finsetSum Finset.univ
    intro k hk
    apply integrable_finsetSum Finset.univ
    intro a ha
    exact (integrable_fullGUEPlainTwoResolventDerivativeEntry
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k a q).const_mul _
  apply hsum.neg.congr
  filter_upwards with y
  have hc := normalizedGUE_leftDerivativeContraction hN
    (fullGUEResolvent H₁ z₁ y) (fullGUEResolvent H₂ z₂ y) A
  have hentry := congrFun (congrFun hc p) q
  rw [sum_smul_mul_apply] at hentry
  change -(∑ k : Fin (Fintype.card (HermitianCoordinate N)),
    ∑ a : Fin N, v k * gueCoordinateDirection N k p a *
      fullGUEPlainTwoResolventDerivativeEntry
        H₁ H₂ A z₁ z₂ k a q y) =
    underlinedTraceFeedback 1
      (fullGUEResolvent H₁ z₁ y) A (fullGUEResolvent H₂ z₂ y) p q
  unfold v fullGUEPlainTwoResolventDerivativeEntry
  rw [hentry]
  unfold underlinedTraceFeedback NTrace
    CEHNative.BlockBand.Conventions.normalizedTrace
  simp only [one_pow, one_mul, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_mul, Matrix.neg_apply, neg_neg, smul_eq_mul]

/-- The trace-feedback part of the underlined word is integrable for every
real coupling. -/
theorem integrable_scaled_underlinedTraceFeedback
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    (lambda : ℝ) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      underlinedTraceFeedback (lambda : ℂ)
        (scaledFullGUEResolvent H₁ lambda z₁ y) A
        (scaledFullGUEResolvent H₂ lambda z₂ y) p q)
      (normalizedGUEMeasure N) := by
  by_cases hlambda : lambda = 0
  · subst lambda
    simp [underlinedTraceFeedback]
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
    have h := (integrable_normalizedGUE_underlinedTraceFeedback
      hN H₁' H₂' A hH₁' hH₂' hz₁' hz₂' p q).const_mul c⁻¹
    dsimp [H₁', H₂', z₁', z₂'] at h
    apply h.congr
    filter_upwards with y
    rw [scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
      H₁ hH₁ lambda hlambda hz₁ y,
      scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
      H₂ hH₂ lambda hlambda hz₂ y]
    unfold underlinedTraceFeedback NTrace
      CEHNative.BlockBand.Conventions.normalizedTrace
    simp only [Matrix.trace_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    dsimp [c]
    field_simp [Complex.ofReal_ne_zero.mpr hlambda]

/-- Every entry of the centered trace remainder is integrable. -/
theorem integrable_scaled_centeredTraceRemainder
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    (lambda : ℝ) (m t : ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      centeredTraceRemainder (lambda : ℂ) m t
        (scaledFullGUEResolvent H₁ lambda z₁ y) A
        (scaledFullGUEResolvent H₂ lambda z₂ y) p q)
      (normalizedGUEMeasure N) := by
  have hfb := integrable_scaled_underlinedTraceFeedback hN
    H₁ H₂ A hH₁ hH₂ lambda hz₁ hz₂ p q
  have hword := integrable_scaledFullGUE_twoResolvent_entry
    H₁ H₂ A hH₁ hH₂ lambda hz₁ hz₂ p q
  have hG₂ := integrable_scaledFullGUEResolvent_entry
    H₂ hH₂ lambda hz₂ p q
  have h := (hfb.sub (hword.const_mul ((lambda : ℂ) ^ 2 * m))).sub
    (hG₂.const_mul ((lambda : ℂ) ^ 2 * t))
  apply h.congr
  filter_upwards with y
  unfold centeredTraceRemainder centeredResolventTrace
    centeredTwoResolventTrace underlinedTraceFeedback
  simp only [Pi.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Fixed left matrix multiplication preserves entrywise integrability. -/
theorem integrable_fixedMatrix_mul_entry
    {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ)
    (X : HermitianCoordinateSpace N → Matrix (Fin N) (Fin N) ℂ)
    (p q : Fin N)
    (hX : ∀ a : Fin N, Integrable (fun y => X y a q)
      (normalizedGUEMeasure N)) :
    Integrable (fun y => (B * X y) p q) (normalizedGUEMeasure N) := by
  simp only [Matrix.mul_apply]
  apply integrable_finsetSum Finset.univ
  intro a ha
  exact (hX a).const_mul _

/-- Paper-facing integrability of the random-source part. -/
theorem integrable_pencilAdapter_underlinedRandomSource
    {N : ℕ} (f : Spectrum N) (lambda : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      underlinedRandomSource (lambda : ℂ) (hermitianGUEBlock N y).1
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q)
      (normalizedGUEMeasure N) := by
  simpa only [← scaledFullGUEResolvent_deformationMatrix] using
    integrable_scaled_underlinedRandomSource
      (deformationMatrix f) (deformationMatrix f) A
      (deformationMatrix_isHermitian f) (deformationMatrix_isHermitian f)
      lambda hz₁ hz₂ p q

/-- Paper-facing integrability of the trace-feedback part. -/
theorem integrable_pencilAdapter_underlinedTraceFeedback
    {N : ℕ} (hN : 0 < N) (f : Spectrum N) (lambda : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      underlinedTraceFeedback (lambda : ℂ)
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q)
      (normalizedGUEMeasure N) := by
  simpa only [← scaledFullGUEResolvent_deformationMatrix] using
    integrable_scaled_underlinedTraceFeedback hN
      (deformationMatrix f) (deformationMatrix f) A
      (deformationMatrix_isHermitian f) (deformationMatrix_isHermitian f)
      lambda hz₁ hz₂ p q

/-- Paper-facing integrability of the centered trace remainder. -/
theorem integrable_pencilAdapter_centeredTraceRemainder
    {N : ℕ} (hN : 0 < N) (f : Spectrum N) (lambda : ℝ)
    (m t : ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      centeredTraceRemainder (lambda : ℂ) m t
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q)
      (normalizedGUEMeasure N) := by
  simpa only [← scaledFullGUEResolvent_deformationMatrix] using
    integrable_scaled_centeredTraceRemainder hN
      (deformationMatrix f) (deformationMatrix f) A
      (deformationMatrix_isHermitian f) (deformationMatrix_isHermitian f)
      lambda m t hz₁ hz₂ p q

/-- The complete paper-facing underlined word is integrable entrywise. -/
theorem integrable_pencilAdapter_underlinedWord
    {N : ℕ} (hN : 0 < N) (f : Spectrum N) (lambda : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      underlinedTwoResolventWord (lambda : ℂ) (hermitianGUEBlock N y).1
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q)
      (normalizedGUEMeasure N) := by
  have hs := integrable_pencilAdapter_underlinedRandomSource
    f lambda A hz₁ hz₂ p q
  have hf := integrable_pencilAdapter_underlinedTraceFeedback
    hN f lambda A hz₁ hz₂ p q
  apply (hs.add hf).congr
  filter_upwards with y
  exact (congrFun (congrFun
    (underlinedTwoResolventWord_eq_source_add_feedback
      (lambda : ℂ) (hermitianGUEBlock N y).1
      (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
      (resolvent f lambda (hermitianGUEBlock N y).1 z₂)) p) q).symm

/-- With integrability now established, the split Gaussian cancellation is a
single Bochner expectation of the underlined word. -/
theorem pencilAdapter_underlined_masterCancellation_integral
    {N : ℕ} (hN : 0 < N) (f : Spectrum N) (lambda : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      underlinedTwoResolventWord (lambda : ℂ) (hermitianGUEBlock N y).1
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q
      ∂normalizedGUEMeasure N) = 0 := by
  rw [show (fun y : HermitianCoordinateSpace N =>
      underlinedTwoResolventWord (lambda : ℂ) (hermitianGUEBlock N y).1
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q) =
      (fun y =>
        underlinedRandomSource (lambda : ℂ) (hermitianGUEBlock N y).1
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q +
        underlinedTraceFeedback (lambda : ℂ)
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂) p q) by
    funext y
    exact congrFun (congrFun
      (underlinedTwoResolventWord_eq_source_add_feedback
        (lambda : ℂ) (hermitianGUEBlock N y).1
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂)) p) q]
  rw [integral_add
    (integrable_pencilAdapter_underlinedRandomSource
      f lambda A hz₁ hz₂ p q)
    (integrable_pencilAdapter_underlinedTraceFeedback
      hN f lambda A hz₁ hz₂ p q)]
  exact pencilAdapter_splitUnderlined_masterCancellation
    hN f lambda A hz₁ hz₂ p q

/-- Integrability of the deterministic-left-multiplied one-resolvent term in
`pencilAdapter_centeredError_identity`. -/
theorem integrable_pencilAdapter_centeredError_oneResolvent
    {N : ℕ} (f : Spectrum N) (lambda : ℝ) (t : ℂ)
    (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ)
    {z₂ : ℂ} (hz₂ : z₂.im ≠ 0) (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      (M₁ *
        (A + (((lambda : ℂ) ^ 2 * t) •
          (1 : Matrix (Fin N) (Fin N) ℂ))) *
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂ - M₂)) p q)
      (normalizedGUEMeasure N) := by
  let B := M₁ *
    (A + (((lambda : ℂ) ^ 2 * t) •
      (1 : Matrix (Fin N) (Fin N) ℂ)))
  apply integrable_fixedMatrix_mul_entry B
  intro a
  have hG : Integrable (fun y : HermitianCoordinateSpace N =>
      resolvent f lambda (hermitianGUEBlock N y).1 z₂ a q)
      (normalizedGUEMeasure N) := by
    simpa only [← scaledFullGUEResolvent_deformationMatrix] using
      integrable_scaledFullGUEResolvent_entry
        (deformationMatrix f) (deformationMatrix_isHermitian f)
        lambda hz₂ a q
  exact hG.sub (integrable_const _)

/-- Integrability of the deterministic-left-multiplied centered trace
remainder in `pencilAdapter_centeredError_identity`. -/
theorem integrable_pencilAdapter_left_centeredTraceRemainder
    {N : ℕ} (hN : 0 < N) (f : Spectrum N) (lambda : ℝ)
    (m t : ℂ) (M₁ A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      (M₁ * centeredTraceRemainder (lambda : ℂ) m t
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂)) p q)
      (normalizedGUEMeasure N) := by
  apply integrable_fixedMatrix_mul_entry M₁
  intro a
  exact integrable_pencilAdapter_centeredTraceRemainder
    hN f lambda m t A hz₁ hz₂ a q

/-- Integrability of the deterministic-left-multiplied underlined word, the
term whose expectation vanishes in the integrated centered-error equation. -/
theorem integrable_pencilAdapter_left_underlinedWord
    {N : ℕ} (hN : 0 < N) (f : Spectrum N) (lambda : ℝ)
    (M₁ A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    Integrable (fun y : HermitianCoordinateSpace N =>
      (M₁ * underlinedTwoResolventWord (lambda : ℂ)
        (hermitianGUEBlock N y).1
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂)) p q)
      (normalizedGUEMeasure N) := by
  apply integrable_fixedMatrix_mul_entry M₁
  intro a
  exact integrable_pencilAdapter_underlinedWord
    hN f lambda A hz₁ hz₂ a q

/-- A deterministic left factor may be brought through the now-integrable
expectation; hence the left-multiplied underlined term in the centered-error
identity has expectation zero. -/
theorem pencilAdapter_left_underlined_expectation_eq_zero
    {N : ℕ} (hN : 0 < N) (f : Spectrum N) (lambda : ℝ)
    (M₁ A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      (M₁ * underlinedTwoResolventWord (lambda : ℂ)
        (hermitianGUEBlock N y).1
        (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
        (resolvent f lambda (hermitianGUEBlock N y).1 z₂)) p q
      ∂normalizedGUEMeasure N) = 0 := by
  simp only [Matrix.mul_apply]
  rw [integral_finsetSum Finset.univ (fun a ha =>
    (integrable_pencilAdapter_underlinedWord
      hN f lambda A hz₁ hz₂ a q).const_mul (M₁ p a))]
  apply Finset.sum_eq_zero
  intro a ha
  rw [integral_const_mul,
    pencilAdapter_underlined_masterCancellation_integral
      hN f lambda A hz₁ hz₂ a q, mul_zero]

/-- The fully combined centered-error expectation equation.  The vanished
underlined expectation is eliminated using concrete Bochner integrability;
the right side consists exactly of the one-resolvent deviation and centered
trace remainder, with no asserted estimate on either. -/
theorem pencilAdapter_centeredError_expectation
    {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (m₁ : ℂ) (A M₂ : Matrix (Fin N) (Fin N) ℂ)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : z₂.im ≠ 0)
    (hm₁ : CEHNative.BlockBand.CEH.IsSolution
      f (lambda ^ 2) z₁ m₁)
    (hstable : stabilityDenominator (lambda : ℂ)
      (NTrace (mdeMatrix f lambda z₁ m₁ * M₂)) ≠ 0)
    (p q : Fin N) :
    let M₁ := mdeMatrix f lambda z₁ m₁
    let Mhat := twoResolventApprox (lambda : ℂ) M₁ A M₂
    let t := NTrace Mhat
    (∫ y : HermitianCoordinateSpace N,
      (resolvent f lambda (hermitianGUEBlock N y).1 z₁ * A *
        resolvent f lambda (hermitianGUEBlock N y).1 z₂ - Mhat) p q
      ∂normalizedGUEMeasure N) =
    ∫ y : HermitianCoordinateSpace N,
      (M₁ * (A + (((lambda : ℂ) ^ 2 * t) •
          (1 : Matrix (Fin N) (Fin N) ℂ))) *
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂ - M₂) +
        M₁ * centeredTraceRemainder (lambda : ℂ) m₁ t
          (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
          (resolvent f lambda (hermitianGUEBlock N y).1 z₂)) p q
      ∂normalizedGUEMeasure N := by
  dsimp only
  let M₁ := mdeMatrix f lambda z₁ m₁
  let Mhat := twoResolventApprox (lambda : ℂ) M₁ A M₂
  let t := NTrace Mhat
  let oneTerm := fun y : HermitianCoordinateSpace N =>
    M₁ * (A + (((lambda : ℂ) ^ 2 * t) •
      (1 : Matrix (Fin N) (Fin N) ℂ))) *
      (resolvent f lambda (hermitianGUEBlock N y).1 z₂ - M₂)
  let remTerm := fun y : HermitianCoordinateSpace N =>
    M₁ * centeredTraceRemainder (lambda : ℂ) m₁ t
      (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
      (resolvent f lambda (hermitianGUEBlock N y).1 z₂)
  let underTerm := fun y : HermitianCoordinateSpace N =>
    M₁ * underlinedTwoResolventWord (lambda : ℂ)
      (hermitianGUEBlock N y).1
      (resolvent f lambda (hermitianGUEBlock N y).1 z₁) A
      (resolvent f lambda (hermitianGUEBlock N y).1 z₂)
  have hone := integrable_pencilAdapter_centeredError_oneResolvent
    f lambda t M₁ M₂ A hz₂ p q
  have hrem := integrable_pencilAdapter_left_centeredTraceRemainder
    hN f lambda m₁ t M₁ A (ne_of_gt hz₁) hz₂ p q
  have hunder := integrable_pencilAdapter_left_underlinedWord
    hN f lambda M₁ A (ne_of_gt hz₁) hz₂ p q
  rw [show (fun y : HermitianCoordinateSpace N =>
      (resolvent f lambda (hermitianGUEBlock N y).1 z₁ * A *
        resolvent f lambda (hermitianGUEBlock N y).1 z₂ - Mhat) p q) =
      (fun y => (oneTerm y + remTerm y - underTerm y) p q) by
    funext y
    exact congrFun (congrFun
      (pencilAdapter_centeredError_identity
        f lambda hlambda m₁ A z₁ z₂ hz₁ hm₁ M₂ hstable y) p) q]
  change (∫ y : HermitianCoordinateSpace N,
      (oneTerm y + remTerm y - underTerm y) p q
      ∂normalizedGUEMeasure N) =
    ∫ y : HermitianCoordinateSpace N,
      (oneTerm y + remTerm y) p q ∂normalizedGUEMeasure N
  simp only [Matrix.add_apply, Matrix.sub_apply]
  calc
    (∫ y : HermitianCoordinateSpace N,
      oneTerm y p q + remTerm y p q - underTerm y p q
      ∂normalizedGUEMeasure N) =
        (∫ y : HermitianCoordinateSpace N,
          oneTerm y p q + remTerm y p q ∂normalizedGUEMeasure N) -
        ∫ y : HermitianCoordinateSpace N,
          underTerm y p q ∂normalizedGUEMeasure N :=
      integral_sub (hone.add hrem) hunder
    _ = _ := by
      rw [pencilAdapter_left_underlined_expectation_eq_zero
        hN f lambda M₁ A (ne_of_gt hz₁) hz₂ p q, sub_zero]

end CEHNative.BlockBand.External.CEH
