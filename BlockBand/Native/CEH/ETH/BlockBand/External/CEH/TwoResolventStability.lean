module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventPencilAdapter
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEMatrixAdapter
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Deterministic two-body stability for CEH

This module proves the finite-dimensional rank-one/tensor decomposition of the
CEH two-body stability operator and its Sherman–Morrison inverse.  It then
connects the inverse to the unconditional Hermitian matrix MDE branch, proves
cutoff denominator estimates, and derives the analytic consequences which use
only this finite-dimensional information: the inactive-cutoff two-resolvent
trace bound and the exact active-cutoff cancellation for a regularized
observable.

The other bounds in CEH Lemma 5.6 use the GUE tensorization meta-limit of the
paper and Ward/Schwarz estimates.  They are not introduced here as hypotheses
or structure fields.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped BigOperators ComplexConjugate

/-!
## Exact finite-dimensional tensor replication
-/

/-- Replication by the `d × d` identity, on the product index space. -/
def tensorReplicate {N : ℕ} (d : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ :=
  Matrix.kronecker X (1 : Matrix (Fin d) (Fin d) ℂ)

/-- Normalized trace on the product index space. -/
def productNTrace {N d : ℕ}
    (X : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) : ℂ :=
  ((N * d : ℕ) : ℂ)⁻¹ * Matrix.trace X

/-- Tensor replication preserves normalized traces exactly. -/
theorem productNTrace_tensorReplicate {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    productNTrace (tensorReplicate d X) = NTrace X := by
  unfold productNTrace tensorReplicate NTrace
    CEHNative.BlockBand.Conventions.normalizedTrace Matrix.kronecker
  rw [Matrix.trace_kronecker, Matrix.trace_one]
  simp only [Fintype.card_fin]
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

/-- Tensor replication respects multiplication, the exact finite-dimensional
identity used before the CEH meta-limit. -/
theorem tensorReplicate_mul {N d : ℕ}
    (X Y : Matrix (Fin N) (Fin N) ℂ) :
    tensorReplicate d (X * Y) = tensorReplicate d X * tensorReplicate d Y := by
  rw [tensorReplicate, tensorReplicate, tensorReplicate,
    Matrix.kronecker]
  rw [← Matrix.one_mul (1 : Matrix (Fin d) (Fin d) ℂ),
    Matrix.mul_kronecker_mul]
  simp

/-- Rank-one operator on the finite matrix space, written as the tensor
`U ⊗ ⟨·⟩`. -/
def normalizedTraceRankOne {N : ℕ}
    (U X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  NTrace X • U

/-- The feedback part of the CEH stability operator. -/
def twoBodyFeedback {N : ℕ} (lambda : ℂ)
    (M₁ M₂ X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  lambda ^ 2 • normalizedTraceRankOne (M₁ * M₂) X

/-- Exact finite-dimensional tensor/rank-one decomposition `B = I - T`. -/
theorem twoBodyStability_eq_id_sub_feedback {N : ℕ} (lambda : ℂ)
    (M₁ M₂ X : Matrix (Fin N) (Fin N) ℂ) :
    twoBodyStability lambda M₁ M₂ X = X - twoBodyFeedback lambda M₁ M₂ X := by
  simp [twoBodyStability, twoBodyFeedback, normalizedTraceRankOne, smul_smul]

/-- Squaring the rank-one trace tensor multiplies it by its unique eigenvalue
`⟨U⟩`. -/
theorem normalizedTraceRankOne_comp {N : ℕ}
    (U X : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTraceRankOne U (normalizedTraceRankOne U X) =
      NTrace U • normalizedTraceRankOne U X := by
  simp [normalizedTraceRankOne, NTrace_smul, smul_smul]
  module

/-- The explicit two-body stability inverse. -/
def twoBodyStabilityInverse {N : ℕ} (lambda : ℂ)
    (M₁ M₂ Y : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Y + (lambda ^ 2 * NTrace Y /
    stabilityDenominator lambda (NTrace (M₁ * M₂))) • (M₁ * M₂)

/-- Applying the stability operator after its tensorized inverse gives the
identity. -/
theorem twoBodyStability_inverse_right {N : ℕ} (lambda : ℂ)
    (M₁ M₂ Y : Matrix (Fin N) (Fin N) ℂ)
    (hbeta : stabilityDenominator lambda (NTrace (M₁ * M₂)) ≠ 0) :
    twoBodyStability lambda M₁ M₂
      (twoBodyStabilityInverse lambda M₁ M₂ Y) = Y := by
  unfold twoBodyStabilityInverse twoBodyStability
  rw [NTrace_add, NTrace_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  unfold stabilityDenominator at hbeta ⊢
  field_simp [hbeta]
  ring

/-- Applying the tensorized inverse after the stability operator also gives the
identity. -/
theorem twoBodyStability_inverse_left {N : ℕ} (lambda : ℂ)
    (M₁ M₂ X : Matrix (Fin N) (Fin N) ℂ)
    (hbeta : stabilityDenominator lambda (NTrace (M₁ * M₂)) ≠ 0) :
    twoBodyStabilityInverse lambda M₁ M₂
      (twoBodyStability lambda M₁ M₂ X) = X := by
  unfold twoBodyStabilityInverse twoBodyStability
  rw [NTrace_sub, NTrace_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  unfold stabilityDenominator at hbeta ⊢
  field_simp [hbeta]
  ring

/-- The deterministic approximation is exactly the tensorized inverse applied
to its bare MDE word. -/
theorem twoResolventApprox_eq_stabilityInverse {N : ℕ} (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    twoResolventApprox lambda M₁ A M₂ =
      twoBodyStabilityInverse lambda M₁ M₂ (M₁ * A * M₂) := by
  unfold twoResolventApprox twoBodyStabilityInverse
  module

/-- The inverse's normalized trace is division by the scalar stability
denominator. -/
theorem NTrace_twoBodyStabilityInverse {N : ℕ} (lambda : ℂ)
    (M₁ M₂ Y : Matrix (Fin N) (Fin N) ℂ)
    (hbeta : stabilityDenominator lambda (NTrace (M₁ * M₂)) ≠ 0) :
    NTrace (twoBodyStabilityInverse lambda M₁ M₂ Y) =
      NTrace Y / stabilityDenominator lambda (NTrace (M₁ * M₂)) := by
  unfold twoBodyStabilityInverse
  rw [NTrace_add, NTrace_smul]
  unfold stabilityDenominator at hbeta ⊢
  field_simp [hbeta]
  ring

/-- A scalar lower bound for every stability denominator, obtained by retaining
only the real part. -/
theorem abs_one_sub_re_le_norm_stabilityDenominator
    (lambda pairTrace : ℂ) :
    |1 - (lambda ^ 2 * pairTrace).re| ≤
      ‖stabilityDenominator lambda pairTrace‖ := by
  have h := Complex.abs_re_le_norm (stabilityDenominator lambda pairTrace)
  simpa [stabilityDenominator] using h

/-- Reverse-triangle quantitative lower bound for the stability denominator. -/
theorem one_sub_feedbackNorm_le_stabilityNorm (lambda pairTrace : ℂ) :
    1 - ‖lambda ^ 2 * pairTrace‖ ≤
      ‖stabilityDenominator lambda pairTrace‖ := by
  have htri :
      ‖(1 : ℂ)‖ ≤
        ‖stabilityDenominator lambda pairTrace‖ +
          ‖lambda ^ 2 * pairTrace‖ := by
    calc
      ‖(1 : ℂ)‖ =
          ‖stabilityDenominator lambda pairTrace +
            lambda ^ 2 * pairTrace‖ := by
              congr 1
              simp [stabilityDenominator]
      _ ≤ _ := norm_add_le _ _
  simpa using sub_le_iff_le_add.mpr htri

/-- Quantitative inverse bound in the exact form supplied by a strict
rank-one feedback gap. -/
theorem norm_stabilityInverse_le_gap (lambda pairTrace : ℂ)
    (hgap : ‖lambda ^ 2 * pairTrace‖ < 1) :
    ‖(stabilityDenominator lambda pairTrace)⁻¹‖ ≤
      (1 - ‖lambda ^ 2 * pairTrace‖)⁻¹ := by
  have hpos : 0 < 1 - ‖lambda ^ 2 * pairTrace‖ := sub_pos.mpr hgap
  have hbeta :
      0 < ‖stabilityDenominator lambda pairTrace‖ := by
    exact lt_of_lt_of_le hpos
      (one_sub_feedbackNorm_le_stabilityNorm lambda pairTrace)
  rw [norm_inv]
  exact inv_anti₀ hpos
    (one_sub_feedbackNorm_le_stabilityNorm lambda pairTrace)

/-- Corresponding quantitative trace estimate for the tensorized inverse. -/
theorem NTrace_twoBodyStabilityInverse_norm_le_gap {N : ℕ} (lambda : ℂ)
    (M₁ M₂ Y : Matrix (Fin N) (Fin N) ℂ)
    (hgap : ‖lambda ^ 2 * NTrace (M₁ * M₂)‖ < 1) :
    ‖NTrace (twoBodyStabilityInverse lambda M₁ M₂ Y)‖ ≤
      ‖NTrace Y‖ * (1 - ‖lambda ^ 2 * NTrace (M₁ * M₂)‖)⁻¹ := by
  have hbeta : stabilityDenominator lambda (NTrace (M₁ * M₂)) ≠ 0 := by
    exact norm_pos_iff.mp (lt_of_lt_of_le (sub_pos.mpr hgap)
      (one_sub_feedbackNorm_le_stabilityNorm lambda (NTrace (M₁ * M₂))))
  rw [NTrace_twoBodyStabilityInverse lambda M₁ M₂ Y hbeta, norm_div]
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact inv_anti₀ (sub_pos.mpr hgap)
    (one_sub_feedbackNorm_le_stabilityNorm lambda (NTrace (M₁ * M₂)))

/-- The value zero of the exact CEH cutoff is equivalent to lying strictly
below its threshold. -/
theorem cehTheta_eq_zero_iff {x : ℝ} : cehTheta x = 0 ↔ x < 0 := by
  constructor
  · intro h
    by_contra hn
    have hx : 0 ≤ x := le_of_not_gt hn
    rcases hx.eq_or_lt with rfl | hx
    · norm_num at h
    · simp [cehTheta_of_pos hx] at h
  · exact cehTheta_of_neg

/-- The value one of the exact CEH cutoff is equivalent to lying strictly
above its threshold. -/
theorem cehTheta_eq_one_iff {x : ℝ} : cehTheta x = 1 ↔ 0 < x := by
  constructor
  · intro h
    by_contra hn
    have hx : x ≤ 0 := le_of_not_gt hn
    rcases hx.eq_or_lt with rfl | hx
    · norm_num at h
    · have := cehTheta_of_neg hx
      linarith
  · exact cehTheta_of_pos

/-- In the inactive regime the scalar two-body denominator is bounded below by
`1/2`, directly from the source cutoff. -/
theorem inactiveCutoff_denominator_gt_half {N : ℕ} (lambda : ℂ)
    (M₁plus M₂minus : Matrix (Fin N) (Fin N) ℂ)
    (hinactive : regularizationCoefficient lambda M₁plus M₂minus = 0) :
    1 / 2 < ‖stabilityDenominator lambda (NTrace (M₁plus * M₂minus))‖ := by
  have harg : (lambda ^ 2 * NTrace (M₁plus * M₂minus)).re - 1 / 2 < 0 :=
    cehTheta_eq_zero_iff.mp hinactive
  have hreal : 1 / 2 <
      |1 - (lambda ^ 2 * NTrace (M₁plus * M₂minus)).re| := by
    rw [abs_of_pos]
    · linarith
    · linarith
  exact hreal.trans_le
    (abs_one_sub_re_le_norm_stabilityDenominator lambda
      (NTrace (M₁plus * M₂minus)))

/-- Hence the inactive-cutoff denominator is nonzero. -/
theorem inactiveCutoff_denominator_ne_zero {N : ℕ} (lambda : ℂ)
    (M₁plus M₂minus : Matrix (Fin N) (Fin N) ℂ)
    (hinactive : regularizationCoefficient lambda M₁plus M₂minus = 0) :
    stabilityDenominator lambda (NTrace (M₁plus * M₂minus)) ≠ 0 := by
  exact norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans
    (inactiveCutoff_denominator_gt_half lambda M₁plus M₂minus hinactive))

/-- In the active regime the mixed MDE pairing used to regularize the
observable is automatically nonzero. -/
theorem activeCutoff_pair_ne_zero {N : ℕ} (lambda : ℂ)
    (M₁plus M₂minus : Matrix (Fin N) (Fin N) ℂ)
    (hactive : regularizationCoefficient lambda M₁plus M₂minus = 1) :
    NTrace (M₁plus * M₂minus) ≠ 0 := by
  have harg : 0 <
      (lambda ^ 2 * NTrace (M₁plus * M₂minus)).re - 1 / 2 :=
    cehTheta_eq_one_iff.mp hactive
  intro hzero
  rw [hzero] at harg
  norm_num at harg

/-- First analytic bound in the inactive-cutoff version of CEH Lemma 5.6:
the trace of the deterministic approximation is at most twice the bare MDE
word.  No numerator estimate is assumed. -/
theorem inactiveCutoff_twoResolventTrace_bound {N : ℕ} (lambda : ℂ)
    (M₁plus A M₂minus : Matrix (Fin N) (Fin N) ℂ)
    (hinactive : regularizationCoefficient lambda M₁plus M₂minus = 0) :
    ‖NTrace (twoResolventApprox lambda M₁plus A M₂minus)‖ <
      2 * ‖NTrace (M₁plus * A * M₂minus)‖ ∨
    NTrace (M₁plus * A * M₂minus) = 0 := by
  let beta := stabilityDenominator lambda (NTrace (M₁plus * M₂minus))
  have hbetaHalf : 1 / 2 < ‖beta‖ :=
    inactiveCutoff_denominator_gt_half lambda M₁plus M₂minus hinactive
  have hbeta : beta ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans hbetaHalf)
  rw [twoResolventApprox_eq_stabilityInverse,
    NTrace_twoBodyStabilityInverse lambda M₁plus M₂minus _ hbeta]
  by_cases hword : NTrace (M₁plus * A * M₂minus) = 0
  · exact Or.inr hword
  · left
    rw [norm_div]
    have hwordPos : 0 < ‖NTrace (M₁plus * A * M₂minus)‖ := norm_pos_iff.mpr hword
    have hbetaPos : 0 < ‖beta‖ :=
      (by norm_num : (0 : ℝ) < 1 / 2).trans hbetaHalf
    apply (div_lt_iff₀ hbetaPos).2
    nlinarith

/-- More convenient non-strict form of the inactive-cutoff trace estimate. -/
theorem inactiveCutoff_twoResolventTrace_le {N : ℕ} (lambda : ℂ)
    (M₁plus A M₂minus : Matrix (Fin N) (Fin N) ℂ)
    (hinactive : regularizationCoefficient lambda M₁plus M₂minus = 0) :
    ‖NTrace (twoResolventApprox lambda M₁plus A M₂minus)‖ ≤
      2 * ‖NTrace (M₁plus * A * M₂minus)‖ := by
  rcases inactiveCutoff_twoResolventTrace_bound lambda M₁plus A M₂minus hinactive with h | h
  · exact h.le
  · rw [twoResolventApprox_eq_stabilityInverse,
      NTrace_twoBodyStabilityInverse lambda M₁plus M₂minus _
        (inactiveCutoff_denominator_ne_zero lambda M₁plus M₂minus hinactive),
      h]
    simp

/-- At active cutoff the regularized observable kills the bare mixed MDE word. -/
theorem activeCutoff_regularized_word_zero {N : ℕ}
    (M₁plus M₂minus A : Matrix (Fin N) (Fin N) ℂ)
    (hpair : NTrace (M₁plus * M₂minus) ≠ 0) :
    NTrace (M₁plus * regularizedObservable 1 M₁plus M₂minus A * M₂minus) = 0 :=
  regularizedObservable_trace_zero M₁plus M₂minus A hpair

/-- Consequently the trace of the full deterministic mixed approximation of an
active-cutoff regularized observable vanishes exactly. -/
theorem activeCutoff_regularized_twoResolventTrace_zero {N : ℕ} (lambda : ℂ)
    (M₁plus M₂minus A : Matrix (Fin N) (Fin N) ℂ)
    (hpair : NTrace (M₁plus * M₂minus) ≠ 0)
    (hbeta : stabilityDenominator lambda (NTrace (M₁plus * M₂minus)) ≠ 0) :
    NTrace (twoResolventApprox lambda M₁plus
      (regularizedObservable 1 M₁plus M₂minus A) M₂minus) = 0 := by
  rw [twoResolventApprox_eq_stabilityInverse,
    NTrace_twoBodyStabilityInverse lambda M₁plus M₂minus _ hbeta]
  rw [regularizedObservable_trace_zero M₁plus M₂minus A hpair]
  simp

/-- Fully cutoff-facing form: coefficient one supplies the nonzero pairing,
so only the already-proved stability nonvanishing is needed. -/
theorem activeCutoff_regularized_twoResolventTrace_zero_of_coefficient
    {N : ℕ} (lambda : ℂ)
    (M₁plus M₂minus A : Matrix (Fin N) (Fin N) ℂ)
    (hactive : regularizationCoefficient lambda M₁plus M₂minus = 1)
    (hbeta : stabilityDenominator lambda (NTrace (M₁plus * M₂minus)) ≠ 0) :
    NTrace (twoResolventApprox lambda M₁plus
      (regularizedObservable 1 M₁plus M₂minus A) M₂minus) = 0 :=
  activeCutoff_regularized_twoResolventTrace_zero lambda M₁plus M₂minus A
    (activeCutoff_pair_ne_zero lambda M₁plus M₂minus hactive) hbeta

/-!
## Unitary transport to the arbitrary Hermitian MDE branch
-/

/-- The normalized two-body pairing of the arbitrary Hermitian branch is
exactly the normalized pairing in its diagonal spectral model. -/
theorem NTrace_hermitianMDEBranch_pair_eq_diagonal {N : ℕ}
    {F : CEHNative.BlockBand.LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) (lambda : ℝ) (hlambda : 0 < lambda)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let f := CEHNative.BlockBand.CEH.hermitianSpectrum hF
    let m₁ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₁
    let m₂ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₂
    NTrace
        (CEHNative.BlockBand.CEH.hermitianMDEBranch hF hs z₁ *
          CEHNative.BlockBand.CEH.hermitianMDEBranch hF hs z₂) =
      NTrace
        (PencilAdapter.mdeMatrix f lambda z₁ m₁ *
          PencilAdapter.mdeMatrix f lambda z₂ m₂) := by
  dsimp only
  simp only [CEHNative.BlockBand.CEH.hermitianMDEBranch,
    dite_eq_left hN]
  rw [
    CEHNative.BlockBand.CEH.hermitianMDEMean_of_im_pos hF hN
      (sq_pos_of_pos hlambda) hz₁,
    CEHNative.BlockBand.CEH.hermitianMDEMean_of_im_pos hF hN
      (sq_pos_of_pos hlambda) hz₂]
  change CEHNative.BlockBand.Conventions.normalizedTrace
      (CEHNative.BlockBand.CEH.spectralLift hF _ *
        CEHNative.BlockBand.CEH.spectralLift hF _) =
    NTrace (PencilAdapter.mdeMatrix _ _ _ _ * PencilAdapter.mdeMatrix _ _ _ _)
  rw [CEHNative.BlockBand.CEH.normalizedTrace_spectralLift_mul]
  exact (PencilAdapter.NTrace_mdeMatrix_mul _ _ _ _ _ _).symm

/-- Quantitative strict feedback gap for two upper-half-plane parameters of
the arbitrary Hermitian MDE branch.  This is the unitary transport of the
scalar MDE Cauchy–Schwarz estimate. -/
theorem hermitianMDEBranch_pair_feedback_norm_lt_one {N : ℕ}
    {F : CEHNative.BlockBand.LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) (lambda : ℝ) (hlambda : 0 < lambda)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let M₁ := CEHNative.BlockBand.CEH.hermitianMDEBranch hF hs z₁
    let M₂ := CEHNative.BlockBand.CEH.hermitianMDEBranch hF hs z₂
    ‖(lambda : ℂ) ^ 2 * NTrace (M₁ * M₂)‖ < 1 := by
  dsimp only
  let f := CEHNative.BlockBand.CEH.hermitianSpectrum hF
  let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  let m₁ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₁
  let m₂ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₂
  have hm₁ := CEHNative.BlockBand.CEH.upperBranch_isSolution
    hN f hs hz₁
  have hm₂ := CEHNative.BlockBand.CEH.upperBranch_isSolution
    hN f hs hz₂
  have hscalar :=
    CEHNative.BlockBand.CEH.mixed_average_norm_lt_inv
      hN f hs hz₁ hz₂ hm₁ hm₂ false
  rw [NTrace_hermitianMDEBranch_pair_eq_diagonal hF hN lambda hlambda hz₁ hz₂,
    PencilAdapter.NTrace_mdeMatrix_mul]
  rw [norm_mul, norm_pow]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlambda]
  simpa [f, hs] using hscalar

/-- The quantitative inverse bound transported to two arbitrary Hermitian MDE
branches. -/
theorem hermitianMDEBranch_pair_inverse_norm_le_gap {N : ℕ}
    {F : CEHNative.BlockBand.LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) (lambda : ℝ) (hlambda : 0 < lambda)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let M₁ := CEHNative.BlockBand.CEH.hermitianMDEBranch hF hs z₁
    let M₂ := CEHNative.BlockBand.CEH.hermitianMDEBranch hF hs z₂
    ‖(stabilityDenominator (lambda : ℂ) (NTrace (M₁ * M₂)))⁻¹‖ ≤
      (1 - ‖(lambda : ℂ) ^ 2 * NTrace (M₁ * M₂)‖)⁻¹ := by
  dsimp only
  exact norm_stabilityInverse_le_gap _ _
    (hermitianMDEBranch_pair_feedback_norm_lt_one
      hF hN lambda hlambda hz₁ hz₂)

/-- The unconditional Hermitian matrix MDE branch has a nonzero two-body
stability denominator for every upper-half-plane parameter and every positive
real coupling. -/
theorem hermitianMDEBranch_stability_ne_zero {N : ℕ}
    {F : CEHNative.BlockBand.LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) (lambda : ℝ) (hlambda : 0 < lambda)
    {z : ℂ} (hz : 0 < z.im) :
    stabilityDenominator (lambda : ℂ)
      (NTrace
        (CEHNative.BlockBand.CEH.hermitianMDEBranch hF
            (sq_pos_of_pos hlambda) z *
          CEHNative.BlockBand.CEH.hermitianMDEBranch hF
            (sq_pos_of_pos hlambda) z)) ≠ 0 := by
  simpa [stabilityDenominator] using
    (CEHNative.BlockBand.CEH.matrix_stability_ne_zero
      hF hN (sq_pos_of_pos hlambda) hz)

/-- Therefore the tensorized stability inverse is an inverse on the
unconditional matrix MDE branch. -/
theorem hermitianMDEBranch_stability_inverse_right {N : ℕ}
    {F : CEHNative.BlockBand.LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) (lambda : ℝ) (hlambda : 0 < lambda)
    {z : ℂ} (hz : 0 < z.im)
    (Y : Matrix (Fin N) (Fin N) ℂ) :
    let M := CEHNative.BlockBand.CEH.hermitianMDEBranch hF
      (sq_pos_of_pos hlambda) z
    twoBodyStability (lambda : ℂ) M M
      (twoBodyStabilityInverse (lambda : ℂ) M M Y) = Y := by
  dsimp only
  exact twoBodyStability_inverse_right (lambda : ℂ) _ _ Y
    (hermitianMDEBranch_stability_ne_zero hF hN lambda hlambda hz)

end CEHNative.BlockBand.External.CEH
