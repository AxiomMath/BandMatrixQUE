module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.OneResolventExpectationBias
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEQuantitative

/-!
# High-height expectation-to-MDE bias for one resolvent

This module converts the exact centered Gaussian master equation into an
unconditional comparison with the finite-dimensional scalar MDE branch.  The
comparison is pointwise in an upper-half-plane parameter and is restricted to
an explicit high-height contraction domain.  It is not a local law and makes
no uniform-in-parameter or stochastic-domination assertion.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal ENNReal
open PencilAdapter

/-- Mean of the concrete replicated normalized-GUE resolvent trace. -/
def replicatedExpectedOneResolventTrace {N : ℕ} (d : ℕ)
    (f : Spectrum N) (lambda : ℝ) (z : ℂ) : ℂ :=
  ∫ y, replicatedOneResolventTrace d f lambda z y
    ∂replicatedNormalizedGUEMeasure N d

/-- The expected normalized trace retains the deterministic nonreal-resolvent
bound. -/
theorem norm_replicatedExpectedOneResolventTrace_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖replicatedExpectedOneResolventTrace d f lambda z‖ ≤ |z.im|⁻¹ := by
  unfold replicatedExpectedOneResolventTrace
  calc
    _ ≤ ∫ _y : ReplicatedGUECoordinateSpace N d, |z.im|⁻¹
        ∂replicatedNormalizedGUEMeasure N d := by
      apply norm_integral_le_of_norm_le (integrable_const |z.im|⁻¹)
      exact ae_of_all _ fun y =>
        norm_replicatedOneResolventTrace_le hN hd f lambda hz y
    _ = |z.im|⁻¹ := by simp

/-- On the high-height domain the MDE pencil evaluated at the expected trace
still has strictly positive effective height, without assuming the desired
MDE comparison in advance. -/
theorem effectiveHeight_expectedTrace_pos
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : 0 < z.im)
    (hheight : lambda ^ 2 < z.im ^ 2) :
    0 < CEHNative.BlockBand.CEH.effectiveHeight (lambda ^ 2) z
      (replicatedExpectedOneResolventTrace d f lambda z) := by
  have hmnorm := norm_replicatedExpectedOneResolventTrace_le
    hN hd f lambda hz.ne'
  have him : -(z.im)⁻¹ ≤
      (replicatedExpectedOneResolventTrace d f lambda z).im := by
    have habs := Complex.abs_im_le_norm
      (replicatedExpectedOneResolventTrace d f lambda z)
    rw [abs_of_pos hz] at hmnorm
    have hneg : -‖replicatedExpectedOneResolventTrace d f lambda z‖ ≤
        (replicatedExpectedOneResolventTrace d f lambda z).im :=
      neg_le_of_abs_le habs
    exact (neg_le_neg hmnorm).trans hneg
  unfold CEHNative.BlockBand.CEH.effectiveHeight
  have hmul := mul_le_mul_of_nonneg_left him (sq_nonneg lambda)
  have hinv : z.im * (z.im)⁻¹ = 1 := mul_inv_cancel₀ hz.ne'
  nlinarith [hheight]

/-- The integrated diagonal resolvent equation, before Gaussian IBP is used. -/
theorem replicated_expected_resolvent_diagonal_equation
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Fin (N * d)) :
    ((replicatedSpectrum d f i : ℂ) - z) *
        (∫ y, scaledFullGUEResolvent
          (deformationMatrix (replicatedSpectrum d f)) lambda z y i i
          ∂replicatedNormalizedGUEMeasure N d) +
      (∫ y, (((lambda : ℂ) • (hermitianGUEBlock (N * d) y).1) *
        scaledFullGUEResolvent (deformationMatrix (replicatedSpectrum d f))
          lambda z y) i i ∂replicatedNormalizedGUEMeasure N d) = 1 := by
  let G := fun y : ReplicatedGUECoordinateSpace N d =>
    scaledFullGUEResolvent (deformationMatrix (replicatedSpectrum d f))
      lambda z y
  have hpoint (y : ReplicatedGUECoordinateSpace N d) :
      ((replicatedSpectrum d f i : ℂ) - z) * G y i i +
        (((lambda : ℂ) • (hermitianGUEBlock (N * d) y).1) * G y) i i = 1 := by
    have hPG := resolventPencil_mul_resolvent (replicatedSpectrum d f) lambda
      (hermitianGUEBlock (N * d) y).1
      (hermitianGUEBlock_isHermitian (N * d) y) hz
    change
      (resolventPencil (replicatedSpectrum d f) lambda
        (hermitianGUEBlock (N * d) y).1 z * G y) = 1 at hPG
    have hpencil : resolventPencil (replicatedSpectrum d f) lambda
        (hermitianGUEBlock (N * d) y).1 z =
      Matrix.diagonal (fun j => (replicatedSpectrum d f j : ℂ) - z) +
        (lambda : ℂ) • (hermitianGUEBlock (N * d) y).1 := by
      ext a b
      by_cases hab : a = b
      · subst b
        simp [resolventPencil, deformedMatrix, deformationMatrix]
        ring
      · simp [resolventPencil, deformedMatrix, deformationMatrix, hab]
    rw [hpencil, Matrix.add_mul] at hPG
    have hii := congrArg (fun M : Matrix (Fin (N * d)) (Fin (N * d)) ℂ => M i i) hPG
    simpa [Matrix.diagonal_mul] using hii
  have hG : Integrable (fun y => G y i i)
      (replicatedNormalizedGUEMeasure N d) := by
    rw [show replicatedNormalizedGUEMeasure N d =
      normalizedGUEMeasure (N * d) by rfl]
    simpa [G] using
      integrable_scaledFullGUEResolvent_entry
        (deformationMatrix (replicatedSpectrum d f))
        (deformationMatrix_isHermitian (replicatedSpectrum d f))
        lambda hz i i
  have hsource : Integrable (fun y =>
      (((lambda : ℂ) • (hermitianGUEBlock (N * d) y).1) * G y) i i)
      (replicatedNormalizedGUEMeasure N d) := by
    rw [show (fun y =>
        (((lambda : ℂ) • (hermitianGUEBlock (N * d) y).1) * G y) i i) =
      (fun y => 1 - ((replicatedSpectrum d f i : ℂ) - z) * G y i i) by
        funext y
        rw [← hpoint y]
        ring]
    exact (integrable_const (1 : ℂ)).sub
      (hG.const_mul ((replicatedSpectrum d f i : ℂ) - z))
  rw [← integral_const_mul]
  rw [← integral_add (hG.const_mul _) hsource]
  simp only [hpoint, integral_const]
  simp

/-- Expectation and normalized trace commute for the finite replicated matrix. -/
theorem replicatedExpectedTrace_eq_averageExpectedDiagonal
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    replicatedExpectedOneResolventTrace d f lambda z =
      CEHNative.BlockBand.CEH.average (fun i : Fin (N * d) =>
        ∫ y, scaledFullGUEResolvent
          (deformationMatrix (replicatedSpectrum d f)) lambda z y i i
          ∂replicatedNormalizedGUEMeasure N d) := by
  unfold replicatedExpectedOneResolventTrace replicatedOneResolventTrace
    NTrace CEHNative.BlockBand.Conventions.normalizedTrace
    CEHNative.BlockBand.CEH.average Matrix.trace
  rw [integral_const_mul]
  rw [integral_finsetSum Finset.univ]
  · simp only [Matrix.diag_apply]
    rw [div_eq_mul_inv]
    ring
  · intro i hi
    rw [show replicatedNormalizedGUEMeasure N d =
      normalizedGUEMeasure (N * d) by rfl]
    exact integrable_scaledFullGUEResolvent_entry
      (deformationMatrix (replicatedSpectrum d f))
      (deformationMatrix_isHermitian (replicatedSpectrum d f))
      lambda hz i i

/-- Scalar remainder obtained after solving the diagonal expectation equation
with the MDE pencil evaluated at the expected trace. -/
def replicatedOneResolventMDETraceRemainder {N : ℕ} (d : ℕ)
    (f : Spectrum N) (lambda : ℝ) (z : ℂ) : ℂ :=
  (lambda : ℂ) ^ 2 * CEHNative.BlockBand.CEH.average
    (fun i : Fin (N * d) =>
      CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f)
        (lambda ^ 2) z (replicatedExpectedOneResolventTrace d f lambda z) i *
      replicatedOneResolventCovarianceRemainder d f lambda z i i)

/-- Exact approximate scalar Dyson equation for the expected trace.  The only
error is the concrete covariance remainder already bounded by Poincare. -/
theorem replicatedExpectedTrace_approximateMDE
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : 0 < z.im)
    (hheight : lambda ^ 2 < z.im ^ 2) :
    replicatedExpectedOneResolventTrace d f lambda z =
      CEHNative.BlockBand.CEH.average
        (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f)
          (lambda ^ 2) z
          (replicatedExpectedOneResolventTrace d f lambda z)) +
      replicatedOneResolventMDETraceRemainder d f lambda z := by
  let m := replicatedExpectedOneResolventTrace d f lambda z
  let g := fun i : Fin (N * d) =>
    ∫ y, scaledFullGUEResolvent
      (deformationMatrix (replicatedSpectrum d f)) lambda z y i i
      ∂replicatedNormalizedGUEMeasure N d
  let r := fun i : Fin (N * d) =>
    replicatedOneResolventCovarianceRemainder d f lambda z i i
  have hh := effectiveHeight_expectedTrace_pos hN hd f lambda hz hheight
  have hentry (i : Fin (N * d)) :
      g i = CEHNative.BlockBand.CEH.entry
          (replicatedSpectrum d f) (lambda ^ 2) z m i +
        (lambda : ℂ) ^ 2 *
          CEHNative.BlockBand.CEH.entry
            (replicatedSpectrum d f) (lambda ^ 2) z m i * r i := by
    have hdiag := replicated_expected_resolvent_diagonal_equation
      f lambda hz.ne' i
    have hm := replicated_oneResolvent_centered_masterCancellation
      hN hd f lambda hz.ne' i i
    change ((replicatedSpectrum d f i : ℂ) - z) * g i + _ = 1 at hdiag
    change _ + (lambda : ℂ) ^ 2 * m * g i +
      (lambda : ℂ) ^ 2 * r i = 0 at hm
    have hcoef : (replicatedSpectrum d f i : ℂ) - z -
        ((lambda ^ 2 : ℝ) : ℂ) * m ≠ 0 :=
      CEHNative.BlockBand.CEH.denominator_ne_zero
        (replicatedSpectrum d f) hh i
    unfold CEHNative.BlockBand.CEH.entry
    push_cast at hcoef hm ⊢
    field_simp [hcoef]
    linear_combination hdiag - hm
  rw (occs := .pos [1])
    [replicatedExpectedTrace_eq_averageExpectedDiagonal f lambda hz.ne']
  change CEHNative.BlockBand.CEH.average g = _
  have hg : g = fun i =>
      CEHNative.BlockBand.CEH.entry
          (replicatedSpectrum d f) (lambda ^ 2) z m i +
        (lambda : ℂ) ^ 2 *
          CEHNative.BlockBand.CEH.entry
            (replicatedSpectrum d f) (lambda ^ 2) z m i * r i :=
    funext hentry
  rw [hg]
  unfold CEHNative.BlockBand.CEH.average
  rw [Finset.sum_add_distrib, add_div]
  unfold replicatedOneResolventMDETraceRemainder
  unfold CEHNative.BlockBand.CEH.average
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  dsimp only [m, r]
  ring

/-- Explicit lower bound for the effective height at the expected trace. -/
theorem expectedTrace_effectiveHeight_lower
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : 0 < z.im) :
    z.im - lambda ^ 2 * (z.im)⁻¹ ≤
      CEHNative.BlockBand.CEH.effectiveHeight (lambda ^ 2) z
        (replicatedExpectedOneResolventTrace d f lambda z) := by
  have hmnorm := norm_replicatedExpectedOneResolventTrace_le
    hN hd f lambda hz.ne'
  rw [abs_of_pos hz] at hmnorm
  have habs := Complex.abs_im_le_norm
    (replicatedExpectedOneResolventTrace d f lambda z)
  have him : -(z.im)⁻¹ ≤
      (replicatedExpectedOneResolventTrace d f lambda z).im :=
    (neg_le_neg hmnorm).trans (neg_le_of_abs_le habs)
  have hmul := mul_le_mul_of_nonneg_left him (sq_nonneg lambda)
  unfold CEHNative.BlockBand.CEH.effectiveHeight
  linarith

/-- Quantitative bound on the scalar MDE residual produced by the centered
master equation. -/
theorem norm_replicatedOneResolventMDETraceRemainder_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : 0 < z.im)
    (hheight : lambda ^ 2 < z.im ^ 2) :
    ‖replicatedOneResolventMDETraceRemainder d f lambda z‖ ≤
      lambda ^ 2 * (z.im - lambda ^ 2 * (z.im)⁻¹)⁻¹ * |z.im|⁻¹ *
        ((Real.pi ^ 2 / 2) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^ (1 / (2 : ℝ)) := by
  let h := z.im - lambda ^ 2 * (z.im)⁻¹
  let m := replicatedExpectedOneResolventTrace d f lambda z
  let a := fun i : Fin (N * d) =>
    CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f)
      (lambda ^ 2) z m i
  let r := fun i : Fin (N * d) =>
    replicatedOneResolventCovarianceRemainder d f lambda z i i
  have hh := effectiveHeight_expectedTrace_pos hN hd f lambda hz hheight
  have hlower := expectedTrace_effectiveHeight_lower hN hd f lambda hz
  have hh0 : 0 < h := by
    dsimp only [h]
    have hinv : z.im * (z.im)⁻¹ = 1 := mul_inv_cancel₀ hz.ne'
    nlinarith [hheight]
  have ha (i : Fin (N * d)) : ‖a i‖ ≤ h⁻¹ := by
    have he := CEHNative.BlockBand.CEH.norm_entry_le_inv_effectiveHeight
      (replicatedSpectrum d f) hh i
    apply he.trans
    simpa [one_div] using one_div_le_one_div_of_le hh0 hlower
  have hr (i : Fin (N * d)) : ‖r i‖ ≤ |z.im|⁻¹ *
      ((Real.pi ^ 2 / 2) * lambda ^ 2 *
        (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^ (1 / (2 : ℝ)) :=
    norm_replicatedOneResolventCovarianceRemainder_le hN hd f lambda hz.ne' i i
  unfold replicatedOneResolventMDETraceRemainder
  calc
    _ = lambda ^ 2 * ‖CEHNative.BlockBand.CEH.average
        (fun i : Fin (N * d) => a i * r i)‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real]
      simp only [Real.norm_eq_abs, sq_abs]
      rfl
    _ ≤ lambda ^ 2 * CEHNative.BlockBand.CEH.averageReal
        (fun i : Fin (N * d) => ‖a i * r i‖) := by
      gcongr
      exact CEHNative.BlockBand.CEH.norm_average_le
        (Nat.mul_pos hN hd) _
    _ ≤ lambda ^ 2 * (h⁻¹ * (|z.im|⁻¹ *
        ((Real.pi ^ 2 / 2) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^ (1 / (2 : ℝ)))) := by
      gcongr
      unfold CEHNative.BlockBand.CEH.averageReal
      apply (div_le_iff₀ (by exact_mod_cast Nat.mul_pos hN hd)).2
      calc
        ∑ i : Fin (N * d), ‖a i * r i‖ ≤
            ∑ _i : Fin (N * d), h⁻¹ * (|z.im|⁻¹ *
              ((Real.pi ^ 2 / 2) * lambda ^ 2 *
                (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^
                  (1 / (2 : ℝ))) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul]
          exact mul_le_mul (ha i) (hr i) (norm_nonneg _) (inv_nonneg.mpr hh0.le)
        _ = ((N * d : ℕ) : ℝ) * (h⁻¹ * (|z.im|⁻¹ *
              ((Real.pi ^ 2 / 2) * lambda ^ 2 *
                (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^
                  (1 / (2 : ℝ)))) := by simp
        _ = (h⁻¹ * (|z.im|⁻¹ *
              ((Real.pi ^ 2 / 2) * lambda ^ 2 *
                (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^
                  (1 / (2 : ℝ)))) * ((N * d : ℕ) : ℝ) := by ring
    _ = _ := by dsimp only [h]; ring

/-- Lipschitz estimate for the scalar Dyson map between two points of positive
effective height. -/
theorem norm_average_entry_sub_le
    {K : ℕ} (hK : 0 < K) (f : Spectrum K) {s : ℝ} (hs : 0 ≤ s)
    (z m₁ m₂ : ℂ)
    (hh₁ : 0 < CEHNative.BlockBand.CEH.effectiveHeight s z m₁)
    (hh₂ : 0 < CEHNative.BlockBand.CEH.effectiveHeight s z m₂) :
    ‖CEHNative.BlockBand.CEH.average
        (CEHNative.BlockBand.CEH.entry f s z m₁) -
      CEHNative.BlockBand.CEH.average
        (CEHNative.BlockBand.CEH.entry f s z m₂)‖ ≤
      s * (CEHNative.BlockBand.CEH.effectiveHeight s z m₁)⁻¹ *
        (CEHNative.BlockBand.CEH.effectiveHeight s z m₂)⁻¹ *
        ‖m₁ - m₂‖ := by
  let e₁ := CEHNative.BlockBand.CEH.entry f s z m₁
  let e₂ := CEHNative.BlockBand.CEH.entry f s z m₂
  have hdiff (i : Fin K) :
      e₁ i - e₂ i = (s : ℂ) * (m₁ - m₂) * e₁ i * e₂ i := by
    have hn₁ := CEHNative.BlockBand.CEH.denominator_ne_zero f hh₁ i
    have hn₂ := CEHNative.BlockBand.CEH.denominator_ne_zero f hh₂ i
    unfold e₁ e₂ CEHNative.BlockBand.CEH.entry
    field_simp [hn₁, hn₂]
    ring
  have he₁ (i : Fin K) :
      ‖e₁ i‖ ≤ (CEHNative.BlockBand.CEH.effectiveHeight s z m₁)⁻¹ :=
    CEHNative.BlockBand.CEH.norm_entry_le_inv_effectiveHeight f hh₁ i
  have he₂ (i : Fin K) :
      ‖e₂ i‖ ≤ (CEHNative.BlockBand.CEH.effectiveHeight s z m₂)⁻¹ :=
    CEHNative.BlockBand.CEH.norm_entry_le_inv_effectiveHeight f hh₂ i
  rw [show CEHNative.BlockBand.CEH.average e₁ -
      CEHNative.BlockBand.CEH.average e₂ =
      CEHNative.BlockBand.CEH.average (fun i => e₁ i - e₂ i) by
    unfold CEHNative.BlockBand.CEH.average
    rw [← sub_div, ← Finset.sum_sub_distrib]]
  calc
    _ ≤ CEHNative.BlockBand.CEH.averageReal
        (fun i => ‖e₁ i - e₂ i‖) :=
      CEHNative.BlockBand.CEH.norm_average_le hK _
    _ ≤ s * (CEHNative.BlockBand.CEH.effectiveHeight s z m₁)⁻¹ *
        (CEHNative.BlockBand.CEH.effectiveHeight s z m₂)⁻¹ *
        ‖m₁ - m₂‖ := by
      unfold CEHNative.BlockBand.CEH.averageReal
      apply (div_le_iff₀ (by exact_mod_cast hK)).2
      calc
        ∑ i : Fin K, ‖e₁ i - e₂ i‖ ≤
            ∑ _i : Fin K, s *
              (CEHNative.BlockBand.CEH.effectiveHeight s z m₁)⁻¹ *
              (CEHNative.BlockBand.CEH.effectiveHeight s z m₂)⁻¹ *
              ‖m₁ - m₂‖ := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hdiff i, norm_mul, norm_mul, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hs]
          calc
            s * ‖m₁ - m₂‖ * ‖e₁ i‖ * ‖e₂ i‖ ≤
                s * ‖m₁ - m₂‖ *
              (CEHNative.BlockBand.CEH.effectiveHeight s z m₁)⁻¹ *
                  (CEHNative.BlockBand.CEH.effectiveHeight s z m₂)⁻¹ := by
              gcongr
              · exact he₁ i
              · exact he₂ i
            _ = s *
                  (CEHNative.BlockBand.CEH.effectiveHeight s z m₁)⁻¹ *
                  (CEHNative.BlockBand.CEH.effectiveHeight s z m₂)⁻¹ *
                  ‖m₁ - m₂‖ := by ring
        _ = (K : ℝ) * (s *
              (CEHNative.BlockBand.CEH.effectiveHeight s z m₁)⁻¹ *
              (CEHNative.BlockBand.CEH.effectiveHeight s z m₂)⁻¹ *
              ‖m₁ - m₂‖) := by simp
        _ = (s *
              (CEHNative.BlockBand.CEH.effectiveHeight s z m₁)⁻¹ *
              (CEHNative.BlockBand.CEH.effectiveHeight s z m₂)⁻¹ *
              ‖m₁ - m₂‖) * (K : ℝ) := by ring

/-- Unconditional expectation-to-MDE bias estimate.  It holds on the
high-height contraction domain `2 * lambda^2 < (Im z)^2`; no spectral
grid or local-law assertion is made. -/
theorem norm_replicatedExpectedTrace_sub_upperBranch_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 < lambda)
    {z : ℂ} (hz : 0 < z.im) (hhigh : 2 * lambda ^ 2 < z.im ^ 2) :
    ‖replicatedExpectedOneResolventTrace d f lambda z -
      CEHNative.BlockBand.CEH.upperBranch hN f
        (sq_pos_of_pos hlambda) z‖ ≤
      (lambda ^ 2 * (z.im - lambda ^ 2 * (z.im)⁻¹)⁻¹ * |z.im|⁻¹ *
        ((Real.pi ^ 2 / 2) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^ (1 / (2 : ℝ))) /
      (1 - lambda ^ 2 * (z.im - lambda ^ 2 * (z.im)⁻¹)⁻¹ * (z.im)⁻¹) := by
  let s := lambda ^ 2
  let h := z.im - s * (z.im)⁻¹
  let m := replicatedExpectedOneResolventTrace d f lambda z
  let u := CEHNative.BlockBand.CEH.upperBranch
    (Nat.mul_pos hN hd) (replicatedSpectrum d f) (sq_pos_of_pos hlambda) z
  let R := replicatedOneResolventMDETraceRemainder d f lambda z
  let L := s * h⁻¹ * (z.im)⁻¹
  have hs : 0 < s := sq_pos_of_pos hlambda
  have hslt : s < z.im ^ 2 := by nlinarith
  have hh := effectiveHeight_expectedTrace_pos hN hd f lambda hz hslt
  have hh0 : 0 < h := by
    dsimp only [h, s]
    have hinv : z.im * (z.im)⁻¹ = 1 := mul_inv_cancel₀ hz.ne'
    nlinarith
  have huSol := CEHNative.BlockBand.CEH.upperBranch_isSolution
    (Nat.mul_pos hN hd) (replicatedSpectrum d f) hs hz
  have hhu : 0 < CEHNative.BlockBand.CEH.effectiveHeight s z u := by
    unfold CEHNative.BlockBand.CEH.effectiveHeight
    exact add_pos_of_pos_of_nonneg hz (mul_nonneg hs.le huSol.2.le)
  have hlower := expectedTrace_effectiveHeight_lower hN hd f lambda hz
  have hLip := norm_average_entry_sub_le (Nat.mul_pos hN hd)
    (replicatedSpectrum d f) hs.le z m u hh hhu
  have hhuLower : z.im ≤
      CEHNative.BlockBand.CEH.effectiveHeight s z u := by
    unfold CEHNative.BlockBand.CEH.effectiveHeight
    exact le_add_of_nonneg_right (mul_nonneg hs.le huSol.2.le)
  have hLip' :
      ‖CEHNative.BlockBand.CEH.average
          (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z m) -
        CEHNative.BlockBand.CEH.average
          (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z u)‖ ≤
        L * ‖m - u‖ := by
    apply hLip.trans
    have hInvM :
        (CEHNative.BlockBand.CEH.effectiveHeight s z m)⁻¹ ≤ h⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hh0 hlower
    have hInvU :
        (CEHNative.BlockBand.CEH.effectiveHeight s z u)⁻¹ ≤
          (z.im)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hz hhuLower
    dsimp only [L]
    gcongr
  have happrox := replicatedExpectedTrace_approximateMDE
    hN hd f lambda hz hslt
  have hfixed : u = CEHNative.BlockBand.CEH.average
      (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z u) :=
    huSol.1
  have hdist : ‖m - u‖ ≤ L * ‖m - u‖ + ‖R‖ := by
    calc
      ‖m - u‖ = ‖(CEHNative.BlockBand.CEH.average
          (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z m) -
        CEHNative.BlockBand.CEH.average
          (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z u)) + R‖ := by
            apply congrArg norm
            calc
              m - u = (CEHNative.BlockBand.CEH.average
                  (CEHNative.BlockBand.CEH.entry
                    (replicatedSpectrum d f) s z m) + R) - u := by
                exact congrArg (fun w : ℂ => w - u) happrox
              _ = (CEHNative.BlockBand.CEH.average
                  (CEHNative.BlockBand.CEH.entry
                    (replicatedSpectrum d f) s z m) + R) -
                  CEHNative.BlockBand.CEH.average
                    (CEHNative.BlockBand.CEH.entry
                      (replicatedSpectrum d f) s z u) :=
                congrArg (fun w : ℂ =>
                  (CEHNative.BlockBand.CEH.average
                    (CEHNative.BlockBand.CEH.entry
                      (replicatedSpectrum d f) s z m) + R) - w) hfixed
              _ = _ := by ring
      _ ≤ ‖CEHNative.BlockBand.CEH.average
          (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z m) -
        CEHNative.BlockBand.CEH.average
          (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z u)‖ + ‖R‖ :=
            norm_add_le _ _
      _ ≤ L * ‖m - u‖ + ‖R‖ := add_le_add hLip' le_rfl
  have hhprod : h * z.im = z.im ^ 2 - s := by
    dsimp only [h]
    have hinv : z.im * (z.im)⁻¹ = 1 := mul_inv_cancel₀ hz.ne'
    nlinarith
  have hL : L < 1 := by
    have hsprod : s < h * z.im := by
      rw [hhprod]
      dsimp only [s]
      nlinarith
    dsimp only [L]
    rw [show s * h⁻¹ * (z.im)⁻¹ = s / (h * z.im) by
      field_simp [hh0.ne', hz.ne']]
    exact (div_lt_one (mul_pos hh0 hz)).2 hsprod
  have hisolate : ‖m - u‖ ≤ ‖R‖ / (1 - L) := by
    apply (le_div_iff₀ (sub_pos.mpr hL)).2
    nlinarith
  have hR := norm_replicatedOneResolventMDETraceRemainder_le
    hN hd f lambda hz hslt
  have hrep : u = CEHNative.BlockBand.CEH.upperBranch hN f
      (sq_pos_of_pos hlambda) z := by
    dsimp only [u]
    unfold CEHNative.BlockBand.CEH.upperBranch
    simp only [dite_eq_left hz]
    exact replicated_upperSolution hN hd f (sq_pos_of_pos hlambda) z hz
  rw [← hrep]
  apply hisolate.trans
  apply div_le_div_of_nonneg_right hR (sub_nonneg.mpr hL.le)

end CEHNative.BlockBand.External.CEH
