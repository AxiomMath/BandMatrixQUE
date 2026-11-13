module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.OneResolventExpectationMDEStability

/-!
# Quantitative one-step vertical continuation for the expected resolvent

This module proves a deterministic, pointwise vertical propagation step.  It
compares two positive heights on one vertical line, transfers a verified small
branch at the upper height to the bootstrap region at the lower height, and
then invokes the nonlinear expectation–MDE stability estimate.  No grid
uniformity or local-law assertion is made.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal ENNReal
open PencilAdapter

/-- Resolvent difference identity when both the spectral parameter and scalar
self-energy vary. -/
theorem mdeEntry_sub_mdeEntry {K : ℕ} (f : Spectrum K) (s : ℝ)
    (z₁ m₁ z₂ m₂ : ℂ)
    (hh₁ : CEHNative.BlockBand.CEH.effectiveHeight s z₁ m₁ ≠ 0)
    (hh₂ : CEHNative.BlockBand.CEH.effectiveHeight s z₂ m₂ ≠ 0)
    (i : Fin K) :
    CEHNative.BlockBand.CEH.entry f s z₁ m₁ i -
        CEHNative.BlockBand.CEH.entry f s z₂ m₂ i =
      (z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) *
        CEHNative.BlockBand.CEH.entry f s z₁ m₁ i *
        CEHNative.BlockBand.CEH.entry f s z₂ m₂ i := by
  have h₁ := CEHNative.BlockBand.CEH.denominator_ne_zero_of_height_ne
    f hh₁ i
  have h₂ := CEHNative.BlockBand.CEH.denominator_ne_zero_of_height_ne
    f hh₂ i
  unfold CEHNative.BlockBand.CEH.entry
  rw [inv_sub_inv' h₁ h₂]
  ring

/-- Exact two-height stability identity for the upper MDE branch. -/
theorem upperBranch_twoParameter_difference_identity {K : ℕ} (hK : 0 < K)
    (f : Spectrum K) {s : ℝ} (hs : 0 < s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    CEHNative.BlockBand.CEH.fourAdjointDenominator false false f s
        z₁ (CEHNative.BlockBand.CEH.upperBranch hK f hs z₁)
        z₂ (CEHNative.BlockBand.CEH.upperBranch hK f hs z₂) *
      (CEHNative.BlockBand.CEH.upperBranch hK f hs z₁ -
        CEHNative.BlockBand.CEH.upperBranch hK f hs z₂) =
    (z₁ - z₂) * CEHNative.BlockBand.CEH.average (fun i =>
      CEHNative.BlockBand.CEH.entry f s z₁
          (CEHNative.BlockBand.CEH.upperBranch hK f hs z₁) i *
        CEHNative.BlockBand.CEH.entry f s z₂
          (CEHNative.BlockBand.CEH.upperBranch hK f hs z₂) i) := by
  let u₁ := CEHNative.BlockBand.CEH.upperBranch hK f hs z₁
  let u₂ := CEHNative.BlockBand.CEH.upperBranch hK f hs z₂
  have hu₁ := CEHNative.BlockBand.CEH.upperBranch_isSolution hK f hs hz₁
  have hu₂ := CEHNative.BlockBand.CEH.upperBranch_isSolution hK f hs hz₂
  change CEHNative.BlockBand.CEH.IsSolution f s z₁ u₁ at hu₁
  change CEHNative.BlockBand.CEH.IsSolution f s z₂ u₂ at hu₂
  have hh₁ : CEHNative.BlockBand.CEH.effectiveHeight s z₁ u₁ ≠ 0 := by
    unfold CEHNative.BlockBand.CEH.effectiveHeight
    nlinarith [hu₁.2]
  have hh₂ : CEHNative.BlockBand.CEH.effectiveHeight s z₂ u₂ ≠ 0 := by
    unfold CEHNative.BlockBand.CEH.effectiveHeight
    nlinarith [hu₂.2]
  have hd : u₁ - u₂ = CEHNative.BlockBand.CEH.average (fun i =>
      (z₁ - z₂ + (s : ℂ) * (u₁ - u₂)) *
        CEHNative.BlockBand.CEH.entry f s z₁ u₁ i *
        CEHNative.BlockBand.CEH.entry f s z₂ u₂ i) := by
    calc
      u₁ - u₂ =
          CEHNative.BlockBand.CEH.average
              (CEHNative.BlockBand.CEH.entry f s z₁ u₁) -
            CEHNative.BlockBand.CEH.average
              (CEHNative.BlockBand.CEH.entry f s z₂ u₂) :=
        congrArg₂ (· - ·) hu₁.1 hu₂.1
      _ = CEHNative.BlockBand.CEH.average (fun i =>
          CEHNative.BlockBand.CEH.entry f s z₁ u₁ i -
            CEHNative.BlockBand.CEH.entry f s z₂ u₂ i) := by
        unfold CEHNative.BlockBand.CEH.average
        rw [Finset.sum_sub_distrib]
        ring
      _ = _ := by
        congr 1
        funext i
        exact mdeEntry_sub_mdeEntry f s z₁ u₁ z₂ u₂ hh₁ hh₂ i
  have hfactor : CEHNative.BlockBand.CEH.average (fun i =>
      (z₁ - z₂ + (s : ℂ) * (u₁ - u₂)) *
        CEHNative.BlockBand.CEH.entry f s z₁ u₁ i *
        CEHNative.BlockBand.CEH.entry f s z₂ u₂ i) =
      (z₁ - z₂ + (s : ℂ) * (u₁ - u₂)) *
        CEHNative.BlockBand.CEH.average (fun i =>
          CEHNative.BlockBand.CEH.entry f s z₁ u₁ i *
          CEHNative.BlockBand.CEH.entry f s z₂ u₂ i) := by
    simpa only [mul_assoc] using
      (CEHNative.BlockBand.CEH.average_const_mul
        (z₁ - z₂ + (s : ℂ) * (u₁ - u₂)) (fun i =>
          CEHNative.BlockBand.CEH.entry f s z₁ u₁ i *
          CEHNative.BlockBand.CEH.entry f s z₂ u₂ i))

  dsimp only [u₁, u₂] at hd hfactor ⊢
  simp only [CEHNative.BlockBand.CEH.fourAdjointDenominator,
    CEHNative.BlockBand.CEH.adjointedEntry, Bool.false_eq_true,
    ↓reduceIte]
  have hd' := hd.trans hfactor
  linear_combination hd'

/-- Explicit two-height continuity modulus for the upper MDE branch. -/
theorem norm_upperBranch_sub_upperBranch_le {K : ℕ} (hK : 0 < K)
    (f : Spectrum K) {s : ℝ} (hs : 0 < s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    ‖CEHNative.BlockBand.CEH.upperBranch hK f hs z₁ -
      CEHNative.BlockBand.CEH.upperBranch hK f hs z₂‖ ≤
    ‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹ *
      (1 + (Real.pi * s / 2) *
        (CEHNative.BlockBand.CEH.density
              (CEHNative.BlockBand.CEH.upperBranch hK f hs z₁) / z₁.im +
          CEHNative.BlockBand.CEH.density
              (CEHNative.BlockBand.CEH.upperBranch hK f hs z₂) / z₂.im)) := by
  let u₁ := CEHNative.BlockBand.CEH.upperBranch hK f hs z₁
  let u₂ := CEHNative.BlockBand.CEH.upperBranch hK f hs z₂
  let A := CEHNative.BlockBand.CEH.average (fun i =>
    CEHNative.BlockBand.CEH.entry f s z₁ u₁ i *
      CEHNative.BlockBand.CEH.entry f s z₂ u₂ i)
  let D := CEHNative.BlockBand.CEH.fourAdjointDenominator false false
    f s z₁ u₁ z₂ u₂
  have hu₁ := CEHNative.BlockBand.CEH.upperBranch_isSolution hK f hs hz₁
  have hu₂ := CEHNative.BlockBand.CEH.upperBranch_isSolution hK f hs hz₂
  change CEHNative.BlockBand.CEH.IsSolution f s z₁ u₁ at hu₁
  change CEHNative.BlockBand.CEH.IsSolution f s z₂ u₂ at hu₂
  have hh₁ : z₁.im ≤ CEHNative.BlockBand.CEH.effectiveHeight s z₁ u₁ := by
    unfold CEHNative.BlockBand.CEH.effectiveHeight
    exact le_add_of_nonneg_right (mul_nonneg hs.le hu₁.2.le)
  have hh₂ : z₂.im ≤ CEHNative.BlockBand.CEH.effectiveHeight s z₂ u₂ := by
    unfold CEHNative.BlockBand.CEH.effectiveHeight
    exact le_add_of_nonneg_right (mul_nonneg hs.le hu₂.2.le)
  have hA : ‖A‖ ≤ (z₁.im)⁻¹ * (z₂.im)⁻¹ := by
    apply (CEHNative.BlockBand.CEH.norm_average_le hK _).trans
    unfold CEHNative.BlockBand.CEH.averageReal
    apply (div_le_iff₀ (by exact_mod_cast hK)).2
    calc
      ∑ i : Fin K, ‖CEHNative.BlockBand.CEH.entry f s z₁ u₁ i *
          CEHNative.BlockBand.CEH.entry f s z₂ u₂ i‖ ≤
          ∑ _i : Fin K, (z₁.im)⁻¹ * (z₂.im)⁻¹ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        apply mul_le_mul
        · apply (CEHNative.BlockBand.CEH.norm_entry_le_inv_effectiveHeight
            f (lt_of_lt_of_le hz₁ hh₁) i).trans
          simpa [one_div] using one_div_le_one_div_of_le hz₁ hh₁
        · apply (CEHNative.BlockBand.CEH.norm_entry_le_inv_effectiveHeight
            f (lt_of_lt_of_le hz₂ hh₂) i).trans
          simpa [one_div] using one_div_le_one_div_of_le hz₂ hh₂
        · positivity
        · positivity
      _ = (K : ℝ) * ((z₁.im)⁻¹ * (z₂.im)⁻¹) := by simp
      _ = ((z₁.im)⁻¹ * (z₂.im)⁻¹) * (K : ℝ) := by ring
  have hD : D ≠ 0 := by
    have hlt := CEHNative.BlockBand.CEH.mixed_average_norm_lt_inv
      hK f hs hz₁ hz₂ hu₁ hu₂ false
    simp only [Bool.false_eq_true, ↓reduceIte] at hlt
    intro hzero
    have heq : (s : ℂ) * A = 1 := by
      dsimp only [D, A, u₁, u₂] at hzero ⊢
      simpa [CEHNative.BlockBand.CEH.fourAdjointDenominator,
        CEHNative.BlockBand.CEH.adjointedEntry] using
          (sub_eq_zero.mp hzero).symm
    have hn := congrArg norm heq
    simp at hn
    rw [abs_of_pos hs] at hn
    nlinarith
  have hid : D * (u₁ - u₂) = (z₁ - z₂) * A := by
    dsimp only [D, A, u₁, u₂]
    exact upperBranch_twoParameter_difference_identity hK f hs hz₁ hz₂
  have hsolve : u₁ - u₂ = D⁻¹ * ((z₁ - z₂) * A) := by
    calc
      u₁ - u₂ = 1 * (u₁ - u₂) := by simp
      _ = (D⁻¹ * D) * (u₁ - u₂) := by rw [inv_mul_cancel₀ hD]
      _ = D⁻¹ * (D * (u₁ - u₂)) := by ring
      _ = D⁻¹ * ((z₁ - z₂) * A) := by rw [hid]
  have hDinv := CEHNative.BlockBand.CEH.upperBranch_fourAdjoint_inverse_ceh_bound
    hK false false f hs hz₁ hz₂
  change ‖D⁻¹‖ ≤ 1 + (Real.pi * s / 2) *
    (CEHNative.BlockBand.CEH.density u₁ / z₁.im +
      CEHNative.BlockBand.CEH.density u₂ / z₂.im) at hDinv
  have hρ₁ : 0 ≤ CEHNative.BlockBand.CEH.density u₁ := by
    exact div_nonneg hu₁.2.le Real.pi_pos.le
  have hρ₂ : 0 ≤ CEHNative.BlockBand.CEH.density u₂ := by
    exact div_nonneg hu₂.2.le Real.pi_pos.le
  rw [hsolve, norm_mul, norm_mul]
  calc
    ‖D⁻¹‖ * (‖z₁ - z₂‖ * ‖A‖) ≤
        (1 + (Real.pi * s / 2) *
          (CEHNative.BlockBand.CEH.density u₁ / z₁.im +
            CEHNative.BlockBand.CEH.density u₂ / z₂.im)) *
          (‖z₁ - z₂‖ * ((z₁.im)⁻¹ * (z₂.im)⁻¹)) := by
      gcongr
    _ = _ := by
      dsimp only [u₁, u₂]
      ring

/-- Spectral-average representation of each concrete replicated resolvent trace. -/
theorem replicatedOneResolventTrace_eq_spectralAverage
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : 0 < z.im)
    (y : ReplicatedGUECoordinateSpace N d) :
    replicatedOneResolventTrace d f lambda z y =
      CEHNative.BlockBand.CEH.average
        (CEHNative.BlockBand.CEH.entry
          (CEHNative.BlockBand.CEH.hermitianSpectrum
            (deformedMatrix_isHermitian (replicatedSpectrum d f) lambda
              (hermitianGUEBlock (N * d) y).1
              (hermitianGUEBlock_isHermitian (N * d) y))) 0 z 0) := by
  let K := N * d
  let H := deformedMatrix (replicatedSpectrum d f) lambda
    (hermitianGUEBlock K y).1
  have hK : 0 < K := Nat.mul_pos hN hd
  let _ : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have hH : H.IsHermitian := deformedMatrix_isHermitian _ _ _
    (hermitianGUEBlock_isHermitian K y)
  let M := CEHNative.BlockBand.CEH.spectralLift hH
    (CEHNative.BlockBand.CEH.entry
      (CEHNative.BlockBand.CEH.hermitianSpectrum hH) 0 z 0)
  have hh : CEHNative.BlockBand.CEH.effectiveHeight 0 z 0 ≠ 0 := by
    simp [CEHNative.BlockBand.CEH.effectiveHeight, hz.ne']
  have hM : (H - z • (1 : Matrix (Fin K) (Fin K) ℂ)) * M = 1 := by
    simpa [M] using CEHNative.BlockBand.CEH.spectralLift_entry_inverse
      hH 0 z 0 hh
  have hG : (H - z • (1 : Matrix (Fin K) (Fin K) ℂ)) *
      scaledFullGUEResolvent (deformationMatrix (replicatedSpectrum d f))
        lambda z y = 1 := by
    simpa [H, scaledFullGUEResolvent_deformationMatrix, resolventPencil,
      deformedMatrix] using resolventPencil_mul_resolvent
        (replicatedSpectrum d f) lambda (hermitianGUEBlock K y).1
        (hermitianGUEBlock_isHermitian K y) hz.ne'
  have hGM : scaledFullGUEResolvent
      (deformationMatrix (replicatedSpectrum d f)) lambda z y = M :=
    Matrix.right_inv_eq_right_inv hG hM
  rw [replicatedOneResolventTrace, hGM]
  simpa [M, H] using
    (CEHNative.BlockBand.CEH.normalizedTrace_spectralLift hH
      (CEHNative.BlockBand.CEH.entry
        (CEHNative.BlockBand.CEH.hermitianSpectrum hH) 0 z 0))

/-- Dimension-free pointwise resolvent-trace continuity between two upper
half-plane parameters. -/
theorem norm_replicatedOneResolventTrace_sub_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z₁ z₂ : ℂ}
    (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (y : ReplicatedGUECoordinateSpace N d) :
    ‖replicatedOneResolventTrace d f lambda z₁ y -
      replicatedOneResolventTrace d f lambda z₂ y‖ ≤
      ‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹ := by
  let H := deformedMatrix (replicatedSpectrum d f) lambda
    (hermitianGUEBlock (N * d) y).1
  let hH : H.IsHermitian := deformedMatrix_isHermitian _ _ _
    (hermitianGUEBlock_isHermitian (N * d) y)
  let e := CEHNative.BlockBand.CEH.hermitianSpectrum hH
  rw [replicatedOneResolventTrace_eq_spectralAverage hN hd f lambda hz₁ y,
    replicatedOneResolventTrace_eq_spectralAverage hN hd f lambda hz₂ y]
  change ‖CEHNative.BlockBand.CEH.average
      (CEHNative.BlockBand.CEH.entry e 0 z₁ 0) -
    CEHNative.BlockBand.CEH.average
      (CEHNative.BlockBand.CEH.entry e 0 z₂ 0)‖ ≤ _
  calc
    _ = ‖CEHNative.BlockBand.CEH.average (fun i =>
        CEHNative.BlockBand.CEH.entry e 0 z₁ 0 i -
          CEHNative.BlockBand.CEH.entry e 0 z₂ 0 i)‖ := by
      unfold CEHNative.BlockBand.CEH.average
      rw [← sub_div, ← Finset.sum_sub_distrib]
    _ ≤ CEHNative.BlockBand.CEH.averageReal (fun i =>
        ‖CEHNative.BlockBand.CEH.entry e 0 z₁ 0 i -
          CEHNative.BlockBand.CEH.entry e 0 z₂ 0 i‖) :=
      CEHNative.BlockBand.CEH.norm_average_le (Nat.mul_pos hN hd) _
    _ ≤ ‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹ := by
      unfold CEHNative.BlockBand.CEH.averageReal
      apply (div_le_iff₀ (by exact_mod_cast Nat.mul_pos hN hd)).2
      calc
        ∑ i : Fin (N * d),
            ‖CEHNative.BlockBand.CEH.entry e 0 z₁ 0 i -
              CEHNative.BlockBand.CEH.entry e 0 z₂ 0 i‖ ≤
            ∑ _i : Fin (N * d), ‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹ := by
          apply Finset.sum_le_sum
          intro i hi
          rw [mdeEntry_sub_mdeEntry e 0 z₁ 0 z₂ 0 (by
            simpa [CEHNative.BlockBand.CEH.effectiveHeight] using hz₁.ne') (by
            simpa [CEHNative.BlockBand.CEH.effectiveHeight] using hz₂.ne') i]
          simp only [Complex.ofReal_zero, zero_mul, add_zero, norm_mul]
          calc
            ‖z₁ - z₂‖ * ‖CEHNative.BlockBand.CEH.entry e 0 z₁ 0 i‖ *
                ‖CEHNative.BlockBand.CEH.entry e 0 z₂ 0 i‖ =
              ‖z₁ - z₂‖ *
                (‖CEHNative.BlockBand.CEH.entry e 0 z₁ 0 i‖ *
                  ‖CEHNative.BlockBand.CEH.entry e 0 z₂ 0 i‖) := by ring
            _ ≤ ‖z₁ - z₂‖ * ((z₁.im)⁻¹ * (z₂.im)⁻¹) := by
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              apply mul_le_mul
              · simpa [CEHNative.BlockBand.CEH.effectiveHeight] using
                  (CEHNative.BlockBand.CEH.norm_entry_le_inv_effectiveHeight
                    e (s := 0) (z := z₁) (m := 0)
                      (by simpa [CEHNative.BlockBand.CEH.effectiveHeight] using hz₁) i)
              · simpa [CEHNative.BlockBand.CEH.effectiveHeight] using
                  (CEHNative.BlockBand.CEH.norm_entry_le_inv_effectiveHeight
                    e (s := 0) (z := z₂) (m := 0)
                      (by simpa [CEHNative.BlockBand.CEH.effectiveHeight] using hz₂) i)
              · positivity
              · positivity
            _ = ‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹ := by ring
        _ = ((N * d : ℕ) : ℝ) *
            (‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹) := by simp
        _ = (‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹) *
            ((N * d : ℕ) : ℝ) := by ring

/-- Dimension-free continuity of the expected normalized trace. -/
theorem norm_replicatedExpectedOneResolventTrace_sub_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z₁ z₂ : ℂ}
    (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    ‖replicatedExpectedOneResolventTrace d f lambda z₁ -
      replicatedExpectedOneResolventTrace d f lambda z₂‖ ≤
      ‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹ := by
  have h₁ := integrable_replicatedOneResolventTrace (d := d) f lambda hz₁.ne'
  have h₂ := integrable_replicatedOneResolventTrace (d := d) f lambda hz₂.ne'
  unfold replicatedExpectedOneResolventTrace
  rw [← integral_sub h₁ h₂]
  calc
    ‖∫ y, (replicatedOneResolventTrace d f lambda z₁ y -
        replicatedOneResolventTrace d f lambda z₂ y)
        ∂replicatedNormalizedGUEMeasure N d‖ ≤
      ∫ _y, ‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹
        ∂replicatedNormalizedGUEMeasure N d := by
      apply norm_integral_le_of_norm_le
        (integrable_const (‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹))
      exact ae_of_all _ (norm_replicatedOneResolventTrace_sub_le
        hN hd f lambda hz₁ hz₂)
    _ = _ := by simp

/-- The expectation–MDE error at a second point is controlled by its value at
the first point and the two explicit continuity moduli. -/
theorem norm_expectationMDEError_step_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 < lambda)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    ‖replicatedExpectedOneResolventTrace d f lambda z₂ -
      CEHNative.BlockBand.CEH.upperBranch (Nat.mul_pos hN hd)
        (replicatedSpectrum d f) (sq_pos_of_pos hlambda) z₂‖ ≤
    ‖replicatedExpectedOneResolventTrace d f lambda z₁ -
      CEHNative.BlockBand.CEH.upperBranch (Nat.mul_pos hN hd)
        (replicatedSpectrum d f) (sq_pos_of_pos hlambda) z₁‖ +
    ‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹ +
    ‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹ *
      (1 + (Real.pi * lambda ^ 2 / 2) *
        (CEHNative.BlockBand.CEH.density
              (CEHNative.BlockBand.CEH.upperBranch
                (Nat.mul_pos hN hd) (replicatedSpectrum d f)
                  (sq_pos_of_pos hlambda) z₁) / z₁.im +
          CEHNative.BlockBand.CEH.density
              (CEHNative.BlockBand.CEH.upperBranch
                (Nat.mul_pos hN hd) (replicatedSpectrum d f)
                  (sq_pos_of_pos hlambda) z₂) / z₂.im)) := by
  let m₁ := replicatedExpectedOneResolventTrace d f lambda z₁
  let m₂ := replicatedExpectedOneResolventTrace d f lambda z₂
  let u₁ := CEHNative.BlockBand.CEH.upperBranch (Nat.mul_pos hN hd)
    (replicatedSpectrum d f) (sq_pos_of_pos hlambda) z₁
  let u₂ := CEHNative.BlockBand.CEH.upperBranch (Nat.mul_pos hN hd)
    (replicatedSpectrum d f) (sq_pos_of_pos hlambda) z₂
  have hm := norm_replicatedExpectedOneResolventTrace_sub_le
    hN hd f lambda hz₂ hz₁
  have hm' : ‖m₂ - m₁‖ ≤ ‖z₁ - z₂‖ * (z₁.im)⁻¹ * (z₂.im)⁻¹ := by
    dsimp only [m₁, m₂]
    calc
      _ ≤ ‖z₂ - z₁‖ * (z₂.im)⁻¹ * (z₁.im)⁻¹ := hm
      _ = _ := by rw [norm_sub_rev z₂ z₁]; ring
  have hu := norm_upperBranch_sub_upperBranch_le (Nat.mul_pos hN hd)
    (replicatedSpectrum d f) (sq_pos_of_pos hlambda) hz₁ hz₂
  change ‖m₂ - u₂‖ ≤ _
  calc
    ‖m₂ - u₂‖ = ‖(m₁ - u₁) + (m₂ - m₁) + (u₁ - u₂)‖ := by ring_nf
    _ ≤ ‖m₁ - u₁‖ + ‖m₂ - m₁‖ + ‖u₁ - u₂‖ := by
      calc
        _ ≤ ‖(m₁ - u₁) + (m₂ - m₁)‖ + ‖u₁ - u₂‖ := norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by
      dsimp only [m₁, m₂, u₁, u₂] at hm' hu ⊢
      gcongr

/-- Explicit error envelope transported in one downward vertical step.  The
first term is the already controlled upper-height error; the next two are the
random-resolvent and MDE-branch continuity costs. -/
def oneResolventVerticalStepControl {N : ℕ} (d : ℕ) (f : Spectrum N)
    (lambda E etaHigh etaLow : ℝ) (hN : 0 < N) (hd : 0 < d)
    (hlambda : 0 < lambda) : ℝ :=
  ‖replicatedExpectedOneResolventTrace d f lambda (plusParameter E etaHigh) -
    CEHNative.BlockBand.CEH.upperBranch (Nat.mul_pos hN hd)
      (replicatedSpectrum d f) (sq_pos_of_pos hlambda)
        (plusParameter E etaHigh)‖ +
  (etaHigh - etaLow) * etaHigh⁻¹ * etaLow⁻¹ +
  (etaHigh - etaLow) * etaHigh⁻¹ * etaLow⁻¹ *
    (1 + (Real.pi * lambda ^ 2 / 2) *
      (CEHNative.BlockBand.CEH.density
            (CEHNative.BlockBand.CEH.upperBranch
              (Nat.mul_pos hN hd) (replicatedSpectrum d f)
                (sq_pos_of_pos hlambda) (plusParameter E etaHigh)) / etaHigh +
        CEHNative.BlockBand.CEH.density
            (CEHNative.BlockBand.CEH.upperBranch
              (Nat.mul_pos hN hd) (replicatedSpectrum d f)
                (sq_pos_of_pos hlambda) (plusParameter E etaLow)) / etaLow))

/-- A quantitative one-step continuation theorem.  If the explicit vertical
continuity envelope fits inside the lower-height nonlinear stability radius,
then the lower point lies on the small branch and obeys the Gaussian bias
bound.  This is pointwise and deterministic; it does not iterate a grid. -/
theorem norm_replicatedExpectedTrace_sub_upperBranch_vertical_step_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 < lambda)
    (E etaHigh etaLow : ℝ) (hetaLow : 0 < etaLow)
    (hetaOrder : etaLow ≤ etaHigh)
    (hstep :
      2 * (lambda ^ 2) ^ 2 * etaLow⁻¹ ^ 3 *
          oneResolventVerticalStepControl d f lambda E etaHigh etaLow
            hN hd hlambda ≤
        etaLow / (etaLow + lambda ^ 2 * (Real.pi *
          CEHNative.BlockBand.CEH.density
            (CEHNative.BlockBand.CEH.upperBranch
              (Nat.mul_pos hN hd) (replicatedSpectrum d f)
                (sq_pos_of_pos hlambda) (plusParameter E etaLow)))) +
        2 * Real.pi ^ 2 * lambda ^ 2 *
          CEHNative.BlockBand.CEH.density
            (CEHNative.BlockBand.CEH.upperBranch
              (Nat.mul_pos hN hd) (replicatedSpectrum d f)
                (sq_pos_of_pos hlambda) (plusParameter E etaLow)) ^ 2) :
    ‖replicatedExpectedOneResolventTrace d f lambda (plusParameter E etaLow) -
      CEHNative.BlockBand.CEH.upperBranch hN f
        (sq_pos_of_pos hlambda) (plusParameter E etaLow)‖ ≤
      (2 * (lambda ^ 2 * etaLow⁻¹ * |etaLow|⁻¹ *
        ((Real.pi ^ 2 / 2) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |etaLow|⁻¹ ^ 4) ^ (1 / (2 : ℝ)))) /
        ‖CEHNative.BlockBand.CEH.stabilityDenominator
          (replicatedSpectrum d f) (lambda ^ 2) (plusParameter E etaLow)
          (CEHNative.BlockBand.CEH.upperBranch
            (Nat.mul_pos hN hd) (replicatedSpectrum d f)
              (sq_pos_of_pos hlambda) (plusParameter E etaLow))‖ := by
  have hetaHigh : 0 < etaHigh := lt_of_lt_of_le hetaLow hetaOrder
  let zHigh := plusParameter E etaHigh
  let zLow := plusParameter E etaLow
  let uLow := CEHNative.BlockBand.CEH.upperBranch
    (Nat.mul_pos hN hd) (replicatedSpectrum d f) (sq_pos_of_pos hlambda) zLow
  have hzHigh : 0 < zHigh.im := by simpa [zHigh, plusParameter] using hetaHigh
  have hzLow : 0 < zLow.im := by simpa [zLow, plusParameter] using hetaLow
  have herr := norm_expectationMDEError_step_le hN hd f lambda hlambda hzHigh hzLow
  have hdist : ‖zHigh - zLow‖ = etaHigh - etaLow := by
    have heq : zHigh - zLow = Complex.I * ((etaHigh - etaLow : ℝ) : ℂ) := by
      dsimp only [zHigh, zLow, plusParameter]
      push_cast
      ring
    rw [heq, norm_mul]
    rw [Complex.norm_I, one_mul, Complex.norm_real]
    exact abs_of_nonneg (sub_nonneg.mpr hetaOrder)

  have herr' :
      ‖replicatedExpectedOneResolventTrace d f lambda zLow - uLow‖ ≤
        oneResolventVerticalStepControl d f lambda E etaHigh etaLow
          hN hd hlambda := by
    rw [hdist] at herr
    simpa [oneResolventVerticalStepControl, zHigh, zLow, uLow,
      plusParameter] using herr
  have hscale : 0 ≤ 2 * (lambda ^ 2) ^ 2 * etaLow⁻¹ ^ 3 := by positivity
  have htransport :
      2 * (lambda ^ 2) ^ 2 * etaLow⁻¹ ^ 3 *
          ‖replicatedExpectedOneResolventTrace d f lambda zLow - uLow‖ ≤
        etaLow / (etaLow + lambda ^ 2 * (Real.pi *
          CEHNative.BlockBand.CEH.density uLow)) +
        2 * Real.pi ^ 2 * lambda ^ 2 *
          CEHNative.BlockBand.CEH.density uLow ^ 2 := by
    apply (mul_le_mul_of_nonneg_left herr' hscale).trans
    simpa [zLow, uLow] using hstep
  have hden := CEHNative.BlockBand.CEH.upperBranch_stability_full_ceh_bound
    (Nat.mul_pos hN hd) (replicatedSpectrum d f) (sq_pos_of_pos hlambda) hzLow
  have hbootstrap :
      2 * (lambda ^ 2) ^ 2 * (zLow.im)⁻¹ ^ 3 *
          ‖replicatedExpectedOneResolventTrace d f lambda zLow - uLow‖ ≤
        ‖CEHNative.BlockBand.CEH.stabilityDenominator
          (replicatedSpectrum d f) (lambda ^ 2) zLow uLow‖ := by
    have him : zLow.im = etaLow := by simp [zLow, plusParameter]
    rw [him]
    apply htransport.trans
    simpa [zLow, uLow, plusParameter] using hden
  have hfinal := norm_replicatedExpectedTrace_sub_upperBranch_stability_step
    hN hd f lambda hlambda hzLow hbootstrap
  simpa [zLow, plusParameter] using hfinal

end CEHNative.BlockBand.External.CEH
