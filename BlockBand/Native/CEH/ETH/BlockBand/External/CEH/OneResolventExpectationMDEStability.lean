module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.OneResolventExpectationMDEBias

/-!
# Imaginary Ward sign and nonlinear MDE stability checkpoint

This module proves the upper-half-plane sign of the concrete expected
one-resolvent trace and records the exact nonlinear stability equation around
the CEH upper branch.  The final estimate is a bootstrap/continuation step,
not a closed local law or a grid-uniform statement.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal ENNReal
open PencilAdapter

/-- Every concrete replicated resolvent trace has positive imaginary part in
the upper half-plane. -/
theorem replicatedOneResolventTrace_im_pos
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : 0 < z.im)
    (y : ReplicatedGUECoordinateSpace N d) :
    0 < (replicatedOneResolventTrace d f lambda z y).im := by
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
  rw [show NTrace M = CEHNative.BlockBand.CEH.average
      (CEHNative.BlockBand.CEH.entry
        (CEHNative.BlockBand.CEH.hermitianSpectrum hH) 0 z 0) by
    exact CEHNative.BlockBand.CEH.normalizedTrace_spectralLift hH _]
  rw [CEHNative.BlockBand.CEH.average_im hK]
  unfold CEHNative.BlockBand.CEH.averageReal
  apply div_pos
  · apply Finset.sum_pos
    · intro i hi
      apply CEHNative.BlockBand.CEH.entry_im_pos
      simp [CEHNative.BlockBand.CEH.effectiveHeight, hz]
    · exact Finset.univ_nonempty
  · exact_mod_cast hK

/-- Hence the expected trace has nonnegative imaginary part. -/
theorem replicatedExpectedOneResolventTrace_im_nonneg
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (replicatedExpectedOneResolventTrace d f lambda z).im := by
  have hg := integrable_replicatedOneResolventTrace (d := d) f lambda hz.ne'
  unfold replicatedExpectedOneResolventTrace
  have hi : 0 ≤ ∫ y, (replicatedOneResolventTrace d f lambda z y).im
      ∂replicatedNormalizedGUEMeasure N d := integral_nonneg fun y =>
    (replicatedOneResolventTrace_im_pos hN hd f lambda hz y).le
  change 0 ≤ ∫ y, RCLike.im (replicatedOneResolventTrace d f lambda z y)
    ∂replicatedNormalizedGUEMeasure N d at hi
  change 0 ≤ RCLike.im (∫ y, replicatedOneResolventTrace d f lambda z y
    ∂replicatedNormalizedGUEMeasure N d)
  rwa [← integral_im hg]

/-- The expected-trace MDE pencil has at least the original spectral height. -/
theorem expectedTrace_effectiveHeight_ge_im
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : 0 < z.im) :
    z.im ≤ CEHNative.BlockBand.CEH.effectiveHeight (lambda ^ 2) z
      (replicatedExpectedOneResolventTrace d f lambda z) := by
  unfold CEHNative.BlockBand.CEH.effectiveHeight
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg lambda)
    (replicatedExpectedOneResolventTrace_im_nonneg hN hd f lambda hz))

/-- The exact approximate scalar Dyson equation now holds throughout the upper
half-plane, because the imaginary Ward sign makes the expected-trace pencil
invertible without a high-height assumption. -/
theorem replicatedExpectedTrace_approximateMDE_upper
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : 0 < z.im) :
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
  have hh : 0 < CEHNative.BlockBand.CEH.effectiveHeight
      (lambda ^ 2) z m := lt_of_lt_of_le hz
    (expectedTrace_effectiveHeight_ge_im hN hd f lambda hz)
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

/-- The scalar MDE residual has the sharper Ward-sign bound throughout the
upper half-plane. -/
theorem norm_replicatedOneResolventMDETraceRemainder_upper_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖replicatedOneResolventMDETraceRemainder d f lambda z‖ ≤
      lambda ^ 2 * (z.im)⁻¹ * |z.im|⁻¹ *
        ((Real.pi ^ 2 / 2) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^ (1 / (2 : ℝ)) := by
  let m := replicatedExpectedOneResolventTrace d f lambda z
  let a := fun i : Fin (N * d) =>
    CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f)
      (lambda ^ 2) z m i
  let r := fun i : Fin (N * d) =>
    replicatedOneResolventCovarianceRemainder d f lambda z i i
  have hh : 0 < CEHNative.BlockBand.CEH.effectiveHeight
      (lambda ^ 2) z m := lt_of_lt_of_le hz
    (expectedTrace_effectiveHeight_ge_im hN hd f lambda hz)
  have hlower := expectedTrace_effectiveHeight_ge_im hN hd f lambda hz
  have ha (i : Fin (N * d)) : ‖a i‖ ≤ (z.im)⁻¹ := by
    apply (CEHNative.BlockBand.CEH.norm_entry_le_inv_effectiveHeight
      (replicatedSpectrum d f) hh i).trans
    simpa [one_div] using one_div_le_one_div_of_le hz hlower
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
    _ ≤ lambda ^ 2 * ((z.im)⁻¹ * (|z.im|⁻¹ *
        ((Real.pi ^ 2 / 2) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^ (1 / (2 : ℝ)))) := by
      gcongr
      unfold CEHNative.BlockBand.CEH.averageReal
      apply (div_le_iff₀ (by exact_mod_cast Nat.mul_pos hN hd)).2
      calc
        ∑ i : Fin (N * d), ‖a i * r i‖ ≤
            ∑ _i : Fin (N * d), (z.im)⁻¹ * (|z.im|⁻¹ *
              ((Real.pi ^ 2 / 2) * lambda ^ 2 *
                (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^
                  (1 / (2 : ℝ))) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul]
          exact mul_le_mul (ha i) (hr i) (norm_nonneg _)
            (inv_nonneg.mpr hz.le)
        _ = ((N * d : ℕ) : ℝ) * ((z.im)⁻¹ * (|z.im|⁻¹ *
              ((Real.pi ^ 2 / 2) * lambda ^ 2 *
                (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^
                  (1 / (2 : ℝ)))) := by simp
        _ = ((z.im)⁻¹ * (|z.im|⁻¹ *
              ((Real.pi ^ 2 / 2) * lambda ^ 2 *
                (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^
                  (1 / (2 : ℝ)))) * ((N * d : ℕ) : ℝ) := by ring
    _ = _ := by ring

/-- Exact nonlinear stability equation for an approximate scalar Dyson fixed
point around an exact one. -/
theorem approximateMDE_nonlinear_stability_equation
    {K : ℕ} (f : Spectrum K) (s : ℝ) (z m u R : ℂ)
    (hhm : CEHNative.BlockBand.CEH.effectiveHeight s z m ≠ 0)
    (hhu : CEHNative.BlockBand.CEH.effectiveHeight s z u ≠ 0)
    (happrox : m = CEHNative.BlockBand.CEH.average
      (CEHNative.BlockBand.CEH.entry f s z m) + R)
    (hfixed : u = CEHNative.BlockBand.CEH.average
      (CEHNative.BlockBand.CEH.entry f s z u)) :
    CEHNative.BlockBand.CEH.stabilityDenominator f s z u * (m - u) =
      R + (s : ℂ) ^ 2 * (m - u) ^ 2 *
        CEHNative.BlockBand.CEH.average (fun i =>
          CEHNative.BlockBand.CEH.entry f s z m i *
            CEHNative.BlockBand.CEH.entry f s z u i ^ 2) := by
  let em := CEHNative.BlockBand.CEH.entry f s z m
  let eu := CEHNative.BlockBand.CEH.entry f s z u
  change m = CEHNative.BlockBand.CEH.average em + R at happrox
  change u = CEHNative.BlockBand.CEH.average eu at hfixed
  have hdiff (i : Fin K) :
      em i - eu i = (s : ℂ) * (m - u) * em i * eu i := by
    have hnm := CEHNative.BlockBand.CEH.denominator_ne_zero_of_height_ne
      f hhm i
    have hnu := CEHNative.BlockBand.CEH.denominator_ne_zero_of_height_ne
      f hhu i
    unfold em eu CEHNative.BlockBand.CEH.entry
    field_simp [hnm, hnu]
    ring
  have havgdiff : CEHNative.BlockBand.CEH.average em -
      CEHNative.BlockBand.CEH.average eu =
      (s : ℂ) * (m - u) *
        CEHNative.BlockBand.CEH.average (fun i => em i * eu i) := by
    unfold CEHNative.BlockBand.CEH.average
    rw [← sub_div, ← Finset.sum_sub_distrib]
    simp_rw [hdiff]
    simp_rw [show ∀ i, (s : ℂ) * (m - u) * em i * eu i =
      ((s : ℂ) * (m - u)) * (em i * eu i) by intro i; ring]
    rw [← Finset.mul_sum]
    ring
  have hmixdiff : CEHNative.BlockBand.CEH.average
        (fun i => em i * eu i) -
      CEHNative.BlockBand.CEH.average (fun i => eu i ^ 2) =
      (s : ℂ) * (m - u) *
        CEHNative.BlockBand.CEH.average
          (fun i => em i * eu i ^ 2) := by
    unfold CEHNative.BlockBand.CEH.average
    rw [← sub_div, ← Finset.sum_sub_distrib]
    simp_rw [show ∀ i, em i * eu i - eu i ^ 2 =
        (em i - eu i) * eu i by intro i; ring, hdiff]
    simp_rw [show ∀ i, ((s : ℂ) * (m - u) * em i * eu i) * eu i =
      ((s : ℂ) * (m - u)) * (em i * eu i ^ 2) by intro i; ring]
    rw [← Finset.mul_sum]
    ring
  have hdelta : m - u = (s : ℂ) * (m - u) *
      CEHNative.BlockBand.CEH.average (fun i => em i * eu i) + R := by
    calc
      m - u = (CEHNative.BlockBand.CEH.average em -
          CEHNative.BlockBand.CEH.average eu) + R := by
        rw [happrox, hfixed]
        ring
      _ = _ := by rw [havgdiff]
  unfold CEHNative.BlockBand.CEH.stabilityDenominator
  change (1 - (s : ℂ) * CEHNative.BlockBand.CEH.average
      (fun i => eu i ^ 2)) * (m - u) = _
  calc
    _ = (1 - (s : ℂ) * CEHNative.BlockBand.CEH.average
          (fun i => em i * eu i)) * (m - u) +
        (s : ℂ) * (CEHNative.BlockBand.CEH.average (fun i => em i * eu i) -
          CEHNative.BlockBand.CEH.average (fun i => eu i ^ 2)) *
          (m - u) := by ring
    _ = R + (s : ℂ) * (CEHNative.BlockBand.CEH.average (fun i => em i * eu i) -
          CEHNative.BlockBand.CEH.average (fun i => eu i ^ 2)) *
          (m - u) := by
      linear_combination hdelta
    _ = _ := by rw [hmixdiff]; ring

/-- Ward-height bound for the cubic coefficient in the nonlinear stability
remainder. -/
theorem norm_average_entry_mul_sq_le
    {K : ℕ} (hK : 0 < K) (f : Spectrum K) (s : ℝ) (z m u : ℂ)
    {eta : ℝ} (heta : 0 < eta)
    (hm : eta ≤ CEHNative.BlockBand.CEH.effectiveHeight s z m)
    (hu : eta ≤ CEHNative.BlockBand.CEH.effectiveHeight s z u) :
    ‖CEHNative.BlockBand.CEH.average (fun i =>
        CEHNative.BlockBand.CEH.entry f s z m i *
          CEHNative.BlockBand.CEH.entry f s z u i ^ 2)‖ ≤
      eta⁻¹ ^ 3 := by
  have hhm : 0 < CEHNative.BlockBand.CEH.effectiveHeight s z m :=
    lt_of_lt_of_le heta hm
  have hhu : 0 < CEHNative.BlockBand.CEH.effectiveHeight s z u :=
    lt_of_lt_of_le heta hu
  have hem (i : Fin K) :
      ‖CEHNative.BlockBand.CEH.entry f s z m i‖ ≤ eta⁻¹ := by
    apply (CEHNative.BlockBand.CEH.norm_entry_le_inv_effectiveHeight
      f hhm i).trans
    simpa [one_div] using one_div_le_one_div_of_le heta hm
  have heu (i : Fin K) :
      ‖CEHNative.BlockBand.CEH.entry f s z u i‖ ≤ eta⁻¹ := by
    apply (CEHNative.BlockBand.CEH.norm_entry_le_inv_effectiveHeight
      f hhu i).trans
    simpa [one_div] using one_div_le_one_div_of_le heta hu
  calc
    _ ≤ CEHNative.BlockBand.CEH.averageReal (fun i =>
        ‖CEHNative.BlockBand.CEH.entry f s z m i *
          CEHNative.BlockBand.CEH.entry f s z u i ^ 2‖) :=
      CEHNative.BlockBand.CEH.norm_average_le hK _
    _ ≤ eta⁻¹ ^ 3 := by
      unfold CEHNative.BlockBand.CEH.averageReal
      apply (div_le_iff₀ (by exact_mod_cast hK)).2
      calc
        ∑ i : Fin K, ‖CEHNative.BlockBand.CEH.entry f s z m i *
            CEHNative.BlockBand.CEH.entry f s z u i ^ 2‖ ≤
            ∑ _i : Fin K, eta⁻¹ ^ 3 := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul, norm_pow]
          have hetaInv : 0 ≤ eta⁻¹ := (inv_pos.mpr heta).le
          calc
            ‖CEHNative.BlockBand.CEH.entry f s z m i‖ *
                ‖CEHNative.BlockBand.CEH.entry f s z u i‖ ^ 2 ≤
              eta⁻¹ * eta⁻¹ ^ 2 := by
                gcongr
                · exact hem i
                · exact heu i
            _ = eta⁻¹ ^ 3 := by ring
        _ = (K : ℝ) * eta⁻¹ ^ 3 := by simp
        _ = eta⁻¹ ^ 3 * (K : ℝ) := by ring

/-- One exact nonlinear CEH stability bootstrap step at an arbitrary upper
half-plane parameter.  The hypothesis is the explicit small-branch condition
(to be propagated along a vertical grid); the proof uses the Gaussian
covariance residual and no local-law input. -/
theorem norm_replicatedExpectedTrace_sub_upperBranch_stability_step
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 < lambda)
    {z : ℂ} (hz : 0 < z.im)
    (hbootstrap :
      2 * (lambda ^ 2) ^ 2 * (z.im)⁻¹ ^ 3 *
          ‖replicatedExpectedOneResolventTrace d f lambda z -
            CEHNative.BlockBand.CEH.upperBranch
              (Nat.mul_pos hN hd) (replicatedSpectrum d f)
                (sq_pos_of_pos hlambda) z‖ ≤
        ‖CEHNative.BlockBand.CEH.stabilityDenominator
          (replicatedSpectrum d f) (lambda ^ 2) z
          (CEHNative.BlockBand.CEH.upperBranch
            (Nat.mul_pos hN hd) (replicatedSpectrum d f)
              (sq_pos_of_pos hlambda) z)‖) :
    ‖replicatedExpectedOneResolventTrace d f lambda z -
      CEHNative.BlockBand.CEH.upperBranch hN f
        (sq_pos_of_pos hlambda) z‖ ≤
      (2 * (lambda ^ 2 * (z.im)⁻¹ * |z.im|⁻¹ *
        ((Real.pi ^ 2 / 2) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^ (1 / (2 : ℝ)))) /
        ‖CEHNative.BlockBand.CEH.stabilityDenominator
          (replicatedSpectrum d f) (lambda ^ 2) z
          (CEHNative.BlockBand.CEH.upperBranch
            (Nat.mul_pos hN hd) (replicatedSpectrum d f)
              (sq_pos_of_pos hlambda) z)‖ := by
  let s := lambda ^ 2
  let m := replicatedExpectedOneResolventTrace d f lambda z
  let u := CEHNative.BlockBand.CEH.upperBranch
    (Nat.mul_pos hN hd) (replicatedSpectrum d f) (sq_pos_of_pos hlambda) z
  let R := replicatedOneResolventMDETraceRemainder d f lambda z
  let D := CEHNative.BlockBand.CEH.stabilityDenominator
    (replicatedSpectrum d f) s z u
  have hs : 0 < s := sq_pos_of_pos hlambda
  have hmHeight : z.im ≤ CEHNative.BlockBand.CEH.effectiveHeight
      s z m := expectedTrace_effectiveHeight_ge_im hN hd f lambda hz
  have huSol := CEHNative.BlockBand.CEH.upperBranch_isSolution
    (Nat.mul_pos hN hd) (replicatedSpectrum d f) hs hz
  have huHeight : z.im ≤ CEHNative.BlockBand.CEH.effectiveHeight
      s z u := by
    unfold CEHNative.BlockBand.CEH.effectiveHeight
    exact le_add_of_nonneg_right (mul_nonneg hs.le huSol.2.le)
  have happrox := replicatedExpectedTrace_approximateMDE_upper
    hN hd f lambda hz
  have hnonlinear := approximateMDE_nonlinear_stability_equation
    (replicatedSpectrum d f) s z m u R
    (lt_of_lt_of_le hz hmHeight).ne' (lt_of_lt_of_le hz huHeight).ne'
    happrox huSol.1
  have hB := norm_average_entry_mul_sq_le (Nat.mul_pos hN hd)
    (replicatedSpectrum d f) s z m u hz hmHeight huHeight
  have hdenLower := CEHNative.BlockBand.CEH.upperBranch_stability_quantitative
    (Nat.mul_pos hN hd) (replicatedSpectrum d f) hs hz
  have hDpos : 0 < ‖D‖ := lt_of_lt_of_le hdenLower.1 hdenLower.2
  have hmain : ‖D‖ * ‖m - u‖ ≤ ‖R‖ +
      s ^ 2 * (z.im)⁻¹ ^ 3 * ‖m - u‖ ^ 2 := by
    calc
      _ = ‖D * (m - u)‖ := by rw [norm_mul]
      _ = ‖R + (s : ℂ) ^ 2 * (m - u) ^ 2 *
          CEHNative.BlockBand.CEH.average (fun i =>
            CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f)
              s z m i *
            CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f)
              s z u i ^ 2)‖ := by rw [hnonlinear]
      _ ≤ ‖R‖ + ‖(s : ℂ) ^ 2 * (m - u) ^ 2 *
          CEHNative.BlockBand.CEH.average (fun i =>
            CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f)
              s z m i *
            CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f)
              s z u i ^ 2)‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hs.le]
        apply add_le_add le_rfl
        calc
          s ^ 2 * ‖m - u‖ ^ 2 *
              ‖CEHNative.BlockBand.CEH.average (fun i =>
                CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f)
                  s z m i *
                CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f)
                  s z u i ^ 2)‖ ≤
            s ^ 2 * ‖m - u‖ ^ 2 * (z.im)⁻¹ ^ 3 := by
              exact mul_le_mul_of_nonneg_left hB
                (mul_nonneg (sq_nonneg s) (sq_nonneg ‖m - u‖))
          _ = s ^ 2 * (z.im)⁻¹ ^ 3 * ‖m - u‖ ^ 2 := by ring
  have hboot : 2 * s ^ 2 * (z.im)⁻¹ ^ 3 * ‖m - u‖ ≤ ‖D‖ := by
    exact hbootstrap
  have hquad : s ^ 2 * (z.im)⁻¹ ^ 3 * ‖m - u‖ ^ 2 ≤
      (‖D‖ * ‖m - u‖) / 2 := by
    have hn := norm_nonneg (m - u)
    nlinarith [mul_le_mul_of_nonneg_right hboot hn]
  have hclose : ‖m - u‖ ≤ 2 * ‖R‖ / ‖D‖ := by
    apply (le_div_iff₀ hDpos).2
    nlinarith
  have hR := norm_replicatedOneResolventMDETraceRemainder_upper_le
    hN hd f lambda hz
  have hrep : u = CEHNative.BlockBand.CEH.upperBranch hN f
      (sq_pos_of_pos hlambda) z := by
    dsimp only [u]
    unfold CEHNative.BlockBand.CEH.upperBranch
    simp only [dite_eq_left hz]
    exact replicated_upperSolution hN hd f (sq_pos_of_pos hlambda) z hz
  rw [← hrep]
  apply hclose.trans
  apply div_le_div_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left hR (by positivity)
  · exact hDpos.le

/-- Ward-sign improvement of the unconditional contraction estimate: the
factor-two height loss from the first checkpoint is removed. -/
theorem norm_replicatedExpectedTrace_sub_upperBranch_ward_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 < lambda)
    {z : ℂ} (hz : 0 < z.im) (hhigh : lambda ^ 2 < z.im ^ 2) :
    ‖replicatedExpectedOneResolventTrace d f lambda z -
      CEHNative.BlockBand.CEH.upperBranch hN f
        (sq_pos_of_pos hlambda) z‖ ≤
      (lambda ^ 2 * (z.im)⁻¹ * |z.im|⁻¹ *
        ((Real.pi ^ 2 / 2) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^ (1 / (2 : ℝ))) /
      (1 - lambda ^ 2 * (z.im)⁻¹ ^ 2) := by
  let s := lambda ^ 2
  let m := replicatedExpectedOneResolventTrace d f lambda z
  let u := CEHNative.BlockBand.CEH.upperBranch
    (Nat.mul_pos hN hd) (replicatedSpectrum d f) (sq_pos_of_pos hlambda) z
  let R := replicatedOneResolventMDETraceRemainder d f lambda z
  let L := s * (z.im)⁻¹ ^ 2
  have hs : 0 < s := sq_pos_of_pos hlambda
  have hmHeight : z.im ≤ CEHNative.BlockBand.CEH.effectiveHeight
      s z m := expectedTrace_effectiveHeight_ge_im hN hd f lambda hz
  have huSol := CEHNative.BlockBand.CEH.upperBranch_isSolution
    (Nat.mul_pos hN hd) (replicatedSpectrum d f) hs hz
  have huHeight : z.im ≤ CEHNative.BlockBand.CEH.effectiveHeight
      s z u := by
    unfold CEHNative.BlockBand.CEH.effectiveHeight
    exact le_add_of_nonneg_right (mul_nonneg hs.le huSol.2.le)
  have hLip := norm_average_entry_sub_le (Nat.mul_pos hN hd)
    (replicatedSpectrum d f) hs.le z m u
      (lt_of_lt_of_le hz hmHeight) (lt_of_lt_of_le hz huHeight)
  have hLip' :
      ‖CEHNative.BlockBand.CEH.average
          (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z m) -
        CEHNative.BlockBand.CEH.average
          (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z u)‖ ≤
        L * ‖m - u‖ := by
    apply hLip.trans
    have hInvM :
        (CEHNative.BlockBand.CEH.effectiveHeight s z m)⁻¹ ≤
          (z.im)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hz hmHeight
    have hInvU :
        (CEHNative.BlockBand.CEH.effectiveHeight s z u)⁻¹ ≤
          (z.im)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hz huHeight
    dsimp only [L]
    have hinvprod :
        (CEHNative.BlockBand.CEH.effectiveHeight s z m)⁻¹ *
            (CEHNative.BlockBand.CEH.effectiveHeight s z u)⁻¹ ≤
          (z.im)⁻¹ * (z.im)⁻¹ :=
      mul_le_mul hInvM hInvU
        (inv_nonneg.mpr (lt_of_lt_of_le hz huHeight).le)
        (inv_nonneg.mpr hz.le)
    calc
      s * (CEHNative.BlockBand.CEH.effectiveHeight s z m)⁻¹ *
          (CEHNative.BlockBand.CEH.effectiveHeight s z u)⁻¹ *
          ‖m - u‖ =
        (s * ((CEHNative.BlockBand.CEH.effectiveHeight s z m)⁻¹ *
          (CEHNative.BlockBand.CEH.effectiveHeight s z u)⁻¹)) *
          ‖m - u‖ := by ring
      _ ≤
        s * ((z.im)⁻¹ * (z.im)⁻¹) * ‖m - u‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinvprod hs.le) (norm_nonneg _)
      _ = s * (z.im)⁻¹ ^ 2 * ‖m - u‖ := by ring
  have happrox := replicatedExpectedTrace_approximateMDE_upper
    hN hd f lambda hz
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
                    (replicatedSpectrum d f) s z m) + R) - u :=
                congrArg (fun w : ℂ => w - u) happrox
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
  have hL : L < 1 := by
    dsimp only [L, s]
    have hinv : z.im * (z.im)⁻¹ = 1 := mul_inv_cancel₀ hz.ne'
    have hinvSq : z.im ^ 2 * (z.im)⁻¹ ^ 2 = 1 := by
      rw [← mul_pow]
      simp [hinv]
    nlinarith
  have hisolate : ‖m - u‖ ≤ ‖R‖ / (1 - L) := by
    apply (le_div_iff₀ (sub_pos.mpr hL)).2
    nlinarith
  have hR := norm_replicatedOneResolventMDETraceRemainder_upper_le
    hN hd f lambda hz
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
