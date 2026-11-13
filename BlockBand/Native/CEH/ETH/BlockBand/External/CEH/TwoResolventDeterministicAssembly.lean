module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventStability
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventLemma56

/-!
# Unconditional finite-dimensional assembly of CEH two-resolvent stability

This module assembles the deterministic content of Cipolloni–Erdős–Henheik
Lemma 5.6 that follows from the finite-dimensional MDE. It uses the
`N × d` tensor replication, the exact rank-one stability inverse, and the
source cutoff `θ ∈ {0, 1/2, 1}`. There is no given solution, stability
certificate, comparison hypothesis, or asymptotic meta-limit.

The observable estimate below keeps the source constant `2`. At the cutoff
transition the regularized numerator and the real part of the denominator are
both exactly `1/2`; this case is treated directly here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped BigOperators ComplexConjugate

/-- For a nonzero mixed MDE pairing, CEH regularization multiplies the bare
mixed trace by exactly `1 - θ`.  This is the finite-dimensional numerator
identity behind the cutoff-regularized observable estimate in Lemma 5.6. -/
theorem NTrace_regularizedObservable_word {N : ℕ} (theta : ℝ)
    (M₁plus M₂minus A : Matrix (Fin N) (Fin N) ℂ)
    (hpair : NTrace (M₁plus * M₂minus) ≠ 0) :
    NTrace (M₁plus * regularizedObservable theta M₁plus M₂minus A * M₂minus) =
      ((1 - theta : ℝ) : ℂ) * NTrace (M₁plus * A * M₂minus) := by
  simp only [regularizedObservable]
  rw [Matrix.mul_sub, Matrix.sub_mul, NTrace_sub]
  rw [show M₁plus *
      (((theta : ℂ) *
        (NTrace (M₁plus * A * M₂minus) / NTrace (M₁plus * M₂minus))) •
        (1 : Matrix (Fin N) (Fin N) ℂ)) * M₂minus =
      ((theta : ℂ) *
        (NTrace (M₁plus * A * M₂minus) / NTrace (M₁plus * M₂minus))) •
        (M₁plus * M₂minus) by
    simp [Matrix.mul_assoc]]
  rw [NTrace_smul]
  field_simp [hpair]
  push_cast
  ring

/-- On the unconditional scalar MDE branches, the exact CEH cutoff-regularized
deterministic mixed two-resolvent trace is bounded by twice the bare mixed
word.  The quantifiers are finite-dimensional and uniform in `N`, the two
upper-half-plane spectral parameters, and the deterministic observable.  The
constant is the source constant `2`; the order of limits is vacuous because no
limit is used. -/
theorem upperBranch_cutoffRegularized_twoResolventTrace_le
    {N : ℕ} (hN : 0 < N)
    (f : CEHNative.BlockBand.CEH.DeformationSpectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let m₁ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₁
    let m₂ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₂
    let M₁ := PencilAdapter.mdeMatrix f lambda z₁ m₁
    let M₂ := (PencilAdapter.mdeMatrix f lambda z₂ m₂)ᴴ
    let theta := regularizationCoefficient (lambda : ℂ) M₁ M₂
    ‖NTrace (twoResolventApprox (lambda : ℂ) M₁
        (regularizedObservable theta M₁ M₂ A) M₂)‖ ≤
      2 * ‖NTrace (M₁ * A * M₂)‖ := by
  dsimp only
  let m₁ := CEHNative.BlockBand.CEH.upperBranch hN f
    (sq_pos_of_pos hlambda) z₁
  let m₂ := CEHNative.BlockBand.CEH.upperBranch hN f
    (sq_pos_of_pos hlambda) z₂
  let M₁ := PencilAdapter.mdeMatrix f lambda z₁ m₁
  let M₂ := (PencilAdapter.mdeMatrix f lambda z₂ m₂)ᴴ
  let q : ℂ := (lambda : ℂ) ^ 2 * NTrace (M₁ * M₂)
  let x : ℝ := q.re - 1 / 2
  change ‖NTrace (twoResolventApprox (lambda : ℂ) M₁
      (regularizedObservable (regularizationCoefficient (lambda : ℂ) M₁ M₂)
        M₁ M₂ A) M₂)‖ ≤ 2 * ‖NTrace (M₁ * A * M₂)‖
  have hm₁ : CEHNative.BlockBand.CEH.IsSolution f
      (lambda ^ 2) z₁ m₁ :=
    CEHNative.BlockBand.CEH.upperBranch_isSolution
      hN f (sq_pos_of_pos hlambda) hz₁
  have hm₂ : CEHNative.BlockBand.CEH.IsSolution f
      (lambda ^ 2) z₂ m₂ :=
    CEHNative.BlockBand.CEH.upperBranch_isSolution
      hN f (sq_pos_of_pos hlambda) hz₂
  have hbeta : stabilityDenominator (lambda : ℂ) (NTrace (M₁ * M₂)) ≠ 0 := by
    simpa [M₁, M₂, chooseAdjoint] using
      (PencilAdapter.constellation_stability_ne_zero hN f lambda hlambda.le
        z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂ AdjointChoice.plain AdjointChoice.adjoint)
  by_cases hxneg : x < 0
  · have htheta : regularizationCoefficient (lambda : ℂ) M₁ M₂ = 0 := by
      simpa [regularizationCoefficient, x, q] using cehTheta_of_neg hxneg
    rw [htheta, regularizedObservable_inactive]
    exact inactiveCutoff_twoResolventTrace_le (lambda : ℂ) M₁ A M₂ htheta
  · by_cases hxzero : x = 0
    · have htheta : regularizationCoefficient (lambda : ℂ) M₁ M₂ = 1 / 2 := by
        change cehTheta x = 1 / 2
        rw [hxzero]
        exact cehTheta_zero
      have hqre : q.re = 1 / 2 := by
        dsimp [x] at hxzero
        linarith
      have hpair : NTrace (M₁ * M₂) ≠ 0 := by
        intro hzero
        have : q = 0 := by simp [q, hzero]
        rw [this] at hqre
        norm_num at hqre
      rw [htheta, twoResolventApprox_eq_stabilityInverse,
        NTrace_twoBodyStabilityInverse (lambda : ℂ) M₁ M₂ _ hbeta,
        NTrace_regularizedObservable_word (1 / 2) M₁ M₂ A hpair]
      rw [norm_div, norm_mul]
      have hbetaHalf : (1 / 2 : ℝ) ≤
          ‖stabilityDenominator (lambda : ℂ) (NTrace (M₁ * M₂))‖ := by
        have hre :
            (stabilityDenominator (lambda : ℂ) (NTrace (M₁ * M₂))).re = 1 / 2 := by
          change 1 - q.re = 1 / 2
          rw [hqre]
          norm_num
        calc
          (1 / 2 : ℝ) =
              |(stabilityDenominator (lambda : ℂ) (NTrace (M₁ * M₂))).re| := by
                rw [hre]
                norm_num
          _ ≤ _ := Complex.abs_re_le_norm _
      have hbetaPos : 0 <
          ‖stabilityDenominator (lambda : ℂ) (NTrace (M₁ * M₂))‖ :=
        (by norm_num : (0 : ℝ) < 1 / 2).trans_le hbetaHalf
      apply (div_le_iff₀ hbetaPos).2
      have hhalfNorm : ‖(((1 - (1 / 2 : ℝ) : ℝ) : ℂ))‖ = (1 / 2 : ℝ) := by
        norm_num
      rw [hhalfNorm]
      have hnonneg : 0 ≤ ‖NTrace (M₁ * A * M₂)‖ := norm_nonneg _
      nlinarith
    · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hxneg) (Ne.symm hxzero)
      have htheta : regularizationCoefficient (lambda : ℂ) M₁ M₂ = 1 := by
        simpa [regularizationCoefficient, x, q] using cehTheta_of_pos hxpos
      rw [htheta,
        activeCutoff_regularized_twoResolventTrace_zero_of_coefficient
          (lambda : ℂ) M₁ M₂ A htheta hbeta, norm_zero]
      positivity

/-- Exact two-sided stability inversion for every adjoint constellation of the
unconditional finite-dimensional scalar MDE branch. -/
theorem upperBranch_constellation_stability_inverse
    {N : ℕ} (hN : 0 < N)
    (f : CEHNative.BlockBand.CEH.DeformationSpectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (c₁ c₂ : AdjointChoice) (Y : Matrix (Fin N) (Fin N) ℂ) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let m₁ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₁
    let m₂ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₂
    let M₁ := chooseAdjoint c₁ (PencilAdapter.mdeMatrix f lambda z₁ m₁)
    let M₂ := chooseAdjoint c₂ (PencilAdapter.mdeMatrix f lambda z₂ m₂)
    twoBodyStability (lambda : ℂ) M₁ M₂
        (twoBodyStabilityInverse (lambda : ℂ) M₁ M₂ Y) = Y ∧
      twoBodyStabilityInverse (lambda : ℂ) M₁ M₂
        (twoBodyStability (lambda : ℂ) M₁ M₂ Y) = Y := by
  dsimp only
  let m₁ := CEHNative.BlockBand.CEH.upperBranch hN f
    (sq_pos_of_pos hlambda) z₁
  let m₂ := CEHNative.BlockBand.CEH.upperBranch hN f
    (sq_pos_of_pos hlambda) z₂
  have hm₁ : CEHNative.BlockBand.CEH.IsSolution f
      (lambda ^ 2) z₁ m₁ :=
    CEHNative.BlockBand.CEH.upperBranch_isSolution
      hN f (sq_pos_of_pos hlambda) hz₁
  have hm₂ : CEHNative.BlockBand.CEH.IsSolution f
      (lambda ^ 2) z₂ m₂ :=
    CEHNative.BlockBand.CEH.upperBranch_isSolution
      hN f (sq_pos_of_pos hlambda) hz₂
  have hbeta := PencilAdapter.constellation_stability_ne_zero hN f lambda
    hlambda.le z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂ c₁ c₂
  exact ⟨twoBodyStability_inverse_right _ _ _ Y hbeta,
    twoBodyStability_inverse_left _ _ _ Y hbeta⟩

/-- Finite-dimensional assembly of CEH two-resolvent stability: exact tensor replication,
two-sided stability inversion, and the cutoff-regularized observable bound hold simultaneously on
the unconditional upper MDE branch. The statement is uniform in the tensor size and introduces no
certificate root or comparison assumption. It does not claim the five Ward-scale inequalities of
CEH Lemma 5.6. -/
theorem twoResolventDeterministicAssembly
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : CEHNative.BlockBand.CEH.DeformationSpectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (A Y : Matrix (Fin N) (Fin N) ℂ) (c₁ c₂ : AdjointChoice) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let m₁ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₁
    let m₂ := CEHNative.BlockBand.CEH.upperBranch hN f hs z₂
    let M₁plus := PencilAdapter.mdeMatrix f lambda z₁ m₁
    let M₂plus := PencilAdapter.mdeMatrix f lambda z₂ m₂
    let M₁ := chooseAdjoint c₁ M₁plus
    let M₂ := chooseAdjoint c₂ M₂plus
    productNTrace
        (productTwoResolventApprox (lambda : ℂ) (tensorReplicate d M₁)
          (tensorReplicate d A) (tensorReplicate d M₂)) =
        NTrace (twoResolventApprox (lambda : ℂ) M₁ A M₂) ∧
      (twoBodyStability (lambda : ℂ) M₁ M₂
          (twoBodyStabilityInverse (lambda : ℂ) M₁ M₂ Y) = Y ∧
        twoBodyStabilityInverse (lambda : ℂ) M₁ M₂
          (twoBodyStability (lambda : ℂ) M₁ M₂ Y) = Y) ∧
      ‖NTrace (twoResolventApprox (lambda : ℂ) M₁plus
          (regularizedObservable
            (regularizationCoefficient (lambda : ℂ) M₁plus M₂plusᴴ)
            M₁plus M₂plusᴴ A) M₂plusᴴ)‖ ≤
        2 * ‖NTrace (M₁plus * A * M₂plusᴴ)‖ := by
  dsimp only
  refine ⟨productNTrace_productTwoResolventApprox_tensorReplicate hN hd
    (lambda : ℂ) _ _ _, ?_, ?_⟩
  · exact upperBranch_constellation_stability_inverse hN f lambda hlambda
      hz₁ hz₂ c₁ c₂ Y
  · exact upperBranch_cutoffRegularized_twoResolventTrace_le hN f lambda
      hlambda hz₁ hz₂ A

end CEHNative.BlockBand.External.CEH
