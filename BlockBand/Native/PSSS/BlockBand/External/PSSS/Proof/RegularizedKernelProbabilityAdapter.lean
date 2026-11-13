module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.RegularizedKernelFourier
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WeightedSquaresLaw

/-!
# Boundary continuity for the regularized APSSS kernel

This module supplies the continuity adapter needed to apply the
Fourier–Stieltjes inversion theorem to the weighted-square random vector.  In
particular, the proof treats the full boundary hyperplane with first coordinate
zero, including the value attained by the zero Gaussian input.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology FourierTransform

/-- At every point of the boundary hyperplane, the regularized kernel is
continuous.  The Gaussian factor is bounded by one, while the zero-extended
factor `exp (-δ x) * x ^ δ` is squeezed by `|x| ^ δ`. -/
theorem continuousAt_regularizedKernelEuclidean_first_eq_zero
    {ε δ : ℝ} (hδ : 0 < δ) {x : RegularizedKernelPlane} (hx : x 0 = 0) :
    ContinuousAt (regularizedKernelEuclidean ε δ) x := by
  rw [ContinuousAt]
  have hkx : regularizedKernelEuclidean ε δ x = 0 := by
    simp [regularizedKernelEuclidean, regularizedFourierRatioKernel, hx]
  rw [hkx]
  refine squeeze_zero_norm (a := fun y : RegularizedKernelPlane => |y 0| ^ δ) ?_ ?_
  · intro y
    by_cases hy : 0 < y 0
    · have hden : 0 ≤ 4 * ε ^ 2 * y 0 := by positivity
      have hgauss : Real.exp (-(y 1 ^ 2) / (4 * ε ^ 2 * y 0)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hden
      have hdamp : Real.exp (-δ * y 0) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) hy.le
      have hpow : 0 ≤ y 0 ^ δ := Real.rpow_nonneg hy.le _
      rw [regularizedKernelEuclidean, regularizedFourierRatioKernel, ite_eq_left hy]
      rw [Complex.norm_real]
      change |Real.exp (-(y 1 ^ 2) / (4 * ε ^ 2 * y 0)) *
        Real.exp (-δ * y 0) * y 0 ^ δ| ≤ |y 0| ^ δ
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
          (Real.exp_pos _).le) hpow), abs_of_pos hy]
      calc
        Real.exp (-(y 1 ^ 2) / (4 * ε ^ 2 * y 0)) *
              Real.exp (-δ * y 0) * y 0 ^ δ
            ≤ 1 * 1 * y 0 ^ δ := by gcongr
        _ = y 0 ^ δ := by ring
    · simp [regularizedKernelEuclidean, regularizedFourierRatioKernel, hy]
      positivity
  · have hcoord : Tendsto (fun y : RegularizedKernelPlane => |y 0|) (𝓝 x) (𝓝 0) := by
      have hc : ContinuousAt (fun y : RegularizedKernelPlane => |y 0|) x :=
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).abs).continuousAt
      simpa [hx] using hc.tendsto
    exact hcoord.rpow_const_nhds_zero hδ

/-- The regularized kernel is continuous everywhere for a positive power
regularizer, including the boundary `x = 0`. -/
theorem continuous_regularizedKernelEuclidean {ε δ : ℝ} (hδ : 0 < δ) :
    Continuous (regularizedKernelEuclidean ε δ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x 0 = 0
  · exact continuousAt_regularizedKernelEuclidean_first_eq_zero hδ hx
  · rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hev : ∀ᶠ y : RegularizedKernelPlane in 𝓝 x, ¬ 0 < y 0 :=
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt.eventually
          (Iio_mem_nhds hxneg)).mono (fun y hy => not_lt_of_ge hy.le)
      refine (continuousAt_const : ContinuousAt
        (fun _ : RegularizedKernelPlane => (0 : ℂ)) x).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      simp [regularizedKernelEuclidean, regularizedFourierRatioKernel, hy]
    · let f : RegularizedKernelPlane → ℂ := fun y =>
        ((Real.exp (-(y 1 ^ 2) / (4 * ε ^ 2 * y 0)) *
          Real.exp (-δ * y 0) * y 0 ^ δ : ℝ) : ℂ)
      have hf : ContinuousAt f x := by
        dsimp [f]
        apply Complex.continuous_ofReal.continuousAt.comp
        have h0 : ContinuousAt (fun y : RegularizedKernelPlane => y 0) x :=
          (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt
        have h1 : ContinuousAt (fun y : RegularizedKernelPlane => y 1) x :=
          (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).continuousAt
        by_cases hε0 : ε = 0
        · simp [hε0]
          exact ((continuousAt_const.mul h0).neg.rexp).mul
            (h0.rpow_const (Or.inl hx))
        · fun_prop (disch := aesop)
      have hev : ∀ᶠ y : RegularizedKernelPlane in 𝓝 x, 0 < y 0 :=
        (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt.eventually
          (Ioi_mem_nhds hxpos)
      refine hf.congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      simp [regularizedKernelEuclidean, regularizedFourierRatioKernel, f, hy]

end PSSSNative.BlockBand.PSSS
