module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierStieltjesInversion
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removal of the positive APSSS Fourier regularizer

The positive regularizer of the APSSS Fourier kernel is at most one, so the regularized kernels
are measurable and uniformly bounded by one.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Filter MeasureTheory Set
open scoped Topology

/-- The positive scalar regularizer never exceeds one. -/
theorem positiveRegularizer_factor_le_one {x δ : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) :
    Real.exp (-δ * x) * x ^ δ ≤ 1 := by
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add, Real.exp_le_one_iff]
  have hlog : Real.log x ≤ x := Real.log_le_self hx.le
  nlinarith

/-- The regularized kernel is uniformly bounded by one. -/
theorem abs_regularizedFourierRatioKernel_le_one {ε δ x y : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ) :
    |regularizedFourierRatioKernel ε δ x y| ≤ 1 := by
  by_cases hx : 0 < x
  · rw [regularizedFourierRatioKernel, ite_eq_left hx, abs_of_nonneg (by positivity)]
    have hg : Real.exp (-y ^ 2 / (4 * ε ^ 2 * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg y))
        (by positivity)
    have hr := positiveRegularizer_factor_le_one hx hδ
    have hgn : 0 ≤ Real.exp (-y ^ 2 / (4 * ε ^ 2 * x)) := Real.exp_nonneg _
    have hrn : 0 ≤ Real.exp (-δ * x) * x ^ δ := by positivity
    nlinarith
  · simp [regularizedFourierRatioKernel, hx]

/-- Measurability of every regularized kernel. -/
theorem measurable_regularizedFourierRatioKernel (ε δ : ℝ) :
    Measurable (fun p : ℝ × ℝ => regularizedFourierRatioKernel ε δ p.1 p.2) := by
  unfold regularizedFourierRatioKernel
  apply Measurable.ite
  · exact measurableSet_lt measurable_const measurable_fst
  · fun_prop
  · exact measurable_const

end PSSSNative.BlockBand.PSSS
