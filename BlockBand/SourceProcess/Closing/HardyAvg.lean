module

public import BlockBand.SourceProcess.Closing.Hardy

/-!
# Phase averages of the closing correction

* `phaseAvg_closingX`: `E_z X = 0`. The Fourier coefficients `c_k = E_z z^k X` satisfy
  `c_k = N c_{k+1}` (from `X = z(T + NX)` and `E_z z^{k+1} = 0`), so `c_0 = N^k c_k → 0`.
* `closingT_mul_conj`, `closingN_mul_proj`: the algebraic inputs of the Hardy series.

The sibling module `HardyMain` proves from these:
* `phaseAvg_closingX_mul`: `E_z XXᴴ = A` (Hardy series: `Y = TTᴴ + NYNᴴ`, `TTᴴ = A - NNᴴ`,
  so `Y - A = N^n (Y - A) (N^n)ᴴ → 0`).
* `phaseAvg_closingDefect`: `E_z (C(z) - 1)(C(z) - 1)ᴴ = 2A` (the Gaussian closing error).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Closing

open MeasureTheory Matrix Filter Topology
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S A Pi : Matrix ι ι ℂ}

section Fixed

variable (hU : ∀ θ, IsUnit (1 - phase θ • closingN S A Pi).det)
include hU

theorem phaseAvg_coeff_succ (k : ℕ) :
    phaseAvg (fun θ => phase θ ^ k • closingX S A Pi θ) =
      closingN S A Pi * phaseAvg (fun θ => phase θ ^ (k + 1) • closingX S A Pi θ) := by
  have hX := continuous_closingX hU
  have e : ∀ θ, phase θ ^ k • closingX S A Pi θ = phase θ ^ (k + 1) • closingT S A Pi +
      closingN S A Pi * (phase θ ^ (k + 1) • closingX S A Pi θ) := by
    intro θ
    conv_lhs => rw [closingX_fixed hU θ]
    rw [smul_smul, ← pow_succ, smul_add, Matrix.mul_smul]
  simp_rw [e]
  rw [phaseAvg_add (f := fun θ => phase θ ^ (k + 1) • closingT S A Pi)
      (g := fun θ => closingN S A Pi * (phase θ ^ (k + 1) • closingX S A Pi θ))
      ((continuous_phase.pow _).smul continuous_const)
      (continuous_const.matrix_mul ((continuous_phase.pow _).smul hX)),
    phaseAvg_phase_pow_smul (by omega), phaseAvg_mul_left _ (f := fun θ => phase θ ^ (k + 1) • closingX S A Pi θ)
      ((continuous_phase.pow _).smul hX),
    zero_add]

theorem phaseAvg_closingX_eq_pow (k : ℕ) :
    phaseAvg (closingX S A Pi) =
      closingN S A Pi ^ k * phaseAvg (fun θ => phase θ ^ k • closingX S A Pi θ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [ih, phaseAvg_coeff_succ hU k, pow_succ, Matrix.mul_assoc]

end Fixed

/-- **`E_z X(z) = 0`.** -/
theorem phaseAvg_closingX (hN : Tendsto (fun n => closingN S A Pi ^ n) atTop (𝓝 0)) :
    phaseAvg (closingX S A Pi) = 0 := by
  have hU : ∀ θ, IsUnit (1 - phase θ • closingN S A Pi).det :=
    fun θ => isUnit_det_of_tendsto hN (norm_phase θ)
  set N := closingN S A Pi
  ext i l
  set c := fun k : ℕ => phaseAvg (fun θ => phase θ ^ k • closingX S A Pi θ)
  set B := fun j => ∫ θ, ‖closingX S A Pi θ j l‖ ∂phaseLaw
  have hbd : ∀ k, ‖(N ^ k * c k) i l‖ ≤ ∑ j, ‖(N ^ k) i j‖ * B j := by
    intro k
    rw [mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_phaseAvg_pow_smul_le k _ j l) (norm_nonneg _)
  have hlim : Tendsto (fun k => ∑ j, ‖(N ^ k) i j‖ * B j) atTop (𝓝 0) := by
    have h : Tendsto (fun k => ∑ j, ‖(N ^ k) i j‖ * B j) atTop (𝓝 (∑ j, ‖(0 : Matrix ι ι ℂ) i j‖ * B j)) := by
      refine tendsto_finsetSum _ fun j _ => Tendsto.mul_const _ ?_
      exact ((continuous_norm.comp (continuous_id.matrix_elem i j)).tendsto 0).comp hN
    simpa using h
  have h0 : Tendsto (fun k => (N ^ k * c k) i l) atTop (𝓝 0) :=
    squeeze_zero_norm hbd hlim
  have he : ∀ k, (N ^ k * c k) i l = phaseAvg (closingX S A Pi) i l := fun k => by
    rw [phaseAvg_closingX_eq_pow hU k]
  simp_rw [he] at h0
  exact tendsto_nhds_unique tendsto_const_nhds h0

theorem closingT_mul_conj (hA2 : A * A = A) (hAH : Aᴴ = A) (hPi : Pi * Piᴴ = A)
    (hS : S * Sᴴ = 1) :
    closingT S A Pi * (closingT S A Pi)ᴴ = A - closingN S A Pi * (closingN S A Pi)ᴴ := by
  have h1 : (1 - A) * (1 - A)ᴴ = 1 - A := by
    rw [conjTranspose_sub, conjTranspose_one, hAH, sub_mul, mul_sub, mul_sub, one_mul, mul_one,
      one_mul, hA2]
    abel
  have hP : (Pi * S) * (Pi * S)ᴴ = A := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc S, hS, Matrix.one_mul, hPi]
  have hT : closingT S A Pi * (closingT S A Pi)ᴴ = (Pi * S) * ((1 - A) * (1 - A)ᴴ) * (Pi * S)ᴴ := by
    simp only [closingT, conjTranspose_mul, Matrix.mul_assoc]
  have hN : closingN S A Pi * (closingN S A Pi)ᴴ = (Pi * S) * (A * Aᴴ) * (Pi * S)ᴴ := by
    simp only [closingN, conjTranspose_mul, Matrix.mul_assoc]
  rw [hT, hN, h1, hAH, hA2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP]

omit [DecidableEq ι] in
theorem closingN_mul_proj (hA2 : A * A = A) : closingN S A Pi * A = closingN S A Pi := by
  rw [closingN, Matrix.mul_assoc, hA2]

end BlockBand.SourceProcess.Closing
