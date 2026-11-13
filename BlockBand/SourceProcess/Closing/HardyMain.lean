module

public import BlockBand.SourceProcess.Closing.HardyAvg

/-!
# The closing covariance identity `E_z (C(z) - 1)(C(z) - 1)ᴴ = 2A`

The Hardy-series identity `E_z XXᴴ = A` (`phaseAvg_closingX_mul`) and, with `E_z X = 0`, the
covariance identity `E_z (C(z) - 1)(C(z) - 1)ᴴ = 2A` (`phaseAvg_closingDefect`), for an orthogonal
projection `A`, `ΠΠᴴ = A`, `𝕊𝕊ᴴ = 1` and `N^n → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Closing

open MeasureTheory Matrix Filter Topology
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S A Pi : Matrix ι ι ℂ}

omit [DecidableEq ι] in
/-- If `X = z(T + NX)` with `|z| = 1`, then `XXᴴ = (T + NX)(T + NX)ᴴ`, expanded. -/
theorem mul_conj_of_fixed (X T N : Matrix ι ι ℂ) (z : ℂ) (hz : z * star z = 1)
    (h : X = z • (T + N * X)) :
    X * Xᴴ = T * Tᴴ + T * (Xᴴ * Nᴴ) + N * (X * Tᴴ) + N * (X * Xᴴ * Nᴴ) := by
  have e : X * Xᴴ = (T + N * X) * (T + N * X)ᴴ := by
    calc X * Xᴴ = (z • (T + N * X)) * (z • (T + N * X))ᴴ := by rw [← h]
      _ = (z * star z) • ((T + N * X) * (T + N * X)ᴴ) := by
          rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = _ := by rw [hz, one_smul]
  calc X * Xᴴ = (T + N * X) * (T + N * X)ᴴ := e
    _ = (T + N * X) * (Tᴴ + Xᴴ * Nᴴ) := by rw [conjTranspose_add, conjTranspose_mul]
    _ = _ := by noncomm_ring

theorem closingX_mul_conj (hU : ∀ θ, IsUnit (1 - phase θ • closingN S A Pi).det) (θ : ℝ) :
    closingX S A Pi θ * (closingX S A Pi θ)ᴴ =
      closingT S A Pi * (closingT S A Pi)ᴴ +
        closingT S A Pi * ((closingX S A Pi θ)ᴴ * (closingN S A Pi)ᴴ) +
        closingN S A Pi * (closingX S A Pi θ * (closingT S A Pi)ᴴ) +
        closingN S A Pi * (closingX S A Pi θ * (closingX S A Pi θ)ᴴ * (closingN S A Pi)ᴴ) :=
  mul_conj_of_fixed _ _ _ _ (phase_mul_star θ) (closingX_fixed hU θ)

/-- **Hardy-series identity** `E_z XXᴴ = A`, i.e. `Σ_k r^k t t* (r*)^k = I`. -/
theorem phaseAvg_closingX_mul (hA2 : A * A = A) (hAH : Aᴴ = A) (hPi : Pi * Piᴴ = A)
    (hS : S * Sᴴ = 1) (hN : Tendsto (fun n => closingN S A Pi ^ n) atTop (𝓝 0)) :
    phaseAvg (fun θ => closingX S A Pi θ * (closingX S A Pi θ)ᴴ) = A := by
  have hU : ∀ θ, IsUnit (1 - phase θ • closingN S A Pi).det :=
    fun θ => isUnit_det_of_tendsto hN (norm_phase θ)
  have hX := continuous_closingX hU
  have h0 := phaseAvg_closingX hN
  set N := closingN S A Pi
  set T := closingT S A Pi
  set Y := phaseAvg (fun θ => closingX S A Pi θ * (closingX S A Pi θ)ᴴ)
  have hXX : Continuous fun θ => closingX S A Pi θ * (closingX S A Pi θ)ᴴ :=
    hX.matrix_mul hX.matrix_conjTranspose
  have hY : Y = T * Tᴴ + N * Y * Nᴴ := by
    have hfun : (fun θ => closingX S A Pi θ * (closingX S A Pi θ)ᴴ) = fun θ =>
        T * Tᴴ + T * ((closingX S A Pi θ)ᴴ * Nᴴ) + N * (closingX S A Pi θ * Tᴴ) +
          N * (closingX S A Pi θ * (closingX S A Pi θ)ᴴ * Nᴴ) :=
      funext (closingX_mul_conj hU)
    have h1 : Y = phaseAvg (fun θ =>
        T * Tᴴ + T * ((closingX S A Pi θ)ᴴ * Nᴴ) + N * (closingX S A Pi θ * Tᴴ) +
          N * (closingX S A Pi θ * (closingX S A Pi θ)ᴴ * Nᴴ)) := by rw [← hfun]
    conv_lhs => rw [h1]
    rw [phaseAvg_add (by fun_prop) (continuous_const.matrix_mul (hXX.matrix_mul continuous_const)),
      phaseAvg_add (by fun_prop) (continuous_const.matrix_mul (hX.matrix_mul continuous_const)),
      phaseAvg_add continuous_const
        (continuous_const.matrix_mul (hX.matrix_conjTranspose.matrix_mul continuous_const)),
      phaseAvg_const, phaseAvg_mul_left _ (hX.matrix_conjTranspose.matrix_mul continuous_const),
      phaseAvg_mul_right _ hX.matrix_conjTranspose, phaseAvg_conjTranspose, h0,
      phaseAvg_mul_left _ (hX.matrix_mul continuous_const), phaseAvg_mul_right _ hX, h0,
      phaseAvg_mul_left _ (hXX.matrix_mul continuous_const), phaseAvg_mul_right _ hXX]
    simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_assoc]
    rfl
  have hZ : Y - A = N * (Y - A) * Nᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, closingN_mul_proj hA2]
    conv_lhs => rw [hY, closingT_mul_conj hA2 hAH hPi hS]
    abel
  have hZn : ∀ n : ℕ, Y - A = N ^ n * (Y - A) * (N ^ n)ᴴ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc Y - A = N ^ n * (N * (Y - A) * Nᴴ) * (N ^ n)ᴴ := by rw [← hZ, ← ih]
        _ = N ^ (n + 1) * (Y - A) * (N ^ (n + 1))ᴴ := by
          rw [pow_succ, conjTranspose_mul]
          simp only [Matrix.mul_assoc]
  have hc : Continuous fun P : Matrix ι ι ℂ => P * (Y - A) * Pᴴ :=
    (continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_conjTranspose
  have ht := (hc.tendsto 0).comp hN
  simp only [Function.comp_def, Matrix.zero_mul] at ht
  have hconst : (fun n => N ^ n * (Y - A) * (N ^ n)ᴴ) = fun _ => Y - A :=
    funext fun n => (hZn n).symm
  rw [hconst] at ht
  exact sub_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds ht)

/-- **The Gaussian closing error, covariance form**: `E_z (C(z) - 1)(C(z) - 1)ᴴ = 2A`. For a
source map `F` and an independent `h ~ CN(0, I)` this gives
`E_{z,h} ‖F C(z) h - F h‖² = 2 Tr(F A Fᴴ)`. -/
theorem phaseAvg_closingDefect (hA2 : A * A = A) (hAH : Aᴴ = A) (hPi : Pi * Piᴴ = A)
    (hS : S * Sᴴ = 1) (hN : Tendsto (fun n => closingN S A Pi ^ n) atTop (𝓝 0)) :
    phaseAvg (fun θ => (closingMap S A Pi (phase θ) - 1) * (closingMap S A Pi (phase θ) - 1)ᴴ) =
      (2 : ℂ) • A := by
  have hU : ∀ θ, IsUnit (1 - phase θ • closingN S A Pi).det :=
    fun θ => isUnit_det_of_tendsto hN (norm_phase θ)
  have hX := continuous_closingX hU
  have e : ∀ θ, (closingMap S A Pi (phase θ) - 1) * (closingMap S A Pi (phase θ) - 1)ᴴ =
      closingX S A Pi θ * (closingX S A Pi θ)ᴴ - closingX S A Pi θ * A -
        A * (closingX S A Pi θ)ᴴ + A := by
    intro θ
    rw [closingMap_sub_one, conjTranspose_sub, hAH, sub_mul, mul_sub, mul_sub, hA2]
    abel
  simp_rw [e]
  rw [phaseAvg_add (by fun_prop) continuous_const,
    phaseAvg_sub (by fun_prop) (continuous_const.matrix_mul hX.matrix_conjTranspose),
    phaseAvg_sub (hX.matrix_mul hX.matrix_conjTranspose) (hX.matrix_mul continuous_const),
    phaseAvg_closingX_mul hA2 hAH hPi hS hN, phaseAvg_mul_right _ hX,
    phaseAvg_mul_left _ hX.matrix_conjTranspose, phaseAvg_conjTranspose, phaseAvg_closingX hN,
    phaseAvg_const, two_smul]
  simp

end BlockBand.SourceProcess.Closing
