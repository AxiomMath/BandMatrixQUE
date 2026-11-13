module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneSTwoBounds

/-!
# The uniform gap and the theta-one CEH `s₂` bound

The regular boundary window controls the ordinary denominator `|1-a|`, while
the generic feedback estimate used by `sTwo_one_le_sqrt_of_feedbackGap`
requires the radial gap `1-|a|`. These are not quantitatively interchangeable,
even under the strict bound `|a|<1`. This file records the exact
obstruction and proves the dimension-free Gamma and regularized-observable norm
bounds that do follow from the regular-window data.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
open CEHNative.BlockBand
open CEHNative.BlockBand.CEH

/-- Exact obstruction to transferring ordinary stability to a radial feedback
gap.  The feedback is strictly inside the unit disk and its ordinary
stability denominator is uniformly at least one, but its radial gap is exactly
`ε` and hence may be arbitrarily small. -/
theorem ordinaryStability_does_not_control_feedbackGap
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    let a : ℂ := (-(1 - ε : ℝ) : ℝ)
    ‖a‖ < 1 ∧
      1 ≤ ‖stabilityDenominator (1 : ℂ) a‖ ∧
      1 - ‖a‖ = ε := by
  dsimp only
  have hpos : 0 < 1 - ε := sub_pos.mpr hε1
  rw [show ‖((-(1 - ε : ℝ) : ℝ) : ℂ)‖ = 1 - ε by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg]
    · ring
    · linarith]
  constructor
  · linarith
  constructor
  · rw [show stabilityDenominator (1 : ℂ)
        ((-(1 - ε : ℝ) : ℝ) : ℂ) = ((2 - ε : ℝ) : ℂ) by
      simp [stabilityDenominator]
      ring]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 2 - ε)]
    linarith
  · ring

/-- Taking the matrix imaginary part does not increase the `L²` operator norm. -/
theorem norm_matrixImaginaryPart_le {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖CEHNative.BlockBand.matrixImaginaryPart M‖ ≤ ‖M‖ := by
  unfold CEHNative.BlockBand.matrixImaginaryPart
  rw [norm_smul]
  have hsub : ‖M - Mᴴ‖ ≤ 2 * ‖M‖ := by
    calc
      ‖M - Mᴴ‖ ≤ ‖M‖ + ‖Mᴴ‖ := norm_sub_le _ _
      _ = 2 * ‖M‖ := by rw [Matrix.l2_opNorm_conjTranspose]; ring
  have hscalar : ‖-Complex.I / 2‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [hscalar]
  nlinarith [norm_nonneg M]

/-- Dimension-free Gamma bound from the density and matrix-norm
bounds in a regular window. -/
theorem norm_gammaMatrix_le_of_traceImaginaryPart
    {N : ℕ} (_hN : 0 < N) (M : Matrix (Fin N) (Fin N) ℂ)
    {c K : ℝ} (hc : 0 < c)
    (htrace : c ≤ |(NTrace M).im|) (hM : ‖M‖ ≤ K) :
    ‖gammaMatrix M‖ ≤ c⁻¹ * K := by
  have hNt : NTrace
      (CEHNative.BlockBand.matrixImaginaryPart M) =
      (((NTrace M).im : ℝ) : ℂ) := by
    simp [NTrace, CEHNative.BlockBand.Conventions.normalizedTrace,
      CEHNative.BlockBand.trace_matrixImaginaryPart,
      Complex.mul_im]
  unfold gammaMatrix
  rw [norm_smul, hNt, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hcabs : 0 < |(NTrace M).im| := hc.trans_le htrace
  calc
    |(NTrace M).im|⁻¹ *
          ‖CEHNative.BlockBand.matrixImaginaryPart M‖
        ≤ |(NTrace M).im|⁻¹ * ‖M‖ := by
          gcongr
          exact norm_matrixImaginaryPart_le M
    _ ≤ c⁻¹ * K := by
      exact mul_le_mul (inv_anti₀ hc htrace) hM (norm_nonneg _) (by positivity)

/-- The theta-one regularized observable is uniformly bounded once the mixed
pairing and the three source operator norms are bounded. -/
theorem norm_regularizedObservable_one_le {N : ℕ} (hN : 0 < N)
    (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ)
    {L R p : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hp : 0 < p)
    (hM₁ : ‖M₁‖ ≤ L) (hM₂ : ‖M₂‖ ≤ L) (hA : ‖A‖ ≤ R)
    (hpair : p ≤ ‖NTrace (M₁ * M₂)‖) :
    ‖regularizedObservable 1 M₁ M₂ A‖ ≤
      R + (L * R * L / p) := by
  unfold regularizedObservable
  simp only [Complex.ofReal_one, one_mul]
  apply (norm_sub_le _ _).trans
  let _ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hone : ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ = 1 := by
    rw [show (1 : Matrix (Fin N) (Fin N) ℂ) =
        Matrix.diagonal (fun _ => (1 : ℂ)) by ext i j; simp]
    rw [Matrix.l2_opNorm_diagonal]
    simp [Pi.norm_def, Finset.sup_const, Finset.univ_nonempty]
  rw [norm_smul, hone, mul_one]
  apply add_le_add hA
  rw [norm_div]
  apply (div_le_div₀ (by positivity)
    (norm_NTrace_three_mul_le hN M₁ A M₂) hp hpair).trans
  gcongr

end CEHNative.BlockBand.External.CEH
