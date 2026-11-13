module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.CyclicResolventDecay
public import Mathlib

/-!
# Quantitative normalization of the cyclic resolvent jump

The source jump of the nearest-neighbour recurrence is the square root, up to
sign, of its characteristic discriminant.  Factoring that discriminant gives
a lower bound at the square-root radial-margin scale with a constant depending
only on the fixed bond weight.  Combining it with the contracting-root gap
removes the final unspecified denominator from the cyclic Green estimate.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERJumpNormalization

open ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERCharacterAngle ERNearestNeighbor ERCyclicDecay ERHerglotz

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Fixed-bond transverse discriminant margin.  It is positive for every
source parameter `0 < b < 1/2` and is independent of `n`, `W`, and parity. -/
def jumpBondMargin (p : Params) : ℝ :=
  1 - |p.c - 2 * p.b|

/-- The second characteristic factor stays uniformly away from zero by the
fixed-bond margin. -/
theorem jumpBondMargin_pos (p : Params) : 0 < jumpBondMargin p := by
  unfold jumpBondMargin
  rw [sub_pos, abs_lt]
  constructor <;> linarith [p.c_pos, p.b_pos, p.c_add_two_b]

/-- Exact factorization of the characteristic discriminant. -/
theorem recurrenceDiscriminant_factor (p : Params) (α : ℂ) :
    recurrenceDiscriminant p α =
      (1 - α) * (1 - α * ((p.c - 2 * p.b : ℝ) : ℂ)) := by
  unfold recurrenceDiscriminant recurrenceDiagonal recurrenceBond
  have hc : (p.c : ℂ) + 2 * p.b = 1 := by
    exact_mod_cast p.c_add_two_b
  have hc' : (p.c : ℂ) = 1 - 2 * p.b := by
    linear_combination hc
  push_cast
  rw [hc']
  ring

/-- For any nonzero characteristic root, the square of the exact source jump
is the recurrence discriminant. -/
theorem recurrenceJump_sq_eq_discriminant (p : Params) {α ρ : ℂ}
    (hρ0 : ρ ≠ 0)
    (hchar : recurrenceBond p α * ρ ^ 2 -
      recurrenceDiagonal p α * ρ + recurrenceBond p α = 0) :
    recurrenceJump p α ρ ^ 2 = recurrenceDiscriminant p α := by
  have hdiag : recurrenceDiagonal p α =
      recurrenceBond p α * (ρ + ρ⁻¹) := by
    apply (mul_right_cancel₀ hρ0)
    field_simp [hρ0]
    linear_combination -hchar
  unfold recurrenceJump recurrenceDiscriminant
  rw [hdiag]
  field_simp [hρ0]
  ring

/-- Reverse triangle inequality in the form needed for each discriminant
factor. -/
theorem one_sub_norm_le_norm_one_sub (z : ℂ) :
    1 - ‖z‖ ≤ ‖1 - z‖ := by
  simpa [sub_eq_add_neg] using (norm_sub_le_norm_add (1 : ℂ) (-z))

/-- The noncritical discriminant factor has the fixed positive lower bound
`1-|c-2b|`, uniformly over the open multiplier disk. -/
theorem jumpBondMargin_le_secondFactor (p : Params) {α : ℂ}
    (hα : ‖α‖ < 1) :
    jumpBondMargin p ≤
      ‖1 - α * ((p.c - 2 * p.b : ℝ) : ℂ)‖ := by
  let q : ℝ := p.c - 2 * p.b
  have hq0 : 0 ≤ |q| := abs_nonneg q
  have hαle : ‖α‖ ≤ 1 := hα.le
  have hnormq : ‖((q : ℝ) : ℂ)‖ = |q| := by simp
  have htri := one_sub_norm_le_norm_one_sub (α * ((q : ℝ) : ℂ))
  rw [norm_mul, hnormq] at htri
  unfold jumpBondMargin
  dsimp only [q] at htri ⊢
  nlinarith [norm_nonneg α]

/-- Quantitative lower bound for the exact source jump.  Its square is bounded
below by the radial margin times a strictly positive fixed-bond margin. -/
theorem radialMargin_mul_jumpBondMargin_le_jump_sq (p : Params) {α ρ : ℂ}
    (hα : ‖α‖ < 1) (hρ0 : ρ ≠ 0)
    (hchar : recurrenceBond p α * ρ ^ 2 -
      recurrenceDiagonal p α * ρ + recurrenceBond p α = 0) :
    (1 - ‖α‖) * jumpBondMargin p ≤ ‖recurrenceJump p α ρ‖ ^ 2 := by
  have hfirst := one_sub_norm_le_norm_one_sub α
  have hsecond := jumpBondMargin_le_secondFactor p hα
  have hδ : 0 ≤ 1 - ‖α‖ := by linarith
  have hκ : 0 ≤ jumpBondMargin p := (jumpBondMargin_pos p).le
  have hmul := mul_le_mul hfirst hsecond hκ (norm_nonneg (1 - α))
  have hsq := recurrenceJump_sq_eq_discriminant p hρ0 hchar
  calc
    (1 - ‖α‖) * jumpBondMargin p ≤
        ‖1 - α‖ * ‖1 - α * ((p.c - 2 * p.b : ℝ) : ℂ)‖ := hmul
    _ = ‖recurrenceDiscriminant p α‖ := by
      rw [recurrenceDiscriminant_factor, norm_mul]
    _ = ‖recurrenceJump p α ρ ^ 2‖ := by rw [hsq]
    _ = ‖recurrenceJump p α ρ‖ ^ 2 := norm_pow _ _

/-- Square-root form of the quantitative jump lower bound. -/
theorem sqrt_radialMargin_mul_jumpBondMargin_le_jump (p : Params)
    {α ρ : ℂ} (hα : ‖α‖ < 1) (hρ0 : ρ ≠ 0)
    (hchar : recurrenceBond p α * ρ ^ 2 -
      recurrenceDiagonal p α * ρ + recurrenceBond p α = 0) :
    Real.sqrt ((1 - ‖α‖) * jumpBondMargin p) ≤
      ‖recurrenceJump p α ρ‖ := by
  have hprod : 0 ≤ (1 - ‖α‖) * jumpBondMargin p :=
    mul_nonneg (by linarith) (jumpBondMargin_pos p).le
  rw [Real.sqrt_le_iff]
  exact ⟨norm_nonneg _, radialMargin_mul_jumpBondMargin_le_jump_sq p hα hρ0 hchar⟩

/-- The selected contracting root satisfies the unconditional quantitative
jump bound whenever the multiplier is nonzero. -/
theorem sqrt_margin_le_contractingRecurrenceJump (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1) :
    Real.sqrt ((1 - ‖α‖) * jumpBondMargin p) ≤
      ‖recurrenceJump p α (contractingRecurrenceRoot p α)‖ := by
  exact sqrt_radialMargin_mul_jumpBondMargin_le_jump p hα
    (contractingRecurrenceRoot_ne_zero p hα0)
    (contractingRecurrenceRoot_characteristic p hα0)

/-- Elementary two-regime exponential inequality.  It is the numerical input
for retaining the finite-cycle gain when `n(1-|ρ|)` is small. -/
theorem min_expOneGap_half_mul_le_one_sub_exp_neg {t : ℝ} (ht : 0 ≤ t) :
    min (1 - Real.exp (-1)) (t / 2) ≤ 1 - Real.exp (-t) := by
  by_cases ht1 : t ≤ 1
  · have hexp : Real.exp (-t) ≤ 1 / (1 + t) := by
      rw [Real.exp_neg]
      simpa [one_div, add_comm] using
        (one_div_le_one_div_of_le (by linarith)
          (Real.add_one_le_exp t))
    have hrat : 1 / (1 + t) ≤ 1 - t / 2 := by
      apply (div_le_iff₀ (by linarith : 0 < 1 + t)).2
      nlinarith [sq_nonneg t]
    exact le_trans (min_le_right _ _) (by linarith)
  · have ht1' : 1 ≤ t := le_of_not_ge ht1
    have hexp : Real.exp (-t) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (by linarith)
    exact le_trans (min_le_left _ _) (by linarith)

/-- Sharper wraparound normalization.  It interpolates between the short-ring
regime `n(1-|ρ|)` and the saturated regime, rather than discarding the factor
of `n` as the cruder bound `1-|ρ|` does. -/
theorem min_wrapScale_le_norm_one_sub_pow (p : Params) {ρ : ℂ}
    (hρ : ‖ρ‖ < 1) :
    min (1 - Real.exp (-1)) (((p.n : ℝ) * (1 - ‖ρ‖)) / 2) ≤
      ‖1 - ρ ^ p.n‖ := by
  let t : ℝ := (p.n : ℝ) * (1 - ‖ρ‖)
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hmin := min_expOneGap_half_mul_le_one_sub_exp_neg ht
  have hpow := pow_le_exp_neg_gap (norm_nonneg ρ) p.n
  have hpow' : ‖ρ‖ ^ p.n ≤ Real.exp (-t) := by
    dsimp only [t]
    convert hpow using 1
    ring_nf
  have hreverse := one_sub_norm_le_norm_one_sub (ρ ^ p.n)
  rw [norm_pow] at hreverse
  dsimp only [t] at hmin
  exact hmin.trans ((by linarith) :
    1 - Real.exp (-t) ≤ ‖1 - ρ ^ p.n‖)

/-- Explicit root-gap rate used in the spatial estimate. -/
def rootGapRate (p : Params) (α : ℂ) : ℝ :=
  min (1 / 2 : ℝ) (Real.sqrt ((1 - ‖α‖) / (2 * p.b)))

/-- Explicit lower scale for the recurrence source jump. -/
def jumpLowerScale (p : Params) (α : ℂ) : ℝ :=
  Real.sqrt ((1 - ‖α‖) * jumpBondMargin p)

/-- Both explicit scales are strictly positive inside the multiplier disk. -/
theorem rootGapRate_pos (p : Params) {α : ℂ} (hα : ‖α‖ < 1) :
    0 < rootGapRate p α := by
  unfold rootGapRate
  apply lt_min (by norm_num)
  apply Real.sqrt_pos.2
  exact div_pos (by linarith) (mul_pos (by norm_num) p.b_pos)

/-- The sharper wrap scale specialized to the selected root.  In particular,
the cyclic denominator is of order `n γ` before saturation and of fixed order
after saturation, uniformly for even and odd rings. -/
theorem min_rootGap_wrapScale_le_contracting_denominator
    (p : Params) {α : ℂ} (hα0 : α ≠ 0) (hα : ‖α‖ < 1) :
    min (1 - Real.exp (-1))
        (((p.n : ℝ) * rootGapRate p α) / 2) ≤
      ‖1 - contractingRecurrenceRoot p α ^ p.n‖ := by
  have hρ :=
    norm_contractingRecurrenceRoot_lt_one p hα0 hα
  have hwrap :=
    min_wrapScale_le_norm_one_sub_pow p hρ
  have hgap :=
    min_half_sqrt_radialMargin_le_root_gap p hα0 hα
  change rootGapRate p α ≤
    1 - ‖contractingRecurrenceRoot p α‖ at hgap
  apply le_trans (min_le_min le_rfl ?_) hwrap
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg _)) (by norm_num)

/-- The jump lower scale is positive inside the multiplier disk. -/
theorem jumpLowerScale_pos (p : Params) {α : ℂ} (hα : ‖α‖ < 1) :
    0 < jumpLowerScale p α := by
  unfold jumpLowerScale
  exact Real.sqrt_pos.2 (mul_pos (by linarith) (jumpBondMargin_pos p))

/-- The Dyson equation supplies the source-domain lower bound omitted by the
unit-disk estimate: on `‖z‖ ≤ C₀`, the semicircle transform has norm at least
`(1+C₀)⁻¹`. -/
theorem one_div_one_add_le_norm_erSemicircleStieltjes {z : ℂ} {C₀ : ℝ}
    (hz : z.im ≠ 0) (hC₀ : 0 ≤ C₀) (hzC₀ : ‖z‖ ≤ C₀) :
    1 / (1 + C₀) ≤ ‖erSemicircleStieltjes z‖ := by
  let m := erSemicircleStieltjes z
  have hdyson := erSemicircleStieltjes_dyson z
  have heq : (1 : ℂ) = -(m * (m + z)) := by
    dsimp only [m]
    calc
      (1 : ℂ) = -(erSemicircleStieltjes z ^ 2 +
          z * erSemicircleStieltjes z) := by
        linear_combination hdyson
      _ = -(erSemicircleStieltjes z *
          (erSemicircleStieltjes z + z)) := by ring
  have hnormeq : 1 = ‖m‖ * ‖m + z‖ := by
    have := congrArg norm heq
    simpa [norm_mul] using this
  have hm : ‖m‖ < 1 := norm_erSemicircleStieltjes_lt_one hz
  have hadd : ‖m + z‖ ≤ 1 + C₀ :=
    (norm_add_le m z).trans (by linarith)
  have hprod : 1 ≤ ‖m‖ * (1 + C₀) :=
    hnormeq.le.trans
      (mul_le_mul_of_nonneg_left hadd (norm_nonneg m))
  apply (div_le_iff₀ (by linarith : 0 < 1 + C₀)).2
  simpa [mul_comm] using hprod

/-- Hence a corrected same-half-plane Θ multiplier has the explicit lower
bound `(1+C₀)⁻²` on the ER norm-cutoff domain. -/
theorem one_div_one_add_sq_le_norm_thetaMultiplier
    {z₁ z₂ : ℂ} {C₀ : ℝ}
    (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0)
    (hC₀ : 0 ≤ C₀) (hz₁ : ‖z₁‖ ≤ C₀) (hz₂ : ‖z₂‖ ≤ C₀) :
    1 / (1 + C₀) ^ 2 ≤
      ‖erSemicircleStieltjes z₁ *
        starRingEnd ℂ (erSemicircleStieltjes z₂)‖ := by
  have hm₁ :=
    one_div_one_add_le_norm_erSemicircleStieltjes h₁ hC₀ hz₁
  have hm₂ :=
    one_div_one_add_le_norm_erSemicircleStieltjes h₂ hC₀ hz₂
  rw [norm_mul, Complex.norm_conj]
  have hden : 0 ≤ 1 / (1 + C₀) := by positivity
  have hmul := mul_le_mul hm₁ hm₂ hden (norm_nonneg _)
  simpa [one_div, pow_two] using hmul

/-- At multiplier zero the scalar inverse kernel is exactly the cyclic point
mass, so no singular recurrence-root normalization is needed. -/
theorem fourierGreenKernel_zero (p : Params) (x y : ZMod p.n) :
    fourierGreenKernel p 0 x y = cyclicDelta y x := by
  have h := ERCharacterAngle.scalarStabilityInverse_physical_right p
    (show ‖(0 : ℂ)‖ < 1 by norm_num) (cyclicDelta y)
  have hx := congrFun h x
  simp [physicalStabilityOperator] at hx
  rw [← scalarStabilityInverse_cyclicDelta p 0 x y]
  exact hx

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERJumpNormalization
