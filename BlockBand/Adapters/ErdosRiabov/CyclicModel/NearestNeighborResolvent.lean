module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.HerglotzCompatibility
public import Mathlib

/-!
# Physical nearest-neighbour resolvent identities

This module starts the spatial part of the corrected Erdős–Riabov analysis.  It
derives the exact inhomogeneous three-term recurrence satisfied by the Fourier
Green kernel and identifies the full-site tensor Green kernel.  These are
physical-operator identities, not Fourier-coordinate certificates.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERNearestNeighbor

open scoped BigOperators
open ERProfile ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERGreenConvolution ERCharacterAngle ERHerglotz

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Kronecker delta on the cyclic block ring. -/
def cyclicDelta {n : ℕ} (y x : ZMod n) : ℂ := if x = y then 1 else 0

@[simp] theorem cyclicDelta_self {n : ℕ} (x : ZMod n) :
    cyclicDelta x x = 1 := by
  simp [cyclicDelta]

@[simp] theorem cyclicDelta_apply {n : ℕ} (x y : ZMod n) :
    cyclicDelta y x = if x = y then 1 else 0 := rfl

/-- Multiplication by the complex cyclic covariance is exactly the physical
three-point stencil. -/
theorem complexCyclicCovariance_mulVec_stencil (p : Params)
    (f : ZMod p.n → ℂ) (x : ZMod p.n) :
    (complexCyclicCovariance p).mulVec f x =
      (p.c : ℂ) * f x + p.b * f (x + 1) + p.b * f (x - 1) := by
  simp [complexCyclicCovariance, Matrix.mulVec, dotProduct,
    Finset.sum_add_distrib, add_mul]

/-- Pointwise nearest-neighbour formula for the physical stability operator. -/
theorem physicalStabilityOperator_stencil (p : Params) (α : ℂ)
    (f : ZMod p.n → ℂ) (x : ZMod p.n) :
    physicalStabilityOperator p α f x =
      f x - α * ((p.c : ℂ) * f x +
        p.b * f (x + 1) + p.b * f (x - 1)) := by
  rw [physicalStabilityOperator, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  change f x - α * (complexCyclicCovariance p).mulVec f x = _
  rw [complexCyclicCovariance_mulVec_stencil]

/-- Applying the Fourier Green convolution to a point mass selects the
corresponding Green-kernel column, with no hidden normalization. -/
theorem scalarStabilityInverse_cyclicDelta (p : Params) (α : ℂ)
    (x y : ZMod p.n) :
    scalarStabilityInverse p α (cyclicDelta y) x =
      fourierGreenKernel p α x y := by
  rw [scalarStabilityInverse_eq_green_convolution]
  simp [cyclicDelta]

/-- Diagonal coefficient in the homogeneous resolvent recurrence. -/
def recurrenceDiagonal (p : Params) (α : ℂ) : ℂ :=
  1 - α * p.c

/-- Nearest-neighbour coefficient in the homogeneous resolvent recurrence. -/
def recurrenceBond (p : Params) (α : ℂ) : ℂ :=
  α * p.b

/-- Characteristic discriminant of the nearest-neighbour recurrence. -/
def recurrenceDiscriminant (p : Params) (α : ℂ) : ℂ :=
  recurrenceDiagonal p α ^ 2 - 4 * recurrenceBond p α ^ 2

/-- The two algebraic characteristic roots.  The formula is used only under a
nonzero bond coefficient; the zero-multiplier Green kernel is already the
identity kernel. -/
def recurrenceRoot (p : Params) (α : ℂ) (sign : ℂ) : ℂ :=
  (recurrenceDiagonal p α +
    sign * Complex.sqrt (recurrenceDiscriminant p α)) /
      (2 * recurrenceBond p α)

/-- Each sign `±1` produces a solution of the exact characteristic equation.
This is the algebraic starting point for choosing and estimating the contracting
root in the spatial-decay argument. -/
theorem recurrenceRoot_characteristic (p : Params) {α sign : ℂ}
    (hbond : recurrenceBond p α ≠ 0) (hsign : sign ^ 2 = 1) :
    recurrenceBond p α * recurrenceRoot p α sign ^ 2 -
        recurrenceDiagonal p α * recurrenceRoot p α sign +
        recurrenceBond p α = 0 := by
  have hsqrt :
      Complex.sqrt (recurrenceDiscriminant p α) ^ 2 =
        recurrenceDiscriminant p α := by
    simp [Complex.sqrt]
  unfold recurrenceRoot
  field_simp [hbond]
  ring_nf
  rw [hsign, hsqrt]
  unfold recurrenceDiscriminant
  ring

/-- The two characteristic roots are reciprocal.  This identity handles real
and complex multipliers uniformly and isolates the subsequent analytic task:
selecting the unique root inside the unit disk. -/
theorem recurrenceRoot_mul_neg (p : Params) {α sign : ℂ}
    (hbond : recurrenceBond p α ≠ 0) (hsign : sign ^ 2 = 1) :
    recurrenceRoot p α sign * recurrenceRoot p α (-sign) = 1 := by
  have hsqrt :
      Complex.sqrt (recurrenceDiscriminant p α) ^ 2 =
        recurrenceDiscriminant p α := by
    simp [Complex.sqrt]
  unfold recurrenceRoot
  field_simp [hbond]
  ring_nf
  rw [hsign, hsqrt]
  unfold recurrenceDiscriminant
  ring

/-- A characteristic root cannot lie on the unit circle when the stability
multiplier is strictly inside the unit disk.  The proof uses only the sharp
stochastic identity `c+2b=1`. -/
theorem characteristic_root_norm_ne_one (p : Params) {α ρ : ℂ}
    (hα : ‖α‖ < 1)
    (hchar : recurrenceBond p α * ρ ^ 2 -
        recurrenceDiagonal p α * ρ + recurrenceBond p α = 0) :
    ‖ρ‖ ≠ 1 := by
  intro hρnorm
  have hρ : ρ ≠ 0 := by
    intro h
    subst ρ
    norm_num at hρnorm
  have hrec :
      recurrenceDiagonal p α =
        recurrenceBond p α * (ρ + ρ⁻¹) := by
    apply (mul_right_cancel₀ hρ)
    field_simp [hρ]
    linear_combination -hchar
  have hone :
      (1 : ℂ) = α * ((p.c : ℂ) + p.b * ρ + p.b * ρ⁻¹) := by
    rw [show (1 : ℂ) =
        recurrenceDiagonal p α + α * p.c by
      unfold recurrenceDiagonal
      ring, hrec]
    unfold recurrenceBond
    ring
  have hρinvnorm : ‖ρ⁻¹‖ = 1 := by
    rw [norm_inv, hρnorm, inv_one]
  have hsymbol :
      ‖(p.c : ℂ) + p.b * ρ + p.b * ρ⁻¹‖ ≤ 1 := by
    calc
      ‖(p.c : ℂ) + p.b * ρ + p.b * ρ⁻¹‖ ≤
          ‖(p.c : ℂ) + p.b * ρ‖ + ‖(p.b : ℂ) * ρ⁻¹‖ :=
        norm_add_le _ _
      _ ≤
          ‖(p.c : ℂ)‖ + ‖(p.b : ℂ) * ρ‖ + ‖(p.b : ℂ) * ρ⁻¹‖ := by
        gcongr
        exact norm_add_le _ _
      _ = p.c + 2 * p.b := by
        rw [norm_mul, norm_mul, hρnorm, hρinvnorm]
        simp [abs_of_pos p.c_pos, abs_of_pos p.b_pos]
        ring
      _ = 1 := p.c_add_two_b
  have hnormone := congrArg norm hone
  rw [norm_one, norm_mul] at hnormone
  nlinarith [norm_nonneg α,
    norm_nonneg ((p.c : ℂ) + p.b * ρ + p.b * ρ⁻¹)]

/-- The contracting characteristic root, selected without imposing a branch
choice on the complex square root. -/
def contractingRecurrenceRoot (p : Params) (α : ℂ) : ℂ :=
  let r := recurrenceRoot p α 1
  if ‖r‖ < 1 then r else recurrenceRoot p α (-1)

/-- For every nonzero multiplier in the open unit disk, the selected
characteristic root is strictly contracting. -/
theorem norm_contractingRecurrenceRoot_lt_one (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1) :
    ‖contractingRecurrenceRoot p α‖ < 1 := by
  have hb : recurrenceBond p α ≠ 0 := by
    unfold recurrenceBond
    exact mul_ne_zero hα0 (by exact_mod_cast ne_of_gt p.b_pos)
  let rp := recurrenceRoot p α 1
  let rm := recurrenceRoot p α (-1)
  have hpchar :
      recurrenceBond p α * rp ^ 2 -
          recurrenceDiagonal p α * rp + recurrenceBond p α = 0 := by
    dsimp only [rp]
    apply recurrenceRoot_characteristic p hb
    norm_num
  have hmchar :
      recurrenceBond p α * rm ^ 2 -
          recurrenceDiagonal p α * rm + recurrenceBond p α = 0 := by
    dsimp only [rm]
    apply recurrenceRoot_characteristic p hb
    norm_num
  have hpne : ‖rp‖ ≠ 1 :=
    characteristic_root_norm_ne_one p hα hpchar
  have hmne : ‖rm‖ ≠ 1 :=
    characteristic_root_norm_ne_one p hα hmchar
  have hprod : rp * rm = 1 := by
    dsimp only [rp, rm]
    simpa using recurrenceRoot_mul_neg p hb (by norm_num : (1 : ℂ) ^ 2 = 1)
  have hnormprod : ‖rp‖ * ‖rm‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  unfold contractingRecurrenceRoot
  dsimp only [rp, rm]
  split
  · assumption
  · rename_i hpnot
    have hpgt : 1 < ‖rp‖ := lt_of_le_of_ne (le_of_not_gt hpnot) hpne.symm
    have hrmnonneg := norm_nonneg rm
    nlinarith

/-- The selected contracting root still satisfies the characteristic equation. -/
theorem contractingRecurrenceRoot_characteristic (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) :
    recurrenceBond p α * contractingRecurrenceRoot p α ^ 2 -
        recurrenceDiagonal p α * contractingRecurrenceRoot p α +
        recurrenceBond p α = 0 := by
  have hb : recurrenceBond p α ≠ 0 := by
    unfold recurrenceBond
    exact mul_ne_zero hα0 (by exact_mod_cast ne_of_gt p.b_pos)
  simp only [contractingRecurrenceRoot]
  split
  · apply recurrenceRoot_characteristic p hb
    norm_num
  · apply recurrenceRoot_characteristic p hb
    norm_num

/-- A contracting characteristic root cannot vanish when the nearest-neighbour
coefficient is nonzero. -/
theorem contractingRecurrenceRoot_ne_zero (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) :
    contractingRecurrenceRoot p α ≠ 0 := by
  intro hρ
  have hchar := contractingRecurrenceRoot_characteristic p hα0
  rw [hρ] at hchar
  norm_num at hchar
  have hb : recurrenceBond p α ≠ 0 := by
    unfold recurrenceBond
    exact mul_ne_zero hα0 (by exact_mod_cast ne_of_gt p.b_pos)
  exact hb hchar

/-- Quantitative square-root radial separation of the contracting recurrence
root.  When the root has norm above `1/2`, its distance from the unit circle is
at least the square-root scale dictated by the multiplier's radial margin. -/
theorem one_sub_norm_alpha_le_two_b_mul_root_gap_sq (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1)
    (hroot : 1 / 2 < ‖contractingRecurrenceRoot p α‖) :
    1 - ‖α‖ ≤
      2 * p.b * (1 - ‖contractingRecurrenceRoot p α‖) ^ 2 := by
  let ρ := contractingRecurrenceRoot p α
  have hρ0 : ρ ≠ 0 := contractingRecurrenceRoot_ne_zero p hα0
  have hchar := contractingRecurrenceRoot_characteristic p hα0
  have hrec :
      recurrenceDiagonal p α = recurrenceBond p α * (ρ + ρ⁻¹) := by
    apply (mul_right_cancel₀ hρ0)
    field_simp [hρ0]
    linear_combination -hchar
  have hone :
      (1 : ℂ) = α * ((p.c : ℂ) + p.b * ρ + p.b * ρ⁻¹) := by
    rw [show (1 : ℂ) =
        recurrenceDiagonal p α + α * p.c by
      unfold recurrenceDiagonal
      ring, hrec]
    unfold recurrenceBond
    ring
  have hsymbol :
      ‖(p.c : ℂ) + p.b * ρ + p.b * ρ⁻¹‖ ≤
        p.c + p.b * ‖ρ‖ + p.b * ‖ρ‖⁻¹ := by
    calc
      ‖(p.c : ℂ) + p.b * ρ + p.b * ρ⁻¹‖ ≤
          ‖(p.c : ℂ) + p.b * ρ‖ + ‖(p.b : ℂ) * ρ⁻¹‖ :=
        norm_add_le _ _
      _ ≤ ‖(p.c : ℂ)‖ + ‖(p.b : ℂ) * ρ‖ +
          ‖(p.b : ℂ) * ρ⁻¹‖ := by
        gcongr
        exact norm_add_le _ _
      _ = p.c + p.b * ‖ρ‖ + p.b * ‖ρ‖⁻¹ := by
        rw [norm_mul, norm_mul, norm_inv]
        simp [abs_of_pos p.c_pos, abs_of_pos p.b_pos]
  have hnormeq : 1 =
      ‖α‖ * ‖(p.c : ℂ) + p.b * ρ + p.b * ρ⁻¹‖ := by
    have := congrArg norm hone
    simpa using this
  have hαnonneg := norm_nonneg α
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hupper :
      1 ≤ ‖α‖ * (p.c + p.b * ‖ρ‖ + p.b * ‖ρ‖⁻¹) := by
    rw [hnormeq]
    exact mul_le_mul_of_nonneg_left hsymbol hαnonneg
  have hc : p.c = 1 - 2 * p.b := by linarith [p.c_add_two_b]
  rw [hc] at hupper
  have hinv : ‖ρ‖⁻¹ * ‖ρ‖ = 1 := inv_mul_cancel₀ (ne_of_gt hρpos)
  have hinv' : ‖ρ‖ * ‖ρ‖⁻¹ = 1 := by
    rw [mul_comm]
    exact hinv
  have hαle : ‖α‖ ≤ 1 := hα.le
  have hbpos := p.b_pos
  have hρhalf : 1 / 2 < ‖ρ‖ := hroot
  have hρlt : ‖ρ‖ < 1 := norm_contractingRecurrenceRoot_lt_one p hα0 hα
  have hupper_mul := mul_le_mul_of_nonneg_right hupper hρpos.le
  have hexpand :
      (1 - 2 * p.b + p.b * ‖ρ‖ + p.b * ‖ρ‖⁻¹) * ‖ρ‖ =
        ‖ρ‖ + p.b * (1 - ‖ρ‖) ^ 2 := by
    ring_nf
    rw [mul_assoc p.b ‖ρ‖ ‖ρ‖⁻¹, hinv', mul_one]
    ring
  rw [one_mul, mul_assoc, hexpand] at hupper_mul
  have hcore :
      (1 - ‖α‖) * ‖ρ‖ ≤
        ‖α‖ * p.b * (1 - ‖ρ‖) ^ 2 := by
    nlinarith
  calc
    1 - ‖α‖ ≤ 2 * ‖α‖ * p.b * (1 - ‖ρ‖) ^ 2 := by
      nlinarith [sq_nonneg (1 - ‖ρ‖)]
    _ ≤ 2 * p.b * (1 - ‖ρ‖) ^ 2 := by
      have hnonneg : 0 ≤ 2 * p.b * (1 - ‖ρ‖) ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) p.b_pos.le) (sq_nonneg _)
      nlinarith

/-- Explicit square-root-scale contraction of the characteristic root.  The
constant depends only on the fixed bond weight `b`, never on the ring length or
its parity. -/
theorem min_half_sqrt_radialMargin_le_root_gap (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1) :
    min (1 / 2 : ℝ) (Real.sqrt ((1 - ‖α‖) / (2 * p.b))) ≤
      1 - ‖contractingRecurrenceRoot p α‖ := by
  have hρlt := norm_contractingRecurrenceRoot_lt_one p hα0 hα
  by_cases hρ : ‖contractingRecurrenceRoot p α‖ ≤ 1 / 2
  · exact le_trans (min_le_left _ _) (by linarith)
  · have hsq := one_sub_norm_alpha_le_two_b_mul_root_gap_sq p hα0 hα
      (lt_of_not_ge hρ)
    have hden : 0 < 2 * p.b := mul_pos (by norm_num) p.b_pos
    have harg :
        (1 - ‖α‖) / (2 * p.b) ≤
          (1 - ‖contractingRecurrenceRoot p α‖) ^ 2 := by
      apply (div_le_iff₀ hden).2
      simpa [mul_comm] using hsq
    have hsqrt :
        Real.sqrt ((1 - ‖α‖) / (2 * p.b)) ≤
          1 - ‖contractingRecurrenceRoot p α‖ := by
      exact (Real.sqrt_le_left (by linarith)).2 harg
    exact le_trans (min_le_right _ _) hsqrt

/-- Exact kernel of the tensorized full-site inverse.  The first term is the
identity on within-block mean-zero vectors; the second is the normalized
block-constant Green correction. -/
def siteGreenKernel (p : Params) (α : ℂ)
    (x y : Site p.n p.W) : ℂ :=
  (if x = y then 1 else 0) +
    (fourierGreenKernel p α x.1 y.1 -
      if x.1 = y.1 then 1 else 0) / (p.W : ℂ)

/-- Block average of a physical-site point mass. -/
theorem blockAverage_pointMass (p : Params) (y : Site p.n p.W)
    (k : ZMod p.n) :
    blockAverage p (fun u => if u = y then 1 else 0) k =
      (if k = y.1 then 1 / (p.W : ℂ) else 0) := by
  by_cases hk : k = y.1
  · subst k
    have hsum :
        ∑ i : Fin p.W, (if (y.1, i) = y then (1 : ℂ) else 0) = 1 := by
      calc
        ∑ i : Fin p.W, (if (y.1, i) = y then (1 : ℂ) else 0) =
            (if (y.1, y.2) = y then 1 else 0) := by
          apply Finset.sum_eq_single y.2
          · intro j _ hj
            simp only [ite_eq_right_iff]
            intro h
            exact False.elim (hj (congrArg Prod.snd h))
          · intro h
            exact False.elim (h (Finset.mem_univ y.2))
        _ = 1 := by simp
    unfold blockAverage
    rw [hsum]
    simp
  · have hsum :
        ∑ i : Fin p.W, (if (k, i) = y then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [ite_eq_right_iff]
      intro h
      exact False.elim (hk (congrArg Prod.fst h))
    unfold blockAverage
    rw [hsum]
    simp [hk]

/-- Applying the tensorized stability inverse to a physical-site point mass
gives the explicit full-site Green kernel. -/
theorem siteStabilityInverse_pointMass (p : Params) (α : ℂ)
    (x y : Site p.n p.W) :
    siteStabilityInverse p α (fun u => if u = y then 1 else 0) x =
      siteGreenKernel p α x y := by
  have hW : (p.W : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt p.W_pos
  unfold siteStabilityInverse siteGreenKernel blockMeanZeroPart
    blockConstantPart
  rw [blockAverage_pointMass]
  rw [scalarStabilityInverse_eq_green_convolution]
  simp_rw [blockAverage_pointMass]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  by_cases hblock : x.1 = y.1 <;>
    by_cases hsite : x = y <;>
    simp [hblock, hsite] <;> field_simp <;> ring

/-- The tensorized Green kernel is a right inverse kernel, rather than
only a block-coordinate formula. -/
theorem siteGreenKernel_physical_right (p : Params) {α : ℂ}
    (hα : ‖α‖ < 1) (y : Site p.n p.W) :
    sitePhysicalStabilityOperator p α (fun x => siteGreenKernel p α x y) =
      fun x => if x = y then 1 else 0 := by
  have hright := ERCharacterAngle.siteStabilityInverse_physical_right p hα
    (fun x => if x = y then 1 else 0)
  have hkernel :
      siteStabilityInverse p α (fun x => if x = y then 1 else 0) =
        fun x => siteGreenKernel p α x y := by
    funext x
    exact siteStabilityInverse_pointMass p α x y
  simpa only [hkernel] using hright

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERNearestNeighbor
