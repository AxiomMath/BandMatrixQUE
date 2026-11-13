module
public import Mathlib

/-!
# The phase-fixed unit representative of the projective affine chart

For `z ∈ ℂ^n` the affine representative `(1, z)` is normalized to the unit vector
`(1, z)/‖(1, z)‖`, whose first coordinate is real and positive. This file computes the real
Fréchet derivatives of the affine representative, of its squared norm, of the inverse radius
and of the unit representative.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Coarea
open Matrix

/-- The affine representative `(1, z)` as a Euclidean vector. -/
def nonlinearAffineVector {n : Type*} (z : n → ℂ) : EuclideanSpace ℂ (Unit ⊕ n) :=
  WithLp.toLp 2 ((fun _ : Unit => (1 : ℂ)) ⊕ᵥ z)

/-- The insertion `z ↦ (0, z)`, the derivative of the affine representative. -/
def nonlinearAffineInsertion {n : Type*} [Fintype n] :
    (n → ℂ) →L[ℝ] EuclideanSpace ℂ (Unit ⊕ n) :=
  ({ toFun := fun z => WithLp.toLp 2 ((fun _ : Unit => (0 : ℂ)) ⊕ᵥ z)
     map_add' := by intro u v; ext i; cases i <;> simp
     map_smul' := by intro c u; ext i; cases i <;> simp } :
    (n → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Unit ⊕ n)).toContinuousLinearMap

theorem nonlinearAffineVector_eq_add {n : Type*} [Fintype n] (z : n → ℂ) :
    nonlinearAffineVector z = nonlinearAffineVector (0 : n → ℂ) + nonlinearAffineInsertion z := by
  ext i
  cases i <;> simp [nonlinearAffineVector, nonlinearAffineInsertion]

theorem nonlinearAffineVector_ne_zero {n : Type*} [Fintype n] (z : n → ℂ) :
    nonlinearAffineVector z ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : EuclideanSpace ℂ (Unit ⊕ n) => v (Sum.inl Unit.unit)) h
  simp [nonlinearAffineVector] at h0

theorem hasFDerivAt_nonlinearAffineVector {n : Type*} [Fintype n] (z : n → ℂ) :
    HasFDerivAt nonlinearAffineVector nonlinearAffineInsertion z := by
  have h := (hasFDerivAt_const (nonlinearAffineVector (0 : n → ℂ)) z).add
    (nonlinearAffineInsertion (n := n)).hasFDerivAt
  convert h using 1
  · funext u
    exact nonlinearAffineVector_eq_add u
  · simp

/-- The derivative of the squared Euclidean norm of `(1, z)`. -/
def nonlinearAffineNormSqDerivative {n : Type*} [Fintype n] (z : n → ℂ) :
    (n → ℂ) →L[ℝ] ℝ :=
  2 • (innerSL ℝ (nonlinearAffineVector z)).comp nonlinearAffineInsertion

theorem hasFDerivAt_nonlinearAffineNorm_sq {n : Type*} [Fintype n] (z : n → ℂ) :
    HasFDerivAt (fun u : n → ℂ => ‖nonlinearAffineVector u‖ ^ 2)
      (nonlinearAffineNormSqDerivative z) z :=
  (hasFDerivAt_nonlinearAffineVector z).norm_sq

/-- The normalization radius `‖(1, z)‖⁻¹`, which is positive. -/
def nonlinearInvRadius {n : Type*} [Fintype n] (z : n → ℂ) : ℝ :=
  ‖nonlinearAffineVector z‖⁻¹

/-- The derivative of the normalization radius. -/
def nonlinearInvRadiusDerivative {n : Type*} [Fintype n] (z : n → ℂ) :
    (n → ℂ) →L[ℝ] ℝ :=
  (-((‖nonlinearAffineVector z‖⁻¹) ^ 2) / (2 * ‖nonlinearAffineVector z‖)) •
    nonlinearAffineNormSqDerivative z

theorem nonlinearInvRadius_pos {n : Type*} [Fintype n] (z : n → ℂ) :
    0 < nonlinearInvRadius z :=
  inv_pos.mpr (norm_pos_iff.mpr (nonlinearAffineVector_ne_zero z))

theorem hasFDerivAt_nonlinearInvRadius {n : Type*} [Fintype n] (z : n → ℂ) :
    HasFDerivAt nonlinearInvRadius (nonlinearInvRadiusDerivative z) z := by
  have hs := hasFDerivAt_nonlinearAffineNorm_sq z
  have hnorm0 : ‖nonlinearAffineVector z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (nonlinearAffineVector_ne_zero z)
  have hnorm : HasFDerivAt (fun u : n → ℂ => ‖nonlinearAffineVector u‖)
      ((1 / (2 * ‖nonlinearAffineVector z‖)) • nonlinearAffineNormSqDerivative z) z := by
    convert hs.sqrt (pow_ne_zero 2 hnorm0) using 1
    · funext u
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · rw [Real.sqrt_sq (norm_nonneg _)]
  have hi := (hasFDerivAt_inv hnorm0).comp z hnorm
  convert hi using 1
  · rfl
  · ext u
    simp [nonlinearInvRadiusDerivative, div_eq_mul_inv]
    ring

/-- The phase-fixed unit representative `(1, z)/‖(1, z)‖` of the projective affine chart. -/
def nonlinearProjectiveUnit {n : Type*} [Fintype n] (z : n → ℂ) :
    EuclideanSpace ℂ (Unit ⊕ n) :=
  nonlinearInvRadius z • nonlinearAffineVector z

/-- The real derivative of the phase-fixed unit representative. -/
def nonlinearProjectiveUnitDerivative {n : Type*} [Fintype n] (z : n → ℂ) :
    (n → ℂ) →L[ℝ] EuclideanSpace ℂ (Unit ⊕ n) :=
  nonlinearInvRadius z • nonlinearAffineInsertion +
    (nonlinearInvRadiusDerivative z).smulRight (nonlinearAffineVector z)

theorem hasFDerivAt_nonlinearProjectiveUnit {n : Type*} [Fintype n] (z : n → ℂ) :
    HasFDerivAt nonlinearProjectiveUnit (nonlinearProjectiveUnitDerivative z) z :=
  (hasFDerivAt_nonlinearInvRadius z).smul (hasFDerivAt_nonlinearAffineVector z)

theorem norm_nonlinearProjectiveUnit {n : Type*} [Fintype n] (z : n → ℂ) :
    ‖nonlinearProjectiveUnit z‖ = 1 := by
  have hn : 0 < ‖nonlinearAffineVector z‖ :=
    norm_pos_iff.mpr (nonlinearAffineVector_ne_zero z)
  rw [nonlinearProjectiveUnit, norm_smul, nonlinearInvRadius,
    Real.norm_eq_abs, abs_inv, abs_of_nonneg hn.le, inv_mul_cancel₀ hn.ne']

theorem nonlinearProjectiveUnit_selected {n : Type*} [Fintype n] (z : n → ℂ) :
    nonlinearProjectiveUnit z (Sum.inl Unit.unit) = (nonlinearInvRadius z : ℂ) := by
  simp [nonlinearProjectiveUnit, nonlinearAffineVector]

theorem nonlinearProjectiveUnit_selected_re_pos {n : Type*} [Fintype n] (z : n → ℂ) :
    0 < (nonlinearProjectiveUnit z (Sum.inl Unit.unit)).re := by
  rw [nonlinearProjectiveUnit_selected, Complex.ofReal_re]
  exact nonlinearInvRadius_pos z

end BlockBand.Coarea
