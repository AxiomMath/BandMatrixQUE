module

public import BlockBand.QUE.SiteDecomposition

/-!
# Finite second-moment algebra behind the Haar site bridge

The second moment of a linear statistic `Σ w_x mass_x` is expanded into coordinate second
moments; for a test with zero sum in each block, block-constant covariances cancel and the
centred residual variance is given by the diagonal excess (`residual_statistic_of_second_moments`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE

open MeasureTheory
open scoped BigOperators Classical
open BlockBand.Foundations.FiniteBlock

variable {Ω B A : Type*} [MeasurableSpace Ω] [Fintype B] [Fintype A] [Nonempty A]

omit [Nonempty A] in
/-- Block-constant covariance terms cancel exactly for a test with zero sum in
each block; the diagonal terms retain precisely the weighted squared norm. -/
theorem centered_covariance_sum (w : B × A → ℝ) (κ : B → B → ℝ)
    (diagonalExcess : B → ℝ) (hw : ∀ b, ∑ a : A, w (b, a) = 0) :
    (∑ x : B × A, ∑ y : B × A,
      w x * w y * (κ x.1 y.1 + if x = y then diagonalExcess x.1 else 0)) =
      ∑ b : B, diagonalExcess b * ∑ a : A, w (b, a) ^ 2 := by
  classical
  have hconstant (x : B × A) :
      (∑ y : B × A, w x * w y * κ x.1 y.1) = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro b _
    calc
      (∑ a : A, w x * w (b, a) * κ x.1 b) =
          (w x * κ x.1 b) * ∑ a : A, w (b, a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = 0 := by rw [hw, mul_zero]
  have hdiagonal (x : B × A) :
      (∑ y : B × A, w x * w y * (if x = y then diagonalExcess x.1 else 0)) =
        diagonalExcess x.1 * w x ^ 2 := by
    simp only [mul_ite, mul_zero]
    simp
    ring
  simp_rw [mul_add, Finset.sum_add_distrib, hconstant, hdiagonal]
  simp only [Finset.sum_const_zero, zero_add, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]

omit [MeasurableSpace Ω] [Nonempty A] in
/-- Expansion of the squared finite real linear statistic into all coordinate second products
(deterministic). -/
theorem squared_sum_expansion (w : B × A → ℝ) (mass : B × A → ℝ) :
    |∑ x : B × A, w x * mass x| ^ 2 =
      ∑ x : B × A, ∑ y : B × A,
        w x * w y * (mass x * mass y) := by
  rw [sq_abs, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Coordinate second-moment identities imply the centred residual variance. All finite products
are integrable under `μ`; `κ` and `diagonalExcess` are coordinate moments. -/
theorem residual_statistic_of_second_moments (μ : Measure Ω)
    (mass : Ω → B × A → ℝ) (baseline : ℝ) (v : B × A → ℝ)
    (κ : B → B → ℝ) (diagonalExcess : B → ℝ)
    (hint : ∀ x y, Integrable (fun ω => mass ω x * mass ω y) μ)
    (hmoment : ∀ x y, (∫ ω, mass ω x * mass ω y ∂μ) =
      κ x.1 y.1 + if x = y then diagonalExcess x.1 else 0) :
    quadraticStatistic μ mass baseline (centeredPart v) =
      ∑ b : B, diagonalExcess b * ∑ a : A, centeredPart v (b, a) ^ 2 := by
  classical
  unfold quadraticStatistic
  simp_rw [fluctuation_centered, squared_sum_expansion]
  rw [integral_finsetSum _ (fun x _ =>
    integrable_finsetSum _ (fun y _ => (hint x y).const_mul _))]
  simp_rw [integral_finsetSum _ (fun y _ => (hint _ y).const_mul _),
    integral_const_mul, hmoment]
  exact centered_covariance_sum (centeredPart v) κ diagonalExcess (sum_centered v)

end BlockBand.QUE
