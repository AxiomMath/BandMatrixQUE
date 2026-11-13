module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.WeightedSquaresEnvelope
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.ShiftedHolderIntegrals

/-!
# Finite-product Hölder assembly for the APSSS shifted integral

This module records the discrete part of APSSS
(Aizenman–Peled–Schenker–Shamis–Sodin), (6.21)--(6.22).  The tail
weights are the normalized coefficient energies, their sum is proved from the
normalization of `ν`, and generalized Hölder is applied on exactly the tail
index set.  The final lemmas isolate the two cancellations used after the
affine coordinate change `η ↦ ξ Eⱼ² + η Eⱼ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory
open scoped ENNReal NNReal

/-- The finite set of indices which occur in the APSSS tail product. -/
def tailIndices (n r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => r ≤ (j : ℕ)

/-- The normalized energy weight `αⱼ = Eⱼ²(1+bⱼ²)/ν²` from APSSS (6.21). -/
def tailHolderWeight {n : ℕ} (E b : Fin n → ℝ) (ν : ℝ) (j : Fin n) : ℝ :=
  E j ^ 2 * (1 + b j ^ 2) / ν ^ 2

/-- Every tail Hölder weight is nonnegative. -/
theorem tailHolderWeight_nonneg {n : ℕ} (E b : Fin n → ℝ) (ν : ℝ)
    (j : Fin n) : 0 ≤ tailHolderWeight E b ν j := by
  unfold tailHolderWeight
  positivity

/-- The normalized tail weights sum to one.  The normalization hypothesis is
exactly the one exported by `charfun_weightedSquares_envelope`. -/
theorem sum_tailHolderWeight_eq_one {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (ν : ℝ) (hνpos : 0 < ν)
    (hν : ν ^ 2 = ∑ j : Fin n,
      if r ≤ (j : ℕ) then E j ^ 2 * (1 + b j ^ 2) else 0) :
    ∑ j ∈ tailIndices n r, tailHolderWeight E b ν j = 1 := by
  unfold tailIndices
  rw [Finset.sum_filter]
  simp only [tailHolderWeight]
  calc
    (∑ j : Fin n, if r ≤ (j : ℕ) then
        E j ^ 2 * (1 + b j ^ 2) / ν ^ 2 else 0) =
        (∑ j : Fin n, if r ≤ (j : ℕ) then
          E j ^ 2 * (1 + b j ^ 2) else 0) / ν ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : r ≤ (j : ℕ) <;> simp [hj]
    _ = 1 := by
      rw [← hν]
      exact div_self (pow_ne_zero 2 hνpos.ne')

/-- Substitution of `δ = 1/(10ν²)` in the Jacobian prefactor.  This is the
exact cancellation used after the two one-dimensional changes of variables. -/
theorem shifted_jacobian_delta_cancel (E ν δ : ℝ)
    (hE : E ≠ 0) (hν : 0 < ν) (hδ : δ = 1 / (10 * ν ^ 2)) :
    (1 / (|E| * Real.sqrt δ)) * (|E| / ν) = Real.sqrt 10 := by
  have hEabs : 0 < |E| := abs_pos.mpr hE
  have hνsq : 0 < ν ^ 2 := sq_pos_of_pos hν
  have hsqrtδ : Real.sqrt δ = 1 / (Real.sqrt 10 * ν) := by
    rw [hδ]
    have h10 : (0 : ℝ) ≤ 10 := by norm_num
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1) (10 * ν ^ 2),
      Real.sqrt_one, Real.sqrt_mul h10, Real.sqrt_sq_eq_abs, abs_of_pos hν]
  rw [hsqrtδ]
  field_simp

/-- Coordinatewise cancellation of the sharp scalar bound from
`tail_scalar_sharp_weighted` against the affine Jacobian and the fixed
contour scale.  The remaining number `sqrt 30 * sqrt 2` is absolute. -/
theorem shifted_scalar_prefactor_uniform (E ν δ : ℝ)
    (hE : E ≠ 0) (hν : 0 < ν) (hδ : δ = 1 / (10 * ν ^ 2)) :
    (1 / (|E| * Real.sqrt δ)) *
        (Real.sqrt 3 * (Real.sqrt 2 * |E| / ν)) =
      Real.sqrt 30 * Real.sqrt 2 := by
  have hcancel := shifted_jacobian_delta_cancel E ν δ hE hν hδ
  have hsqrt30 : Real.sqrt 3 * Real.sqrt 10 = Real.sqrt 30 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  calc
    (1 / (|E| * Real.sqrt δ)) *
        (Real.sqrt 3 * (Real.sqrt 2 * |E| / ν)) =
      (Real.sqrt 3 * Real.sqrt 2) *
        ((1 / (|E| * Real.sqrt δ)) * (|E| / ν)) := by ring
    _ = (Real.sqrt 3 * Real.sqrt 2) * Real.sqrt 10 := by rw [hcancel]
    _ = Real.sqrt 30 * Real.sqrt 2 := by rw [← hsqrt30]; ring

/-- The exact coordinate integral in APSSS (6.21): the common shifted
`ξ`-kernel, followed by the polynomial and exponential parts of
`tailDecayFactor` with their second-Hölder exponents. -/
def tailHolderCoordinate {n : ℕ} (E b : Fin n → ℝ) (r : ℕ) (ν δ : ℝ)
    (j : Fin n) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) *
      (1 + 4 * (tailAffineFrequency (E j) x.1 x.2) ^ 2) ^
        (-(3 / (4 * ((3 - r : ℕ) : ℝ) *
          tailHolderWeight E b ν j)) : ℝ) *
      Real.exp
        (-(2 * b j ^ 2 / tailHolderWeight E b ν j) *
          (tailAffineFrequency (E j) x.1 x.2) ^ 2 /
            (1 + 4 * (tailAffineFrequency (E j) x.1 x.2) ^ 2)))

/-- The exact coordinate kernel is measurable, so Tonelli and generalized
Hölder apply without a separate regularity assumption. -/
theorem tailHolderCoordinate_aemeasurable {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (ν δ : ℝ) (j : Fin n) :
    AEMeasurable (tailHolderCoordinate E b r ν δ j)
      (volume : Measure (ℝ × ℝ)) := by
  unfold tailHolderCoordinate tailAffineFrequency
  fun_prop

/-- The integrand after the first APSSS Hölder split, uniformly encoded for
the three possible values `r = 0,1,2`.  `d₀,d₁` are the dominant-coordinate
third powers and `t` is the tail factor before its second Hölder split. -/
def firstHolderIntegrand {X : Type*} (r : ℕ)
    (d₀ d₁ t : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  if r = 0 then t x
  else if r = 1 then d₀ x ^ ((1 : ℝ) / 3) * t x ^ ((2 : ℝ) / 3)
  else d₀ x ^ ((1 : ℝ) / 3) * d₁ x ^ ((1 : ℝ) / 3) *
    t x ^ ((1 : ℝ) / 3)

/-- The exact right side of the first Hölder step, with no constants hidden.
This declaration is expressed using the three scalar
integrals, so later dominant-coordinate estimates can rewrite it directly. -/
def firstHolderBound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (r : ℕ) (d₀ d₁ t : X → ℝ≥0∞) : ℝ≥0∞ :=
  if r = 0 then ∫⁻ x, t x ∂μ
  else if r = 1 then
    (∫⁻ x, d₀ x ∂μ) ^ ((1 : ℝ) / 3) *
      (∫⁻ x, t x ∂μ) ^ ((2 : ℝ) / 3)
  else
    (∫⁻ x, d₀ x ∂μ) ^ ((1 : ℝ) / 3) *
      (∫⁻ x, d₁ x ∂μ) ^ ((1 : ℝ) / 3) *
      (∫⁻ x, t x ∂μ) ^ ((1 : ℝ) / 3)

/-- APSSS (6.19) instantiated simultaneously for `r=0,1,2`. -/
theorem firstHolder_lintegral_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (r : ℕ) (hr : r ≤ 2) (d₀ d₁ t : X → ℝ≥0∞)
    (hd₀ : AEMeasurable d₀ μ) (hd₁ : AEMeasurable d₁ μ)
    (ht : AEMeasurable t μ) :
    (∫⁻ x, firstHolderIntegrand r d₀ d₁ t x ∂μ) ≤
      firstHolderBound μ r d₀ d₁ t := by
  interval_cases r
  · simp [firstHolderIntegrand, firstHolderBound]
  · simpa [firstHolderIntegrand, firstHolderBound] using
      holder_three_one d₀ t hd₀ ht
  · simpa [firstHolderIntegrand, firstHolderBound, mul_assoc] using
      holder_three_two d₀ d₁ t hd₀ hd₁ ht

/-- The first Hölder bound after substituting a proved uniform estimate for
the tail integral.  This is monotone in the tail bound with the exact weights
`1`, `2/3`, and `1/3`. -/
theorem firstHolderBound_mono_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℕ) (hr : r ≤ 2) (d₀ d₁ t : X → ℝ≥0∞)
    (C : ℝ≥0∞) (ht : (∫⁻ x, t x ∂μ) ≤ C) :
    firstHolderBound μ r d₀ d₁ t ≤
      if r = 0 then C
      else if r = 1 then
        (∫⁻ x, d₀ x ∂μ) ^ ((1 : ℝ) / 3) * C ^ ((2 : ℝ) / 3)
      else
        (∫⁻ x, d₀ x ∂μ) ^ ((1 : ℝ) / 3) *
          (∫⁻ x, d₁ x ∂μ) ^ ((1 : ℝ) / 3) * C ^ ((1 : ℝ) / 3) := by
  interval_cases r
  · simpa [firstHolderBound] using ht
  · norm_num [firstHolderBound]
    gcongr
  · norm_num [firstHolderBound]
    gcongr

/-- Final parametric two-dimensional shifted-integral assembly.  Its sole
analytic input beyond measurability is a bound for the tail integral `t`;
the companion coordinate module supplies this input by Tonelli and the sharp
one-dimensional estimate.  The dominant factors and all constants remain
displayed exactly. -/
theorem shifted_integral_le_of_tail_bound
    (r : ℕ) (hr : r ≤ 2) (d₀ d₁ t : (ℝ × ℝ) → ℝ≥0∞)
    (hd₀ : AEMeasurable d₀ (volume : Measure (ℝ × ℝ)))
    (hd₁ : AEMeasurable d₁ (volume : Measure (ℝ × ℝ)))
    (htmeas : AEMeasurable t (volume : Measure (ℝ × ℝ)))
    (C : ℝ≥0∞) (htail : (∫⁻ x : ℝ × ℝ, t x) ≤ C) :
    (∫⁻ x : ℝ × ℝ, firstHolderIntegrand r d₀ d₁ t x) ≤
      if r = 0 then C
      else if r = 1 then
        (∫⁻ x : ℝ × ℝ, d₀ x) ^ ((1 : ℝ) / 3) * C ^ ((2 : ℝ) / 3)
      else
        (∫⁻ x : ℝ × ℝ, d₀ x) ^ ((1 : ℝ) / 3) *
          (∫⁻ x : ℝ × ℝ, d₁ x) ^ ((1 : ℝ) / 3) *
            C ^ ((1 : ℝ) / 3) := by
  exact (firstHolder_lintegral_le r hr d₀ d₁ t hd₀ hd₁ htmeas).trans
    (firstHolderBound_mono_tail volume r hr d₀ d₁ t C htail)

/-- The tail product which enters the first Hölder step after the second
Hölder weights have been installed. -/
def tailHolderProduct {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (ν δ : ℝ) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ∏ j ∈ tailIndices n r,
    tailHolderCoordinate E b r ν δ j x ^ tailHolderWeight E b ν j

/-- Measurability of the complete finite tail product. -/
theorem tailHolderProduct_aemeasurable {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (ν δ : ℝ) :
    AEMeasurable (tailHolderProduct E b r ν δ)
      (volume : Measure (ℝ × ℝ)) := by
  unfold tailHolderProduct
  exact (tailIndices n r).aemeasurable_fun_prod fun j _ =>
    (tailHolderCoordinate_aemeasurable E b r ν δ j).pow_const _

end PSSSNative.BlockBand.PSSS
