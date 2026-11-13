module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.DominantSelectionStructure
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.ShiftedHolderCoordinateBound

/-!
# Reduction of the APSSS tail to its nonzero support

The nominal APSSS tail can contain coordinates with coefficient `E j = 0`.
Those coordinates have zero normalized weight, unit characteristic and decay
factors, and unit powered Hölder factors.  This module removes them before the
affine changes of variables, while preserving the exact tail energy and the
full shifted-integral conclusion.  Both the empty zero-tail branch and the
positive nonempty branch are treated explicitly.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex MeasureTheory
open scoped ENNReal NNReal

/-- The active tail coordinates (those with nonzero coefficient). -/
def nonzeroTailSupport {n : ℕ} (E : Fin n → ℝ) (r : ℕ) : Finset (Fin n) :=
  (tailIndices n r).filter fun j => E j ≠ 0

@[simp]
theorem mem_nonzeroTailSupport {n : ℕ} (E : Fin n → ℝ) (r : ℕ)
    (j : Fin n) :
    j ∈ nonzeroTailSupport E r ↔ r ≤ (j : ℕ) ∧ E j ≠ 0 := by
  simp [nonzeroTailSupport, tailIndices]

/-- Every active tail coefficient is nonzero, by construction. -/
theorem coefficient_ne_zero_of_mem_nonzeroTailSupport {n : ℕ}
    (E : Fin n → ℝ) (r : ℕ) (j : Fin n)
    (hj : j ∈ nonzeroTailSupport E r) : E j ≠ 0 :=
  (mem_nonzeroTailSupport E r j).mp hj |>.2

/-- A zero coefficient has zero normalized Hölder weight, including at
`ν = 0` under Lean's totalized real division. -/
@[simp]
theorem tailHolderWeight_eq_zero_of_coefficient_eq_zero {n : ℕ}
    (E b : Fin n → ℝ) (ν : ℝ) (j : Fin n) (hE : E j = 0) :
    tailHolderWeight E b ν j = 0 := by
  simp [tailHolderWeight, hE]

/-- The APSSS tail decay factor of a zero coefficient is one. -/
@[simp]
theorem tailDecayFactor_eq_one_of_coefficient_eq_zero
    (E b ξ η : ℝ) (hE : E = 0) :
    tailDecayFactor E b ξ η = 1 := by
  simp [tailDecayFactor, tailAffineFrequency, hE]

/-- A zero coefficient contributes the unit factor after installation of its
zero Hölder exponent. -/
@[simp]
theorem tailHolderCoordinate_rpow_eq_one_of_coefficient_eq_zero {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ν δ : ℝ) (j : Fin n) (x : ℝ × ℝ)
    (hE : E j = 0) :
    tailHolderCoordinate E b r ν δ j x ^ tailHolderWeight E b ν j = 1 := by
  rw [tailHolderWeight_eq_zero_of_coefficient_eq_zero E b ν j hE]
  exact ENNReal.rpow_zero

/-- A finite tail product whose zero-coordinate factors are one is unchanged
when restricted to the nonzero support. -/
theorem prod_tailIndices_eq_prod_nonzeroTailSupport {n : ℕ}
    {M : Type*} [CommMonoid M] (E : Fin n → ℝ) (r : ℕ) (f : Fin n → M)
    (hzero : ∀ j ∈ tailIndices n r, E j = 0 → f j = 1) :
    (∏ j ∈ tailIndices n r, f j) =
      ∏ j ∈ nonzeroTailSupport E r, f j := by
  rw [nonzeroTailSupport, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hE : E j = 0
  · simp [hE, hzero j hj hE]
  · simp [hE]

/-- Zero tail decay factors can be erased exactly. -/
theorem prod_tailDecayFactor_eq_prod_nonzeroTailSupport {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ξ η : ℝ) :
    (∏ j ∈ tailIndices n r, tailDecayFactor (E j) (b j) ξ η) =
      ∏ j ∈ nonzeroTailSupport E r,
        tailDecayFactor (E j) (b j) ξ η := by
  apply prod_tailIndices_eq_prod_nonzeroTailSupport E r
  intro j _ hE
  exact tailDecayFactor_eq_one_of_coefficient_eq_zero (E j) (b j) ξ η hE

/-- With positive tail scale, the weights on the nonzero support still sum
exactly to one. -/
theorem sum_nonzeroTailSupport_tailHolderWeight_eq_one {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ν : ℝ) (hνpos : 0 < ν)
    (hν : ν ^ 2 = tailEnergy E b r) :
    ∑ j ∈ nonzeroTailSupport E r, tailHolderWeight E b ν j = 1 := by
  rw [← sum_tailHolderWeight_eq_one E b r ν hνpos (by
    simpa only [tailEnergy, coefficientEnergy] using hν)]
  apply Finset.sum_subset
  · show nonzeroTailSupport E r ⊆ tailIndices n r
    exact Finset.filter_subset _ _
  · intro j hjtail hjnot
    have hE : E j = 0 := by
      by_contra hne
      exact hjnot (Finset.mem_filter.mpr ⟨hjtail, hne⟩)
    simp [hE, tailHolderWeight]

/-- The tail Hölder product restricted to active coordinates. -/
def supportedTailHolderProduct {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (ν δ : ℝ) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ∏ j ∈ nonzeroTailSupport E r,
    tailHolderCoordinate E b r ν δ j x ^ tailHolderWeight E b ν j

/-- Removing zero-coordinate unit factors does not change the Hölder product. -/
theorem tailHolderProduct_eq_supportedTailHolderProduct {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ν δ : ℝ) :
    tailHolderProduct E b r ν δ = supportedTailHolderProduct E b r ν δ := by
  funext x
  unfold tailHolderProduct supportedTailHolderProduct
  apply prod_tailIndices_eq_prod_nonzeroTailSupport E r
  intro j _ hE
  exact tailHolderCoordinate_rpow_eq_one_of_coefficient_eq_zero
    E b r ν δ j x hE

/-- Measurability of the supported tail Hölder product. -/
theorem supportedTailHolderProduct_aemeasurable {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ν δ : ℝ) :
    AEMeasurable (supportedTailHolderProduct E b r ν δ)
      (volume : Measure (ℝ × ℝ)) := by
  unfold supportedTailHolderProduct
  exact (nonzeroTailSupport E r).aemeasurable_fun_prod fun j _ =>
    (tailHolderCoordinate_aemeasurable E b r ν δ j).pow_const _

/-- Generalized Hölder on precisely the active support. -/
theorem supportedTailHolderProduct_lintegral_holder {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (ν δ : ℝ) (hνpos : 0 < ν)
    (hν : ν ^ 2 = tailEnergy E b r) :
    (∫⁻ x : ℝ × ℝ, supportedTailHolderProduct E b r ν δ x) ≤
      ∏ j ∈ nonzeroTailSupport E r,
        (∫⁻ x : ℝ × ℝ, tailHolderCoordinate E b r ν δ j x) ^
          tailHolderWeight E b ν j := by
  exact ENNReal.lintegral_prod_norm_pow_le (nonzeroTailSupport E r)
    (fun j _ => tailHolderCoordinate_aemeasurable E b r ν δ j)
    (sum_nonzeroTailSupport_tailHolderWeight_eq_one E b r ν hνpos hν)
    (fun j _ => tailHolderWeight_nonneg E b ν j)

/-- The full APSSS absolute tail bound after deleting zero coefficients.  The
sharp coordinate theorem is applied directly on the nonzero support. -/
theorem supportedTailHolderProduct_lintegral_le_absolute {n : ℕ}
    (E b : Fin n → ℝ) (r : ℕ) (hr : r ≤ 2) (ν δ : ℝ)
    (hνpos : 0 < ν) (hν : ν ^ 2 = tailEnergy E b r)
    (hδ : δ = 1 / (10 * ν ^ 2))
    (hweight : ∀ j ∈ nonzeroTailSupport E r,
      ((3 - r : ℕ) : ℝ) * tailHolderWeight E b ν j ≤ 1) :
    (∫⁻ x : ℝ × ℝ, supportedTailHolderProduct E b r ν δ x) ≤
      ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
        threeQuarterKernelConstant ^ 2 := by
  refine (supportedTailHolderProduct_lintegral_holder
    E b r ν δ hνpos hν).trans ?_
  have hcoordinate : ∀ j ∈ nonzeroTailSupport E r,
      (∫⁻ x : ℝ × ℝ, tailHolderCoordinate E b r ν δ j x) ≤
        ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
          threeQuarterKernelConstant ^ 2 := by
    intro j hj
    exact tailHolderCoordinate_lintegral_le E b r hr ν δ j
      (coefficient_ne_zero_of_mem_nonzeroTailSupport E r j hj)
      hνpos hδ (hweight j hj)
  have hprod :
      (∏ j ∈ nonzeroTailSupport E r,
        (∫⁻ x : ℝ × ℝ, tailHolderCoordinate E b r ν δ j x) ^
          tailHolderWeight E b ν j) ≤
      ∏ j ∈ nonzeroTailSupport E r,
        (ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
          threeQuarterKernelConstant ^ 2) ^ tailHolderWeight E b ν j := by
    exact Finset.prod_le_prod₀ (fun _ _ => bot_le) fun j hj =>
      ENNReal.rpow_le_rpow (hcoordinate j hj)
        (tailHolderWeight_nonneg E b ν j)
  refine hprod.trans ?_
  have hcollapse :
    (∏ j ∈ nonzeroTailSupport E r,
        (ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
          threeQuarterKernelConstant ^ 2) ^ tailHolderWeight E b ν j) =
      ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
        threeQuarterKernelConstant ^ 2 := by
    calc
      (∏ j ∈ nonzeroTailSupport E r,
          (ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
            threeQuarterKernelConstant ^ 2) ^ tailHolderWeight E b ν j) =
        (ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
          threeQuarterKernelConstant ^ 2) ^
          (∑ j ∈ nonzeroTailSupport E r, tailHolderWeight E b ν j) := by
        symm
        induction nonzeroTailSupport E r using Finset.induction_on with
        | empty => simp
        | @insert j s hjs ih =>
            rw [Finset.sum_insert hjs, Finset.prod_insert hjs,
              ENNReal.rpow_add_of_nonneg]
            · rw [ih]
            · exact tailHolderWeight_nonneg E b ν j
            · exact Finset.sum_nonneg fun k hk =>
                tailHolderWeight_nonneg E b ν k
      _ = ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
            threeQuarterKernelConstant ^ 2 := by
        rw [sum_nonzeroTailSupport_tailHolderWeight_eq_one E b r ν hνpos hν,
          ENNReal.rpow_one]
  exact hcollapse.le

end PSSSNative.BlockBand.PSSS
