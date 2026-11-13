module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.ShiftedHolderCoordinateBound
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.FourierCriterion

/-!
# Absolute bound for the shifted APSSS integral

This module closes the first Hölder step after the coordinatewise tail bound.
The dominant factors are the cubed dominant decays of APSSS
(Aizenman–Peled–Schenker–Shamis–Sodin), with the
common shifted `ξ` kernel assigned to each first-Hölder factor.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory
open scoped ENNReal NNReal

/-- The dominant selection makes the energy left after the dominant coordinates
at most ten times each selected dominant energy. -/
theorem dominantSelection_tailEnergy_le {n : ℕ} {E b : Fin n → ℝ} {r : ℕ}
    (hsel : DominantSelection E b r) (j : Fin n) (hj : (j : ℕ) < r) :
    (∑ k : Fin n,
      if r ≤ (k : ℕ) then E k ^ 2 * (1 + b k ^ 2) else 0) ≤
        10 * (E j ^ 2 * (1 + b j ^ 2)) := by
  have hmono := hsel.1
  have hr := hsel.2
  let w : Fin n → ℝ := fun k => E k ^ 2 * (1 + b k ^ 2)
  by_cases hzero :
      (∑ k : Fin n, if (k : ℕ) = 0 then w k else 0) ≤
        (∑ k : Fin n, if 0 < (k : ℕ) then w k else 0) / 10
  · have : r = 0 := by simpa [w, hzero] using hr
    omega
  · by_cases hone :
      (∑ k : Fin n, if (k : ℕ) = 1 then w k else 0) ≤
        (∑ k : Fin n, if 1 < (k : ℕ) then w k else 0) / 10
    · have hr1 : r = 1 := by simpa [w, hzero, hone] using hr
      have hj0 : (j : ℕ) = 0 := by omega
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) j.isLt
      let k₀ : Fin n := ⟨0, hn0⟩
      have hjk₀ : j = k₀ := Fin.ext (by simpa [k₀] using hj0)
      have hlt :
          (∑ k : Fin n, if 0 < (k : ℕ) then w k else 0) <
            10 * (∑ k : Fin n, if (k : ℕ) = 0 then w k else 0) := by
        have := lt_of_not_ge hzero
        linarith
      have hsingle :
          (∑ k : Fin n, if (k : ℕ) = 0 then w k else 0) = w k₀ := by
        rw [Finset.sum_eq_single k₀]
        · simp [k₀]
        · intro k _ hk
          by_cases h : (k : ℕ) = 0
          · exact (hk (Fin.ext (by simpa [k₀] using h))).elim
          · simp [h]
        · simp
      rw [hsingle] at hlt
      rw [hr1, hjk₀]
      calc
        (∑ k : Fin n, if 1 ≤ (k : ℕ) then
            E k ^ 2 * (1 + b k ^ 2) else 0) =
            ∑ k : Fin n, if 0 < (k : ℕ) then w k else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              simp only [w]
              congr 1
        _ ≤ 10 * w k₀ := hlt.le
        _ = 10 * (E k₀ ^ 2 * (1 + b k₀ ^ 2)) := rfl
    · have hr2 : r = 2 := by simpa [w, hzero, hone] using hr
      have hlt :
          (∑ k : Fin n, if 1 < (k : ℕ) then w k else 0) <
            10 * (∑ k : Fin n, if (k : ℕ) = 1 then w k else 0) := by
        have := lt_of_not_ge hone
        linarith
      have h1n : 1 < n := by
        by_contra hn
        have hnle : n ≤ 1 := by omega
        apply hone
        have hs1 :
            (∑ k : Fin n, if (k : ℕ) = 1 then w k else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          have hk : (k : ℕ) ≠ 1 := by omega
          simp [hk]
        have hst :
            (∑ k : Fin n, if 1 < (k : ℕ) then w k else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          have hk : ¬ 1 < (k : ℕ) := by omega
          simp [hk]
        rw [hs1, hst]
        norm_num
      let k₁ : Fin n := ⟨1, h1n⟩
      have hkj : w k₁ ≤ w j := by
        apply hmono
        apply Fin.mk_le_mk.mpr
        omega
      rw [hr2]
      calc
        (∑ k : Fin n, if 2 ≤ (k : ℕ) then E k ^ 2 * (1 + b k ^ 2) else 0) =
            ∑ k : Fin n, if 1 < (k : ℕ) then w k else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              simp only [w]
              congr 1
        _ ≤ 10 * w k₁ := by
          have hsum1 :
              (∑ k : Fin n, if (k : ℕ) = 1 then w k else 0) = w k₁ := by
            rw [Finset.sum_eq_single k₁]
            · simp [k₁]
            · intro k _ hk
              by_cases h : (k : ℕ) = 1
              · exact (hk (Fin.ext (by simpa [k₁] using h))).elim
              · simp [h]
            · simp [k₁]
          rw [hsum1] at hlt
          exact hlt.le
        _ ≤ 10 * w j := mul_le_mul_of_nonneg_left hkj (by norm_num)
        _ = 10 * (E j ^ 2 * (1 + b j ^ 2)) := rfl

/-- The exact cube of the dominant APSSS decay factor, written in its
algebraically combined form after multiplying the three identical factors. -/
def dominantCubedDecay (E b η : ℝ) : ℝ :=
  (1 + (2 * E * η) ^ 2) ^ (-(3 : ℝ) / 4) *
    Real.exp (-((3 / 2 : ℝ) * b ^ 2) * (2 * E * η) ^ 2 /
      (1 + (2 * E * η) ^ 2))

/-- Dominant factor used in the first APSSS Hölder step. -/
def dominantHolderCoordinate {n : ℕ} (E b : Fin n → ℝ) (δ : ℝ)
    (j : Fin n) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (((x.1 ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) *
      dominantCubedDecay (E j) (b j) x.2)

/-- Dominant-coordinate measurability. -/
theorem dominantHolderCoordinate_aemeasurable {n : ℕ} (E b : Fin n → ℝ)
    (δ : ℝ) (j : Fin n) :
    AEMeasurable (dominantHolderCoordinate E b δ j)
      (volume : Measure (ℝ × ℝ)) := by
  unfold dominantHolderCoordinate dominantCubedDecay
  fun_prop

private theorem lintegral_comp_mul (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (c : ℝ) (hc : c ≠ 0) :
    (∫⁻ x : ℝ, f (c * x)) =
      ENNReal.ofReal |c⁻¹| * ∫⁻ y : ℝ, f y := by
  calc
    (∫⁻ x : ℝ, f (c * x)) =
        ∫⁻ y : ℝ, f y ∂Measure.map (fun x : ℝ => c * x) volume := by
          rw [lintegral_map']
          · exact hf.aemeasurable
          · fun_prop
    _ = ∫⁻ y : ℝ, f y ∂
          (ENNReal.ofReal |c⁻¹| • (volume : Measure ℝ)) := by
          rw [Real.map_volume_mul_left hc]
    _ = ENNReal.ofReal |c⁻¹| * ∫⁻ y : ℝ, f y := by
          rw [lintegral_smul_measure]
          rfl

/-- Sharp one-dimensional integral of a cubed dominant decay factor. -/
theorem dominantDecayFactor_cubed_lintegral_le (E b : ℝ) (hE : E ≠ 0) :
    (∫⁻ η : ℝ, ENNReal.ofReal (dominantCubedDecay E b η)) ≤
      ENNReal.ofReal
          ((1 / (2 * |E|)) * (Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2))⁻¹) *
        threeQuarterKernelConstant := by
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal
    ((1 + x ^ 2) ^ (-(3 : ℝ) / 4) *
      Real.exp (-((3 / 2 : ℝ) * b ^ 2) * x ^ 2 / (1 + x ^ 2)))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hchange := lintegral_comp_mul f hf (2 * E) (mul_ne_zero (by norm_num) hE)
  have hsharp := lintegral_rational_exp_sharp ((3 / 2 : ℝ) * b ^ 2) (by positivity)
  have hre :
      (∫⁻ η : ℝ, ENNReal.ofReal (dominantCubedDecay E b η)) =
        ENNReal.ofReal |(2 * E)⁻¹| * ∫⁻ x : ℝ, f x := by
    simpa only [f, dominantCubedDecay] using hchange
  rw [hre]
  calc
    _ ≤ ENNReal.ofReal |(2 * E)⁻¹| *
        (ENNReal.ofReal
          ((Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2))⁻¹) *
            threeQuarterKernelConstant) := by gcongr
    _ = ENNReal.ofReal
          ((1 / (2 * |E|)) * (Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2))⁻¹) *
        threeQuarterKernelConstant := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      apply congrArg ENNReal.ofReal
      rw [abs_inv, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring

/-- Selection-energy control cancels the dominant-coordinate Jacobian and the
fixed contour scale with an absolute factor five. -/
theorem dominant_prefactor_le_five (E b ν δ : ℝ)
    (hE : E ≠ 0) (hν : 0 < ν)
    (hδ : δ = 1 / (10 * ν ^ 2))
    (henergy : ν ^ 2 ≤ 10 * (E ^ 2 * (1 + b ^ 2))) :
    (1 / Real.sqrt δ) * (1 / (2 * |E|)) *
        (Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2))⁻¹ ≤ 5 := by
  have hEabs : 0 < |E| := abs_pos.mpr hE
  have hs : 0 < Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2) := by positivity
  have hs_sq :
      Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2) ^ 2 =
        1 + (3 / 2 : ℝ) * b ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrtδ : Real.sqrt δ = 1 / (Real.sqrt 10 * ν) := by
    rw [hδ]
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1) (10 * ν ^ 2),
      Real.sqrt_one, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 10),
      Real.sqrt_sq_eq_abs, abs_of_pos hν]
  have hden_sq :
      (|E| * Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2)) ^ 2 =
        E ^ 2 * (1 + (3 / 2 : ℝ) * b ^ 2) := by
    rw [mul_pow, sq_abs, hs_sq]
  have hratio_sq :
      ν ^ 2 ≤
        (Real.sqrt 10 *
          (|E| * Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 10), hden_sq]
    nlinarith [sq_nonneg E, sq_nonneg b]
  have hratio :
      ν ≤ Real.sqrt 10 *
        (|E| * Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2)) := by
    exact (sq_le_sq₀ hν.le
      (mul_nonneg (Real.sqrt_nonneg 10) (mul_nonneg hEabs.le hs.le))).mp
        hratio_sq
  rw [hsqrtδ]
  have hsqrt10 : 0 < Real.sqrt 10 := by positivity
  have hratio' :
      ν / (|E| * Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2)) ≤ Real.sqrt 10 :=
    (div_le_iff₀ (mul_pos hEabs hs)).2 (by simpa [mul_assoc] using hratio)
  calc
    (1 / (1 / (Real.sqrt 10 * ν))) * (1 / (2 * |E|)) *
        (Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2))⁻¹ =
      (Real.sqrt 10 / 2) *
        (ν / (|E| * Real.sqrt (1 + (3 / 2 : ℝ) * b ^ 2))) := by
          field_simp
    _ ≤ (Real.sqrt 10 / 2) * Real.sqrt 10 := by
      exact mul_le_mul_of_nonneg_left hratio' (by positivity)
    _ = 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)]

/-- Each selected dominant coordinate has the same universal two-dimensional
integral bound as the complete tail product. -/
theorem dominantHolderCoordinate_lintegral_le {n : ℕ}
    (E b : Fin n → ℝ) (ν δ : ℝ) (j : Fin n)
    (hE : E j ≠ 0) (hν : 0 < ν)
    (hδ : δ = 1 / (10 * ν ^ 2))
    (henergy : ν ^ 2 ≤ 10 * (E j ^ 2 * (1 + b j ^ 2))) :
    (∫⁻ x : ℝ × ℝ, dominantHolderCoordinate E b δ j x) ≤
      ENNReal.ofReal 5 * threeQuarterKernelConstant ^ 2 := by
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hη := dominantDecayFactor_cubed_lintegral_le (E j) (b j) hE
  rw [Measure.volume_eq_prod ℝ ℝ, MeasureTheory.lintegral_prod]
  swap
  · simpa only [Measure.volume_eq_prod] using
      (dominantHolderCoordinate_aemeasurable E b δ j)
  calc
    (∫⁻ ξ : ℝ, ∫⁻ η : ℝ, dominantHolderCoordinate E b δ j (ξ, η)) ≤
        ∫⁻ ξ : ℝ, ENNReal.ofReal
          ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) *
        (ENNReal.ofReal
          ((1 / (2 * |E j|)) *
            (Real.sqrt (1 + (3 / 2 : ℝ) * b j ^ 2))⁻¹) *
          threeQuarterKernelConstant) := by
      apply lintegral_mono
      intro ξ
      change (∫⁻ η : ℝ, dominantHolderCoordinate E b δ j (ξ, η)) ≤
        ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) *
          (ENNReal.ofReal
            ((1 / (2 * |E j|)) *
              (Real.sqrt (1 + (3 / 2 : ℝ) * b j ^ 2))⁻¹) *
            threeQuarterKernelConstant)
      unfold dominantHolderCoordinate
      have hfactor :
          (fun η : ℝ => ENNReal.ofReal
            (((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) *
              dominantCubedDecay (E j) (b j) η)) =
            (fun η : ℝ => ENNReal.ofReal
              ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) *
                ENNReal.ofReal (dominantCubedDecay (E j) (b j) η)) := by
        funext η
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      rw [hfactor]
      rw [lintegral_const_mul]
      swap
      · unfold dominantCubedDecay
        fun_prop
      gcongr
    _ =
        (∫⁻ ξ : ℝ, ENNReal.ofReal
          ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4))) *
        (ENNReal.ofReal
          ((1 / (2 * |E j|)) *
            (Real.sqrt (1 + (3 / 2 : ℝ) * b j ^ 2))⁻¹) *
          threeQuarterKernelConstant) := by
      exact lintegral_mul_const _ (by fun_prop)
    _ = (ENNReal.ofReal (1 / Real.sqrt δ) *
          threeQuarterKernelConstant) *
        (ENNReal.ofReal
          ((1 / (2 * |E j|)) *
            (Real.sqrt (1 + (3 / 2 : ℝ) * b j ^ 2))⁻¹) *
          threeQuarterKernelConstant) := by
      rw [xi_kernel_lintegral_eq δ hδpos]
    _ = ENNReal.ofReal
          ((1 / Real.sqrt δ) * (1 / (2 * |E j|)) *
            (Real.sqrt (1 + (3 / 2 : ℝ) * b j ^ 2))⁻¹) *
          threeQuarterKernelConstant ^ 2 := by
      calc
        _ = (ENNReal.ofReal (1 / Real.sqrt δ) *
              ENNReal.ofReal ((1 / (2 * |E j|)) *
                (Real.sqrt (1 + (3 / 2 : ℝ) * b j ^ 2))⁻¹)) *
              threeQuarterKernelConstant ^ 2 := by ring
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity :
            (0 : ℝ) ≤ 1 / Real.sqrt δ)]
          ring
    _ ≤ ENNReal.ofReal 5 * threeQuarterKernelConstant ^ 2 := by
      gcongr
      exact dominant_prefactor_le_five (E j) (b j) ν δ hE hν hδ henergy

/-- The explicit universal constant left by both Hölder steps. -/
def shiftedIntegralAbsoluteConstant : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
    threeQuarterKernelConstant ^ 2

/-- The factor five from a dominant coordinate is below the common absolute
constant used for the tail. -/
theorem dominant_constant_le_absolute :
    ENNReal.ofReal 5 * threeQuarterKernelConstant ^ 2 ≤
      shiftedIntegralAbsoluteConstant := by
  unfold shiftedIntegralAbsoluteConstant
  gcongr
  have h30 : Real.sqrt 30 ^ 2 = 30 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ Real.sqrt 30 * Real.sqrt 2 := mul_nonneg
    (Real.sqrt_nonneg 30) (Real.sqrt_nonneg 2)
  nlinarith

end PSSSNative.BlockBand.PSSS
