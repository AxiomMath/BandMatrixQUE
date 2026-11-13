module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.ShiftedHolderProduct

/-!
# Uniform bound for one shifted Hölder coordinate

This module proves `tailHolderCoordinate_lintegral_le`: for `E_j ≠ 0`, `ν > 0`,
`δ = 1/(10ν²)` and `(3 - r) w_j ≤ 1`, the integral of the shifted Hölder
coordinate over `ℝ × ℝ` is at most `√30 √2 · c²`, `c = threeQuarterKernelConstant`.
The proof uses Tonelli, two affine changes of variables and the sharp scalar
tail estimate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory
open scoped ENNReal NNReal

/-- Exact change of variables for a nonnegative measurable function under a
nondegenerate real affine map. -/
private theorem lintegral_comp_affine (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (c E : ℝ) (hE : E ≠ 0) :
    (∫⁻ x : ℝ, f (c + E * x)) =
      ENNReal.ofReal |E⁻¹| * ∫⁻ y : ℝ, f y := by
  have hg : Measurable (fun y : ℝ => f (c + y)) := by fun_prop
  calc
    (∫⁻ x : ℝ, f (c + E * x)) =
        ∫⁻ y : ℝ, f (c + y) ∂Measure.map (fun x : ℝ => E * x) volume := by
          rw [lintegral_map']
          · exact hg.aemeasurable
          · fun_prop
    _ = ∫⁻ y : ℝ, f (c + y) ∂
          (ENNReal.ofReal |E⁻¹| • (volume : Measure ℝ)) := by
          rw [Real.map_volume_mul_left hE]
    _ = ENNReal.ofReal |E⁻¹| * ∫⁻ y : ℝ, f (c + y) := by
          rw [lintegral_smul_measure]
          rfl
    _ = ENNReal.ofReal |E⁻¹| * ∫⁻ y : ℝ, f y := by
          rw [lintegral_add_left_eq_self]

/-- The sharp scalar tail bound after the physical substitution `x = 2 ζ`.
The elementary max comparison costs exactly a factor two. -/
theorem tail_scalar_sharp_half_weighted {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (hr : r ≤ 2) (ν : ℝ) (j : Fin n)
    (hE : E j ≠ 0) (hν : 0 < ν)
    (hweight : ((3 - r : ℕ) : ℝ) * tailHolderWeight E b ν j ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((1 + x ^ 2) ^
          (-(3 / (4 * ((3 - r : ℕ) : ℝ) *
            tailHolderWeight E b ν j) : ℝ)) *
        Real.exp
          (-(2 * (b j / 2) ^ 2 / tailHolderWeight E b ν j) *
            x ^ 2 / (1 + x ^ 2)))) ≤
      ENNReal.ofReal
          (2 * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν))) *
        threeQuarterKernelConstant := by
  have hα : 0 < tailHolderWeight E b ν j := by
    unfold tailHolderWeight
    positivity
  have htail := tail_scalar_sharp_of_r r hr (tailHolderWeight E b ν j)
    (b j / 2) hα hweight
  refine htail.trans ?_
  gcongr
  have hmaxpos : 0 < max (1 : ℝ) |b j / 2| :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmaxcmp : max (1 : ℝ) |b j| ≤ 2 * max 1 |b j / 2| := by
    apply max_le
    · nlinarith [le_max_left (1 : ℝ) |b j / 2|]
    · rw [abs_div]
      norm_num
      nlinarith [le_max_right (1 : ℝ) (|b j| / 2)]
  have hratio :
      Real.sqrt (tailHolderWeight E b ν j) / max 1 |b j / 2| ≤
        2 * (Real.sqrt (tailHolderWeight E b ν j) / max 1 |b j|) := by
    have hmaxorig : 0 < max (1 : ℝ) |b j| :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    calc
      _ ≤ (2 * Real.sqrt (tailHolderWeight E b ν j)) / max 1 |b j| := by
        apply (div_le_div_iff₀ hmaxpos hmaxorig).2
        nlinarith [Real.sqrt_nonneg (tailHolderWeight E b ν j)]
      _ = 2 * (Real.sqrt (tailHolderWeight E b ν j) / max 1 |b j|) := by ring
  have hbridge := sqrt_weight_div_max_le (E j) (b j) ν hν
  have hcore :
      Real.sqrt (tailHolderWeight E b ν j) / max 1 |b j / 2| ≤
        2 * (Real.sqrt 2 * |E j| / ν) := by
    calc
      _ ≤ 2 * (Real.sqrt (tailHolderWeight E b ν j) / max 1 |b j|) := hratio
      _ ≤ 2 * (Real.sqrt 2 * |E j| / ν) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [tailHolderWeight] using hbridge) (by norm_num)
  calc
    Real.sqrt 3 * Real.sqrt (tailHolderWeight E b ν j) / max 1 |b j / 2| =
        Real.sqrt 3 *
          (Real.sqrt (tailHolderWeight E b ν j) / max 1 |b j / 2|) := by ring
    _ ≤ Real.sqrt 3 * (2 * (Real.sqrt 2 * |E j| / ν)) :=
      mul_le_mul_of_nonneg_left hcore (Real.sqrt_nonneg 3)
    _ = 2 * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν)) := by ring

/-- After the two exact affine changes `η ↦ ξ E² + η E` and `x = 2ζ`,
the tail factor has a bound independent of `ξ`. -/
theorem tailHolder_inner_lintegral_le {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (hr : r ≤ 2) (ν : ℝ) (j : Fin n)
    (hE : E j ≠ 0) (hν : 0 < ν)
    (hweight : ((3 - r : ℕ) : ℝ) * tailHolderWeight E b ν j ≤ 1)
    (ξ : ℝ) :
    (∫⁻ η : ℝ, ENNReal.ofReal
      ((1 + 4 * (tailAffineFrequency (E j) ξ η) ^ 2) ^
          (-(3 / (4 * ((3 - r : ℕ) : ℝ) *
            tailHolderWeight E b ν j) : ℝ)) *
        Real.exp
          (-(2 * b j ^ 2 / tailHolderWeight E b ν j) *
            (tailAffineFrequency (E j) ξ η) ^ 2 /
              (1 + 4 * (tailAffineFrequency (E j) ξ η) ^ 2)))) ≤
      ENNReal.ofReal
          ((1 / |E j|) * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν))) *
        threeQuarterKernelConstant := by
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal
    ((1 + x ^ 2) ^
        (-(3 / (4 * ((3 - r : ℕ) : ℝ) * tailHolderWeight E b ν j) : ℝ)) *
      Real.exp (-(2 * (b j / 2) ^ 2 / tailHolderWeight E b ν j) *
        x ^ 2 / (1 + x ^ 2)))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hη := lintegral_comp_affine (fun ζ => f (2 * ζ)) (by fun_prop)
    (ξ * (E j) ^ 2) (E j) hE
  have htwo := lintegral_comp_affine f hf 0 2 (by norm_num)
  have hscalar := tail_scalar_sharp_half_weighted E b r hr ν j hE hν hweight
  have hrewrite :
      (∫⁻ η : ℝ, ENNReal.ofReal
        ((1 + 4 * (tailAffineFrequency (E j) ξ η) ^ 2) ^
            (-(3 / (4 * ((3 - r : ℕ) : ℝ) *
              tailHolderWeight E b ν j) : ℝ)) *
          Real.exp
            (-(2 * b j ^ 2 / tailHolderWeight E b ν j) *
              (tailAffineFrequency (E j) ξ η) ^ 2 /
                (1 + 4 * (tailAffineFrequency (E j) ξ η) ^ 2)))) =
        ENNReal.ofReal |(E j)⁻¹| * ENNReal.ofReal (1 / 2) *
          (∫⁻ x : ℝ, f x) := by
    calc
      _ = ∫⁻ η : ℝ, f (2 * (ξ * (E j) ^ 2 + E j * η)) := by
        apply lintegral_congr
        intro η
        simp only [f, tailAffineFrequency]
        congr 2 <;> ring
      _ = ENNReal.ofReal |(E j)⁻¹| * ∫⁻ ζ : ℝ, f (2 * ζ) := hη
      _ = ENNReal.ofReal |(E j)⁻¹| *
          (ENNReal.ofReal |(2 : ℝ)⁻¹| * ∫⁻ x : ℝ, f x) := by
        rw [show (∫⁻ ζ : ℝ, f (2 * ζ)) =
          ENNReal.ofReal |(2 : ℝ)⁻¹| * ∫⁻ x : ℝ, f x by
            simpa only [zero_add] using htwo]
      _ = ENNReal.ofReal |(E j)⁻¹| * ENNReal.ofReal (1 / 2) *
          (∫⁻ x : ℝ, f x) := by
        norm_num
        ring
  rw [hrewrite]
  calc
    _ ≤ ENNReal.ofReal |(E j)⁻¹| * ENNReal.ofReal (1 / 2) *
        (ENNReal.ofReal (2 * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν))) *
          threeQuarterKernelConstant) := by gcongr
    _ = ENNReal.ofReal
          ((1 / |E j|) * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν))) *
        threeQuarterKernelConstant := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ |(E j)⁻¹|),
        ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity :
          (0 : ℝ) ≤ |(E j)⁻¹| * (1 / 2))]
      congr 1
      apply congrArg ENNReal.ofReal
      rw [abs_inv]
      field_simp

private theorem xi_kernel_scale_identity (δ u : ℝ) (hδ : 0 < δ) :
    (((δ * u) ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) =
      (1 / (δ * Real.sqrt δ)) *
        ((1 + u ^ 2) ^ (-(3 : ℝ) / 4)) := by
  have hbase : (δ * u) ^ 2 + δ ^ 2 = δ ^ 2 * (1 + u ^ 2) := by ring
  rw [hbase, Real.mul_rpow (sq_nonneg δ) (by positivity)]
  congr 1
  calc
    (δ ^ 2) ^ (-(3 : ℝ) / 4) = δ ^ ((2 : ℝ) * (-(3 : ℝ) / 4)) := by
      rw [Real.rpow_mul hδ.le, Real.rpow_two]
    _ = δ ^ (-1 + (-(1 / 2 : ℝ))) := by norm_num
    _ = δ ^ (-1 : ℝ) * δ ^ (-(1 / 2 : ℝ)) := Real.rpow_add hδ _ _
    _ = δ⁻¹ * (Real.sqrt δ)⁻¹ := by
      rw [Real.rpow_neg hδ.le, Real.rpow_one, Real.rpow_neg hδ.le,
        ← Real.sqrt_eq_rpow]
    _ = 1 / (δ * Real.sqrt δ) := by field_simp

/-- Exact `ξ/δ` scaling of the common shifted kernel. -/
theorem xi_kernel_lintegral_eq (δ : ℝ) (hδ : 0 < δ) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal
      ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4))) =
      ENNReal.ofReal (1 / Real.sqrt δ) * threeQuarterKernelConstant := by
  let k : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal
    ((1 + u ^ 2) ^ (-(3 : ℝ) / 4))
  have hk : Measurable k := by
    dsimp [k]
    fun_prop
  have hscale := lintegral_comp_affine k hk 0 δ⁻¹ (inv_ne_zero hδ.ne')
  have hconst : (∫⁻ u : ℝ, k u) = threeQuarterKernelConstant := by
    unfold threeQuarterKernelConstant
    apply lintegral_congr
    intro u
    rw [Real.enorm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    simp only [k, Real.norm_eq_abs, sq_abs]
  calc
    (∫⁻ ξ : ℝ, ENNReal.ofReal ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4))) =
        ∫⁻ ξ : ℝ, ENNReal.ofReal (1 / (δ * Real.sqrt δ)) * k (δ⁻¹ * ξ) := by
      apply lintegral_congr
      intro ξ
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (δ * Real.sqrt δ))]
      rw [← xi_kernel_scale_identity δ (δ⁻¹ * ξ) hδ]
      congr 2
      field_simp
    _ = ENNReal.ofReal (1 / (δ * Real.sqrt δ)) *
        (∫⁻ ξ : ℝ, k (0 + δ⁻¹ * ξ)) := by
      rw [lintegral_const_mul]
      · simp only [zero_add]
      · exact hk.comp (measurable_const.mul measurable_id)
    _ = ENNReal.ofReal (1 / (δ * Real.sqrt δ)) *
        (ENNReal.ofReal |(δ⁻¹)⁻¹| * ∫⁻ u : ℝ, k u) := by rw [hscale]
    _ = ENNReal.ofReal (1 / Real.sqrt δ) * threeQuarterKernelConstant := by
      rw [hconst, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (δ * Real.sqrt δ))]
      congr 1
      apply congrArg ENNReal.ofReal
      rw [inv_inv, abs_of_pos hδ]
      field_simp

/-- Coordinate bound.  The hypotheses are precisely the nondegeneracy
`E j ≠ 0`, the contour scale `δ = 1/(10ν²)`, and the Hölder-weight
restriction `(3 - r) w_j ≤ 1`, `w_j = tailHolderWeight E b ν j`. -/
theorem tailHolderCoordinate_lintegral_le {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (hr : r ≤ 2) (ν δ : ℝ) (j : Fin n)
    (hE : E j ≠ 0) (hν : 0 < ν)
    (hδ : δ = 1 / (10 * ν ^ 2))
    (hweight : ((3 - r : ℕ) : ℝ) * tailHolderWeight E b ν j ≤ 1) :
    (∫⁻ x : ℝ × ℝ, tailHolderCoordinate E b r ν δ j x) ≤
      ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
        threeQuarterKernelConstant ^ 2 := by
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hinner := fun ξ => tailHolder_inner_lintegral_le E b r hr ν j hE hν hweight ξ
  rw [Measure.volume_eq_prod ℝ ℝ, MeasureTheory.lintegral_prod]
  swap
  · simpa only [Measure.volume_eq_prod] using
      (tailHolderCoordinate_aemeasurable E b r ν δ j)
  have hsep :
      (∫⁻ ξ : ℝ, ∫⁻ η : ℝ, tailHolderCoordinate E b r ν δ j (ξ, η)) ≤
        (∫⁻ ξ : ℝ, ENNReal.ofReal
          ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4))) *
        (ENNReal.ofReal
          ((1 / |E j|) * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν))) *
          threeQuarterKernelConstant) := by
    calc
      _ ≤ ∫⁻ ξ : ℝ, ENNReal.ofReal
          ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4)) *
          (ENNReal.ofReal
            ((1 / |E j|) * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν))) *
            threeQuarterKernelConstant) := by
        apply lintegral_mono
        intro ξ
        unfold tailHolderCoordinate
        simp only
        simp_rw [mul_assoc]
        conv_lhs =>
          enter [2, η]
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
        rw [lintegral_const_mul]
        · gcongr
          simpa only [mul_assoc] using hinner ξ
        · unfold tailAffineFrequency
          fun_prop
      _ = (∫⁻ ξ : ℝ, ENNReal.ofReal
          ((ξ ^ 2 + δ ^ 2) ^ (-(3 : ℝ) / 4))) *
          (ENNReal.ofReal
            ((1 / |E j|) * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν))) *
            threeQuarterKernelConstant) := by
        rw [lintegral_mul_const]
        exact ENNReal.measurable_ofReal.comp (by fun_prop)
  refine hsep.trans ?_
  rw [xi_kernel_lintegral_eq δ hδpos]
  have hpref := shifted_scalar_prefactor_uniform (E j) ν δ hE hν hδ
  have hpref' :
      (1 / Real.sqrt δ) *
        ((1 / |E j|) * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν))) =
        Real.sqrt 30 * Real.sqrt 2 := by
    calc
      _ = (1 / (|E j| * Real.sqrt δ)) *
          (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν)) := by ring
      _ = _ := hpref
  calc
    (ENNReal.ofReal (1 / Real.sqrt δ) * threeQuarterKernelConstant) *
        (ENNReal.ofReal
          ((1 / |E j|) * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν))) *
          threeQuarterKernelConstant) =
      (ENNReal.ofReal (1 / Real.sqrt δ) * ENNReal.ofReal
        ((1 / |E j|) * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν)))) *
        threeQuarterKernelConstant ^ 2 := by ring
    _ = ENNReal.ofReal
        ((1 / Real.sqrt δ) *
          ((1 / |E j|) * (Real.sqrt 3 * (Real.sqrt 2 * |E j| / ν)))) *
        threeQuarterKernelConstant ^ 2 := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt δ)]
    _ ≤ ENNReal.ofReal (Real.sqrt 30 * Real.sqrt 2) *
        threeQuarterKernelConstant ^ 2 := by
      rw [hpref']

end PSSSNative.BlockBand.PSSS
