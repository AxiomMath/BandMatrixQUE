module

public import BlockBand.Counting.CircularGaussianMoments

/-!
# Circular mixed monomials through fourth order

For a standard circular complex Gaussian `Z`, the mixed moments `E[Z^a conj(Z)^b]` with
`a, b ≤ 2` are integrable and computed exactly: unbalanced moments vanish by rotation
invariance, and the balanced moments are `1` and `2`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate NNReal

/-- Quarter-turn of the real/imaginary sample coordinates. -/
def circularQuarterTurn (z : ℝ × ℝ) : ℝ × ℝ := (-z.2, z.1)

/-- Rotation by `i` preserves the circular law. -/
theorem circularQuarterTurn_law :
    Measure.map circularQuarterTurn standardCircularGaussian = standardCircularGaussian := by
  have hn : Measure.map (fun x : ℝ => -x) standardCircularReal = standardCircularReal := by
    simpa [standardCircularReal] using
      (gaussianReal_map_neg (μ := 0) (v := (1 / 2 : ℝ≥0)))
  have hrot : circularQuarterTurn = (Prod.map (fun x : ℝ => -x) id) ∘ Prod.swap := rfl
  rw [hrot, ← Measure.map_map (by fun_prop) measurable_swap,
    standardCircularGaussian, Measure.prod_swap, ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    hn, Measure.map_id]

theorem circularGaussianCoordinate_quarterTurn (z : ℝ × ℝ) :
    circularGaussianCoordinate (circularQuarterTurn z) =
      Complex.I * circularGaussianCoordinate z := by
  apply Complex.ext <;> simp [circularGaussianCoordinate, circularQuarterTurn]

/-- Mixed monomial integrability under the scalar circular law. -/
theorem integrable_circular_monomial (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) :
    Integrable (fun z => conj (circularGaussianCoordinate z) ^ a *
      circularGaussianCoordinate z ^ b) standardCircularGaussian := by
  refine (integrable_circular_normSq_sq.add (integrable_const 1)).mono'
    (by unfold circularGaussianCoordinate; fun_prop) ?_
  filter_upwards with z
  have hnorm : ‖circularGaussianCoordinate z‖ ^ 2 = z.1 ^ 2 + z.2 ^ 2 := by
    rw [Complex.sq_norm]
    simp [circularGaussianCoordinate, Complex.normSq_apply, pow_two]
  have hq := norm_nonneg (circularGaussianCoordinate z)
  rw [norm_mul, norm_pow, norm_pow, RCLike.norm_conj, ← pow_add]
  interval_cases a <;> interval_cases b <;> norm_num <;> nlinarith [sq_nonneg
    (‖circularGaussianCoordinate z‖ - 1), sq_nonneg (‖circularGaussianCoordinate z‖ ^ 2 - 1)]

/-- Exact mixed scalar monomials, including the vanishing unbalanced moments.
The two balanced positive moments are 1 and 2 in the standard circular normalization. -/
theorem integral_circular_monomial (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) :
    (∫ z, conj (circularGaussianCoordinate z) ^ a * circularGaussianCoordinate z ^ b
      ∂standardCircularGaussian) =
      if a = b then (if a = 2 then 2 else 1) else 0 := by
  let m : ℂ := ∫ z, conj (circularGaussianCoordinate z) ^ a *
    circularGaussianCoordinate z ^ b ∂standardCircularGaussian
  have hr : m = (conj Complex.I ^ a * Complex.I ^ b) * m := by
    have hmeas : AEStronglyMeasurable
        (fun z => conj (circularGaussianCoordinate z) ^ a * circularGaussianCoordinate z ^ b)
        (Measure.map circularQuarterTurn standardCircularGaussian) := by
      rw [circularQuarterTurn_law]
      exact (integrable_circular_monomial a b ha hb).aestronglyMeasurable
    have hmap := integral_map (show AEMeasurable circularQuarterTurn standardCircularGaussian from
      by unfold circularQuarterTurn; fun_prop) hmeas
    rw [circularQuarterTurn_law] at hmap
    change m = _ at hmap
    calc
      m = _ := hmap
      _ = (conj Complex.I ^ a * Complex.I ^ b) * m := by
        simp_rw [circularGaussianCoordinate_quarterTurn, map_mul, mul_pow]
        simp_rw [show ∀ z : ℝ × ℝ,
          (conj Complex.I ^ a * conj (circularGaussianCoordinate z) ^ a) *
            (Complex.I ^ b * circularGaussianCoordinate z ^ b) =
          (conj Complex.I ^ a * Complex.I ^ b) *
            (conj (circularGaussianCoordinate z) ^ a * circularGaussianCoordinate z ^ b)
          from fun z => by ring]
        rw [integral_const_mul]
  by_cases hab : a = b
  · subst b
    interval_cases a
    · simp
    · simpa using integral_conj_mul_circularGaussianCoordinate
    · simp only [ite_true]
      simpa [mul_pow] using integral_conj_mul_circularGaussianCoordinate_sq
  · suffices hm : m = 0 by simpa [hab] using hm
    have hc : conj Complex.I ^ a * Complex.I ^ b ≠ 1 := by
      interval_cases a <;> interval_cases b <;> simp_all [Complex.ext_iff]
      all_goals norm_num
    exact eq_zero_of_mul_eq_self_left hc hr.symm

end BlockBand.Counting
