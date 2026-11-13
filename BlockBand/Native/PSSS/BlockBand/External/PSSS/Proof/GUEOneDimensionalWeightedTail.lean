module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WeightedEventTransport
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEOneDimensionalFixedVector

/-!
# Weighted fixed-vector tail in dimension one

The compression is the zero matrix in dimension one, hence every admissible
compression weight is constant.  This closes the empty-compression branch of
the weighted fixed-vector theorem without appealing to an unweighted theorem
in positive compression dimension.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- In dimension one, projection away from the canonical coordinate is zero. -/
theorem orthProj_canonicalFirst_one_eq_zero :
    orthProj (canonicalFirstEuclidean (by norm_num : 0 < 1)) =
      (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [orthProj, canonicalFirstEuclidean, phaseFixedCoordinateVector,
    Matrix.vecMulVec_apply]

/-- Weighted canonical fixed-vector inverse tail in the empty-compression
case. -/
theorem canonicalGUE_one_fixedVector_inverse_tail_weighted
    (A : HermitianMatrix (Fin 1)) (t : ℝ) (ht : 1 ≤ t)
    (F : Matrix (Fin 1) (Fin 1) ℂ → ℝ≥0∞) :
    let P := orthProj (canonicalFirstEuclidean (by norm_num : 0 < 1))
    (∫⁻ V, Set.indicator {V : HermitianMatrix (Fin 1) |
        t ≤ ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ canonicalUnitVectorOne) :
          EuclideanSpace ℂ (Fin 1))‖} (fun _ => (1 : ℝ≥0∞)) V *
        F (P * V.1 * P)
      ∂canonicalHermitianGUEPushforward 1 (canonicalGUEVariance 1)
        (canonicalGUEVariance_nonneg 1)) ≤
      ENNReal.ofReal (2 / t) *
        ∫⁻ V, F (P * V.1 * P)
          ∂canonicalHermitianGUEPushforward 1 (canonicalGUEVariance 1)
            (canonicalGUEVariance_nonneg 1) := by
  intro P
  have htail := canonicalGUE_one_fixedVector_inverse_tail A t ht
  have hP : P = 0 := orthProj_canonicalFirst_one_eq_zero
  rw [hP]
  simp only [zero_mul, mul_zero]
  let μ := canonicalHermitianGUEPushforward 1 (canonicalGUEVariance 1)
    (canonicalGUEVariance_nonneg 1)
  let _ : IsProbabilityMeasure μ := by
    unfold μ canonicalHermitianGUEPushforward
    infer_instance
  let B : Set (HermitianMatrix (Fin 1)) := {V |
    t ≤ ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ canonicalUnitVectorOne) :
      EuclideanSpace ℂ (Fin 1))‖}
  have hB : MeasurableSet B := by
    unfold B
    have hm : Measurable fun V : HermitianMatrix (Fin 1) => (A.1 + V.1)⁻¹ :=
      PSSSNative.BlockBand.Measurable.matrixNonsingInv
        ((continuous_const.add continuous_subtype_val).measurable)
    apply measurableSet_le measurable_const
    fun_prop
  rw [show (∫⁻ V, Set.indicator B (fun _ => (1 : ℝ≥0∞)) V * F 0 ∂μ) =
      μ B * F 0 by
    rw [show (fun V => Set.indicator B (fun _ => (1 : ℝ≥0∞)) V * F 0) =
        fun V => F 0 * Set.indicator B (fun _ => (1 : ℝ≥0∞)) V by
      funext V
      ac_rfl]
    rw [lintegral_const_mul (F 0) (measurable_const.indicator hB)]
    rw [lintegral_indicator hB]
    simp [mul_comm]]
  rw [lintegral_const, measure_univ, mul_one]
  exact mul_le_mul_of_nonneg_right htail bot_le

end PSSSNative.BlockBand.PSSS
