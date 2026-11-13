module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.FixedVectorWeighted
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiRankOneConditioning

/-!
# Weighted fixed-vector tail at every positive threshold

The weighted fixed-vector inverse tail bound of `fixedVector_tail_weighted`, extended from `t ≥ 1`
to every `t > 0`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The weighted fixed-vector inverse tail, extended to every positive
threshold.  The compression weight and canonical normalized-GUE law are
unchanged. -/
theorem fixedVector_tail_weighted_all_positive :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (N : ℕ), 0 < N → ∀ (A : HermitianMatrix (Fin N))
      (φ : EuclideanSpace ℂ (Fin N)), ‖φ‖ = 1 →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞), Measurable F →
      ∀ t : ℝ, 0 < t →
      (∫⁻ V, Set.indicator {V : HermitianMatrix (Fin N) |
          t * Real.sqrt N ≤
            ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ WithLp.ofLp φ) :
              EuclideanSpace ℂ (Fin N))‖} (fun _ => (1 : ℝ≥0∞)) V *
          F (orthProj φ * V.1 * orthProj φ)
        ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
          Measure (HermitianMatrix (Fin N)))) ≤
        ENNReal.ofReal (C / t) *
          ∫⁻ V, F (orthProj φ * V.1 * orthProj φ)
            ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
              Measure (HermitianMatrix (Fin N))) := by
  obtain ⟨C, hC, htail⟩ := fixedVector_tail_weighted
  refine ⟨C, hC, ?_⟩
  intro N hN A φ hφ F hF t ht
  by_cases ht1 : 1 ≤ t
  · exact htail N hN A φ hφ F hF t ht1
  · exact lintegral_indicator_mul_le_scaled_of_lt_one
      (PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))
      {V : HermitianMatrix (Fin N) |
        t * Real.sqrt N ≤
          ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ WithLp.ofLp φ) :
            EuclideanSpace ℂ (Fin N))‖}
      (fun V => F (orthProj φ * V.1 * orthProj φ))
      hC ht (lt_of_not_ge ht1)

end PSSSNative.BlockBand.PSSS
