module
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEArbitraryWeightedFixedVector
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.PublicGUE
/-!
# The weighted fixed-vector PSSS theorem

For the GUE `V` of variance `1/N`, a deterministic Hermitian `A`, a unit vector `φ`, a measurable
weight `F ≥ 0` of the compression `P V P` (`P = 1 - φφ*` the projection onto `φ⊥`) and `t ≥ 1`,
`E[1{‖(A + V)⁻¹ φ‖ ≥ t √N} F(P V P)] ≤ (C/t) E[F(P V P)]` with an absolute constant `C ≥ 1`
(`FixedVectorWeighted`, `fixedVector_tail_weighted`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace PSSSNative.BlockBand.PSSS
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The weighted fixed-vector inverse tail with constant `C`: for every `N > 0`, Hermitian `A`,
unit `φ`, measurable `F ≥ 0` and `t ≥ 1`, under `GUE N (1/N)`,
`E[1{‖(A + V)⁻¹ φ‖ ≥ t √N} F(P V P)] ≤ (C/t) E[F(P V P)]`. -/
def FixedVectorWeighted (C : ℝ) : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (A : HermitianMatrix (Fin N))
    (φ : EuclideanSpace ℂ (Fin N)), ‖φ‖ = 1 →
    ∀ (F : (Matrix (Fin N) (Fin N) ℂ) → ℝ≥0∞), Measurable F →
    ∀ t : ℝ, 1 ≤ t →
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
            Measure (HermitianMatrix (Fin N)))

/-- **Weighted fixed-vector inverse tail.**  There is an absolute constant `C ≥ 1`, chosen
before the dimension, deformation, unit vector, measurable compression weight and threshold,
with `FixedVectorWeighted C`. -/
theorem fixedVector_tail_weighted :
    ∃ C : ℝ, 1 ≤ C ∧ FixedVectorWeighted C := by
  obtain ⟨C, hC, htail⟩ := canonicalGUE_arbitraryUnitVector_inverse_tail_weighted
  refine ⟨C, hC, ?_⟩
  intro N hN A φ hφ F hF t ht
  have hv : 0 ≤ (1 / (N : ℝ)) := by positivity
  rw [PSSSNative.BlockBand.GUE_toMeasure_eq_canonicalHermitianGUEPushforward
    N (1 / (N : ℝ)) hv]
  simpa only [canonicalGUEVariance] using htail N hN A φ hφ F hF t ht

end PSSSNative.BlockBand.PSSS
