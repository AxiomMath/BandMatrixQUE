module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECompressionProjection

/-!
# Weighted Schur tail with the projected compression

The enlarged Schur-complement tail estimate holds with an arbitrary measurable weight of the
projected compression matrix `P V P`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The weighted enlarged-Schur estimate with an arbitrary measurable
functional of the projected compression matrix. -/
theorem randomCompression_enlargedSchur_tail_projectedWeight :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (n : ℕ), 0 < n → ∀ (A : HermitianMatrix (Fin (n + 1)))
      (c : ℝ) (b : Fin (2 * n) → ℝ) (t : ℝ), 1 ≤ t →
      ∀ (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ℝ≥0∞), Measurable F →
      let μ := (gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (2 * n) => gaussianReal 0 1)
      let ν := Measure.map (compressionGUECoordinates (n + 1))
        (hermitianGUECoordinateMeasure (n + 1)
          (canonicalGUEVariance (n + 1))
          (canonicalGUEVariance_nonneg (n + 1)))
      let D := fun u => zerothBlockCompression
        (A.1 + (compressionGUEHermitian (n + 1) u).1)
      let P := orthProj (canonicalFirstEuclidean (Nat.succ_pos n))
      let W := fun u : CompressionGUECoordinate (n + 1) → ℝ =>
        F (P * (compressionGUEHermitian (n + 1) u).1 * P)
      (∫⁻ z, Set.indicator {z | enlargedRealSchurEvent
          (normalizedCompressionRealMatrix n (D z.2)) c b t z.1}
          (fun _ => (1 : ℝ≥0∞)) z * W z.2 ∂μ.prod ν) ≤
        ENNReal.ofReal (K / t) * ∫⁻ u, W u ∂ν := by
  obtain ⟨K, hK, htail⟩ := randomCompression_enlargedSchur_tail_weighted
  refine ⟨K, hK, ?_⟩
  intro n hn A c b t ht F hF μ ν D P W
  exact htail n hn A c b t ht W
    (measurable_projectedCompressionWeight (Nat.succ_pos n) F hF)

end PSSSNative.BlockBand.PSSS
