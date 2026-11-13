module

public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairSmoothCharts
public import BlockBand.Coarea.Native.BlockBand.Coarea.GaussianDensityFactor

/-!
# Paper-facing ordered eigenpair coarea assembly

This module connects the finite smooth-chart assembly to the local gap determinant,
projective normalization, and consecutive GUE normalization appearing in the RBM
coarea argument.  The only external geometry retained is the smooth phase-fixed
frame input: chart sources, two-sided reconstruction, differentiability, and the
identification of the resulting derivative density with the canonical local
`(E I - B)` density.  All finite-chart, ordered-rank, projective, and Gaussian
normalization steps are proved downstream from that input.

This replaces the older one-chart-per-rank `EigenpairCoareaAtlas` interface by the
finite disjoint atlas forced by phase gauges.  No global projective chart or
unproved smooth eigenvector choice is asserted.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory
open scoped ENNReal

/-- The single remaining geometric input in paper coordinates.

Besides the already assembled smooth finite atlas, it records the selected energy
and Hermitian complementary block in every source chart, and identifies the chart
Jacobian with the canonical local density proved in `EigenpairJacobianLocal`.
All quantifiers are pointwise in ordered rank, least-entry chart, and source point. -/
structure PaperEigenpairCoareaInput (d : ℕ) where
  smoothAtlas : OrderedEigenpairSmoothAtlasInput d
  energy : HermitianEigenRank d → OrderedEigenlineChartIndex d →
    HermitianCoordinateSpace d → ℝ
  complement : HermitianEigenRank d → OrderedEigenlineChartIndex d →
    HermitianCoordinateSpace d → Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ
  complement_isHermitian : ∀ r p y,
    y ∈ (smoothAtlas.completion r).source p →
      (complement r p y).IsHermitian
  gapDensity_eq_local : ∀ r p y,
    y ∈ (smoothAtlas.completion r).source p →
      (smoothAtlas.completion r).gapDensity p y =
        eigenpairLocalRealJacobianDensity (energy r p y) (complement r p y)

/-- The declared smooth-chart Jacobian is exactly the square of the real
spectral-gap determinant. -/
theorem PaperEigenpairCoareaInput.gapDensity_eq_detGap_sq
    {d : ℕ} (A : PaperEigenpairCoareaInput d)
    (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d)
    (y : HermitianCoordinateSpace d)
    (hy : y ∈ (A.smoothAtlas.completion r).source p) :
    (A.smoothAtlas.completion r).gapDensity p y =
      (eigenpairGapMatrix (A.energy r p y)
        (A.complement r p y)).det.re ^ 2 := by
  rw [A.gapDensity_eq_local r p y hy]
  exact eigenpairLocalRealJacobianDensity_eq_detGap_sq
    (A.energy r p y) (A.complement_isHermitian r p y hy)

/-- Paper-facing global coarea formula summed over all ordered eigenpairs and all
phase-fixed least-entry charts, with the exact squared gap determinant density. -/
theorem PaperEigenpairCoareaInput.lintegral_sum_orderedEigenpairs_detGap
    {d : ℕ} (A : PaperEigenpairCoareaInput d)
    (g : HermitianEigenRank d → HermitianCoordinateSpace d → ℝ≥0∞) :
    (∑ r : HermitianEigenRank d, ∫⁻ K, g r K) =
      ∑ r : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
          ∫⁻ y in (A.smoothAtlas.completion r).source p,
            ENNReal.ofReal
              ((eigenpairGapMatrix (A.energy r p y)
                (A.complement r p y)).det.re ^ 2) *
              g r ((A.smoothAtlas.completion r).decode p y) := by
  rw [A.smoothAtlas.lintegral_sum_orderedEigenpairs g]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro p _
  apply MeasureTheory.setLIntegral_congr_fun
    ((A.smoothAtlas.completion r).source_measurable p)
  intro y hy
  change
    ENNReal.ofReal ((A.smoothAtlas.completion r).gapDensity p y) *
        g r ((A.smoothAtlas.completion r).decode p y) =
      ENNReal.ofReal
        ((eigenpairGapMatrix (A.energy r p y)
          (A.complement r p y)).det.re ^ 2) *
        g r ((A.smoothAtlas.completion r).decode p y)
  rw [A.gapDensity_eq_detGap_sq r p y hy]

/-- The affine projective-chart integral multiplies the completed chart density
by exactly `π^(d-1)/(d-1)!` times the squared gap determinant. -/
theorem PaperEigenpairCoareaInput.projectiveIntegral_mul_gapDensity
    {d : ℕ} (hd : 1 < d) (A : PaperEigenpairCoareaInput d)
    (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d)
    (y : HermitianCoordinateSpace d)
    (hy : y ∈ (A.smoothAtlas.completion r).source p) :
    (∫ z : EuclideanSpace ℝ (Fin (2 * (d - 1))),
        ((1 + ‖z‖ ^ 2)⁻¹) ^ d) *
        (A.smoothAtlas.completion r).gapDensity p y =
      (Real.pi ^ (d - 1) / (d - 1).factorial) *
        (eigenpairGapMatrix (A.energy r p y)
          (A.complement r p y)).det.re ^ 2 := by
  rw [A.gapDensity_eq_local r p y hy]
  exact eigenpairJacobianLocalFormula hd (A.energy r p y)
    (A.complement_isHermitian r p y hy)

/-- Claim 2's paper normalization after inserting the exact chart Jacobian:
the projective mass and consecutive GUE normalizer ratio collapse to
`c_{d,t}`, leaving only the squared gap determinant. -/
theorem PaperEigenpairCoareaInput.projective_gue_mul_gapDensity
    {d : ℕ} (hd : 1 < d) {t : ℝ} (ht : 0 < t)
    (A : PaperEigenpairCoareaInput d)
    (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d)
    (y : HermitianCoordinateSpace d)
    (hy : y ∈ (A.smoothAtlas.completion r).source p) :
    ((∫ z : EuclideanSpace ℝ (Fin (2 * (d - 1))),
          ((1 + ‖z‖ ^ 2)⁻¹) ^ d) *
        (gueNormalizer (d - 1) t / gueNormalizer d t)) *
        (A.smoothAtlas.completion r).gapDensity p y =
      coareaGaussianDensityConstant d t *
        (eigenpairGapMatrix (A.energy r p y)
          (A.complement r p y)).det.re ^ 2 := by
  rw [projectiveChartIntegral_mul_gueNormalizerRatio hd ht,
    A.gapDensity_eq_detGap_sq r p y hy]

/-- The same normalization with the projective integral already evaluated.
This endpoint also makes explicit that no limit or asymptotic order is involved:
`d` and positive variance `t` are fixed throughout. -/
theorem PaperEigenpairCoareaInput.projective_constant_gue_mul_gapDensity
    {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t)
    (A : PaperEigenpairCoareaInput d)
    (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d)
    (y : HermitianCoordinateSpace d)
    (hy : y ∈ (A.smoothAtlas.completion r).source p) :
    ((Real.pi ^ (d - 1) / (d - 1).factorial) *
        (gueNormalizer (d - 1) t / gueNormalizer d t)) *
        (A.smoothAtlas.completion r).gapDensity p y =
      coareaGaussianDensityConstant d t *
        (eigenpairGapMatrix (A.energy r p y)
          (A.complement r p y)).det.re ^ 2 := by
  rw [projectiveJacobian_mul_gueNormalizerRatio hd ht,
    A.gapDensity_eq_detGap_sq r p y hy]

end CoareaNative.BlockBand
