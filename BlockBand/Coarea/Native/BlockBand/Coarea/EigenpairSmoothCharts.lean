module

public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairAtlasReconstruction
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Smooth ordered eigenpair chart assembly

This module proves that the minimal smooth-chart completion isolated in
`EigenpairAtlasReconstruction` is sufficient for the complete finite-chart
change-of-variables step.  Each chart image is measurable, different least-entry
charts have disjoint images, and Mathlib's finite-dimensional Jacobian theorem
applies chart by chart.  Summing the chart identities gives an unconditional
assembly theorem from the full-measure simple-spectrum locus to the exact local
Jacobian densities supplied by a completion.

The only remaining geometric input is therefore an inhabitant of
`OrderedEigenpairSmoothChartCompletion`: equivalently, a smooth phase-fixed
unitary completion of the explicitly selected eigenline, together with its
orthogonal-complement coordinates and the already computed local derivative.
No existence of such a smooth unitary frame is asserted here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Set
open scoped ENNReal

/-- The image of a completed smooth chart is measurable.  This is obtained from
its exact identification with the corresponding measurable least-entry region,
not from a general (false) assertion that continuous images are measurable. -/
theorem OrderedEigenpairSmoothChartCompletion.measurableSet_decode_image
    {d : ℕ} {r : HermitianEigenRank d}
    (C : OrderedEigenpairSmoothChartCompletion d r)
    (p : OrderedEigenlineChartIndex d) :
    MeasurableSet (C.decode p '' C.source p) := by
  rw [C.decode_image p]
  exact (measurableSet_hermitianSimpleSpectrumCoordinates d).subtype_image
    (measurableSet_orderedEigenpairReconstructionChartRegion d r p)

/-- Distinct completed smooth chart images are disjoint because they are exactly
the images of the disjoint least-entry regions under the injective subtype
inclusion. -/
theorem OrderedEigenpairSmoothChartCompletion.disjoint_decode_image
    {d : ℕ} {r : HermitianEigenRank d}
    (C : OrderedEigenpairSmoothChartCompletion d r)
    {p q : OrderedEigenlineChartIndex d} (hpq : p ≠ q) :
    Disjoint (C.decode p '' C.source p) (C.decode q '' C.source q) := by
  rw [C.decode_image p, C.decode_image q, Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have hsub : x = y := Subtype.ext hxy.symm
  subst y
  exact Set.disjoint_left.1
    (disjoint_orderedEigenpairReconstructionChartRegion r hpq) hx hy

/-- One completed phase-fixed chart satisfies the exact real
change-of-variables identity with its declared local Jacobian density. -/
theorem OrderedEigenpairSmoothChartCompletion.lintegral_decode_chart
    {d : ℕ} {r : HermitianEigenRank d}
    (C : OrderedEigenpairSmoothChartCompletion d r)
    (p : OrderedEigenlineChartIndex d)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in C.decode p '' C.source p, g K) =
      ∫⁻ y in C.source p,
        ENNReal.ofReal (C.gapDensity p y) * g (C.decode p y) := by
  calc
    (∫⁻ K in C.decode p '' C.source p, g K) =
        ∫⁻ y in C.source p,
          ENNReal.ofReal |(C.deriv p y).det| * g (C.decode p y) :=
      MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        (C.source_measurable p) (C.decode_hasFDerivWithinAt p)
        (C.decode_injOn p) g
    _ = ∫⁻ y in C.source p,
        ENNReal.ofReal (C.gapDensity p y) * g (C.decode p y) := by
      apply MeasureTheory.setLIntegral_congr_fun (C.source_measurable p)
      intro y hy
      change ENNReal.ofReal |(C.deriv p y).det| * g (C.decode p y) =
        ENNReal.ofReal (C.gapDensity p y) * g (C.decode p y)
      rw [C.abs_det_deriv_eq_gapDensity p y hy]

/-- The completed chart images form a pairwise-disjoint family. -/
theorem OrderedEigenpairSmoothChartCompletion.pairwise_disjoint_decode_image
    {d : ℕ} {r : HermitianEigenRank d}
    (C : OrderedEigenpairSmoothChartCompletion d r) :
    Pairwise (Function.onFun Disjoint fun p : OrderedEigenlineChartIndex d =>
      C.decode p '' C.source p) := by
  intro p q hpq
  exact C.disjoint_decode_image hpq

/-- Global finite-chart coarea assembly for one ordered eigenvalue rank.

The left side is the ambient Lebesgue integral.  The repeated-spectrum
polynomial discriminant is null, while the completed chart images are measurable,
pairwise disjoint, and cover the simple-spectrum locus.  The right side is the
finite sum of the exact local Jacobian integrals. -/
theorem OrderedEigenpairSmoothChartCompletion.lintegral_sum_charts
    {d : ℕ} {r : HermitianEigenRank d}
    (C : OrderedEigenpairSmoothChartCompletion d r)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K, g K) =
      ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ y in C.source p,
          ENNReal.ofReal (C.gapDensity p y) * g (C.decode p y) := by
  have hrestrict : volume.restrict (hermitianSimpleSpectrumCoordinates d) =
      (volume : Measure (HermitianCoordinateSpace d)) :=
    Measure.restrict_eq_self_of_ae_mem
      (volume_hermitianSimpleSpectrumCoordinates_compl d)
  calc
    (∫⁻ K, g K) =
        ∫⁻ K in hermitianSimpleSpectrumCoordinates d, g K := by
      rw [hrestrict]
    _ = ∫⁻ K in ⋃ p : OrderedEigenlineChartIndex d,
          C.decode p '' C.source p, g K := by
      rw [C.iUnion_decode_image]
    _ = ∑' p : OrderedEigenlineChartIndex d,
          ∫⁻ K in C.decode p '' C.source p, g K :=
      MeasureTheory.lintegral_iUnion
        C.measurableSet_decode_image C.pairwise_disjoint_decode_image g
    _ = ∑' p : OrderedEigenlineChartIndex d,
          ∫⁻ y in C.source p,
            ENNReal.ofReal (C.gapDensity p y) * g (C.decode p y) := by
      apply tsum_congr
      intro p
      exact C.lintegral_decode_chart p g
    _ = ∑ p : OrderedEigenlineChartIndex d,
          ∫⁻ y in C.source p,
            ENNReal.ofReal (C.gapDensity p y) * g (C.decode p y) := by
      exact tsum_fintype _

/-- The exact remaining external geometric datum for all ordered ranks.  An
inhabitant consists only of the smooth phase-fixed chart completions; all
measurable disjointization, discriminant removal, injectivity, coverage, and
change-of-variables assembly are theorems above. -/
structure OrderedEigenpairSmoothAtlasInput (d : ℕ) where
  completion : ∀ r : HermitianEigenRank d,
    OrderedEigenpairSmoothChartCompletion d r

/-- Sum the completed finite-chart coarea identities over every selected ordered
eigenpair. -/
theorem OrderedEigenpairSmoothAtlasInput.lintegral_sum_orderedEigenpairs
    {d : ℕ} (A : OrderedEigenpairSmoothAtlasInput d)
    (g : HermitianEigenRank d → HermitianCoordinateSpace d → ℝ≥0∞) :
    (∑ r : HermitianEigenRank d, ∫⁻ K, g r K) =
      ∑ r : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
          ∫⁻ y in (A.completion r).source p,
            ENNReal.ofReal ((A.completion r).gapDensity p y) *
              g r ((A.completion r).decode p y) := by
  apply Finset.sum_congr rfl
  intro r _
  exact (A.completion r).lintegral_sum_charts (g r)

end CoareaNative.BlockBand
