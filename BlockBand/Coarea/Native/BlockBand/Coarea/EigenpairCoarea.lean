module

public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairJacobianLocal
public import BlockBand.Coarea.Native.BlockBand.Spectral.Measurable.OrderedSpectrum
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Global chart assembly for eigenpair coarea

Mathlib's finite-dimensional Jacobian theorem applies to one injective chart at a
time.  The eigenpair map is not globally injective: on the simple-spectrum locus it
has one sheet for each ordered eigenvalue, while the repeated-spectrum discriminant
must be discarded as a null set.  This file proves the global assembly
lemma.  It turns a finite family of ordered, injective, differentiable eigenpair
charts, each covering the same full-measure simple-spectrum locus and carrying the
exact squared gap determinant, into the sum-over-selected-eigenpairs integral
identity of the eigenpair Jacobian lemma.

The theorem is conditional on `EigenpairCoareaAtlas`: `d` injective differentiable charts on
measurable sources, each with image the simple-spectrum locus (whose complement is null) and
with absolute Jacobian determinant equal to the gap density.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Set
open scoped ENNReal

/-- Data needed to globalize the local eigenpair Jacobian over the `d` ordered
simple eigenpairs.

`simpleSpectrum` is the good locus and its complement is the repeated-spectrum
discriminant.  For each ordered rank `r : Fin d`, `chart r` parametrizes the same
good locus injectively from `source r`.  The field `abs_det_deriv_eq_gapDensity`
identifies Mathlib's real Jacobian determinant with the exact squared spectral-gap
density proved locally in `EigenpairJacobianLocal`.

This is an explicit integration input, not an unconditional assertion that such an
atlas has already been constructed for Hermitian matrices. -/
structure EigenpairCoareaAtlas
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (d : ℕ) (μ : Measure E) where
  simpleSpectrum : Set E
  source : Fin d → Set E
  chart : Fin d → E → E
  deriv : Fin d → E → E →L[ℝ] E
  gapDensity : Fin d → E → ℝ
  source_measurable : ∀ r, MeasurableSet (source r)
  chart_hasFDerivWithinAt : ∀ r x, x ∈ source r →
    HasFDerivWithinAt (chart r) (deriv r x) (source r) x
  chart_injOn : ∀ r, InjOn (chart r) (source r)
  chart_image : ∀ r, chart r '' source r = simpleSpectrum
  discriminant_null : μ (simpleSpectrum)ᶜ = 0
  abs_det_deriv_eq_gapDensity : ∀ r x, x ∈ source r →
    |(deriv r x).det| = gapDensity r x

/-- One ordered eigenpair chart gives a global integral identity once its image
misses only the null discriminant.

This is the Mathlib change-of-variables step: the left side integrates an
observable of the reconstructed matrix on the whole ambient space, while the right
side integrates its pullback against the squared-gap Jacobian density on the chart. -/
theorem EigenpairCoareaAtlas.lintegral_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {d : ℕ} {μ : Measure E} [μ.IsAddHaarMeasure]
    (A : EigenpairCoareaAtlas E d μ) (r : Fin d)
    (g : E → ℝ≥0∞) :
    (∫⁻ K, g K ∂μ) =
      ∫⁻ x in A.source r,
        ENNReal.ofReal (A.gapDensity r x) * g (A.chart r x) ∂μ := by
  have hrestrict : μ.restrict A.simpleSpectrum = μ := by
    exact Measure.restrict_eq_self_of_ae_mem A.discriminant_null
  calc
    (∫⁻ K, g K ∂μ) = ∫⁻ K in A.simpleSpectrum, g K ∂μ := by
      rw [hrestrict]
    _ = ∫⁻ K in A.chart r '' A.source r, g K ∂μ := by
      rw [A.chart_image r]
    _ = ∫⁻ x in A.source r,
        ENNReal.ofReal |(A.deriv r x).det| * g (A.chart r x) ∂μ :=
      MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul μ
        (A.source_measurable r)
        (A.chart_hasFDerivWithinAt r) (A.chart_injOn r) g
    _ = ∫⁻ x in A.source r,
        ENNReal.ofReal (A.gapDensity r x) * g (A.chart r x) ∂μ := by
      apply MeasureTheory.setLIntegral_congr_fun (A.source_measurable r)
      intro x hx
      simp only [A.abs_det_deriv_eq_gapDensity r x hx]

/-- Global finite-sheet eigenpair coarea identity for nonnegative observables.

The left side is the paper's sum over the `d` selected ordered simple
eigenpairs.  The right side is the sum of their coordinate integrals with the exact
squared-gap density.  Repeated eigenvalues contribute nothing because
`discriminant_null` is part of the atlas data. -/
theorem EigenpairCoareaAtlas.lintegral_sum_selectedEigenpairs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {d : ℕ} {μ : Measure E} [μ.IsAddHaarMeasure]
    (A : EigenpairCoareaAtlas E d μ) (g : Fin d → E → ℝ≥0∞) :
    (∑ r : Fin d, ∫⁻ K, g r K ∂μ) =
      ∑ r : Fin d, ∫⁻ x in A.source r,
        ENNReal.ofReal (A.gapDensity r x) * g r (A.chart r x) ∂μ := by
  apply Finset.sum_congr rfl
  intro r _
  exact A.lintegral_chart r (g r)

/-- Constant-observable specialization: the total weighted volume of every ordered
chart is the ambient volume, with the repeated-spectrum discriminant removed only
on a null set. -/
theorem EigenpairCoareaAtlas.lintegral_gapDensity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {d : ℕ} {μ : Measure E} [μ.IsAddHaarMeasure]
    (A : EigenpairCoareaAtlas E d μ) (r : Fin d) :
    (∫⁻ _ : E, (1 : ℝ≥0∞) ∂μ) =
      ∫⁻ x in A.source r, ENNReal.ofReal (A.gapDensity r x) ∂μ := by
  simpa using A.lintegral_chart r (fun _ => (1 : ℝ≥0∞))

end CoareaNative.BlockBand
