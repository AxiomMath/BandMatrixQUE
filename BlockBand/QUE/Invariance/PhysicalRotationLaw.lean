module
public import BlockBand.QUE.Invariance.PhysicalRotationGrid
public import BlockBand.Model.Construction.PhysicalCanonicalLaw

/-!
# Grid-rotation invariance of the physical marked law

A cyclic shift rotates every atom of the physical ordered marked configuration at the same
increasing rank, so the canonical physical marked law, and the marked law of every finite
realization, is invariant under the grid rotations of the marks
(`canonicalPhysicalMarkedLaw_gridRotation`, `finiteRealization_markedLaw_gridRotation`).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Invariance
open Matrix MeasureTheory BlockBand.Model.Construction

/-- Every atom rotates at the same increasing rank, on the good locus. -/
theorem physicalOrderedMarkedConfig_cyclic (p : Parameters) (E : ℝ) (H : p.SiteMatrix)
    (h : physicalProfileGood p H) (s : ZMod p.n) :
    physicalOrderedMarkedConfig p E (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) =
      globalMarkedRotation (-physicalProfileGrid p s) (physicalOrderedMarkedConfig p E H) := by
  apply markedPointMeasure_eq_of_marked_measure_eq
  rw [physicalOrderedMarkedConfig_eq p E _ (physicalProfileGood_cyclic p H h s),
    globalMarkedRotation_measure, physicalOrderedMarkedConfig_eq p E H h,
    Measure.map_finset_sum' (measurable_markedLocationRotation _).aemeasurable]
  simp_rw [Measure.map_dirac' (measurable_markedLocationRotation _)]
  apply Finset.sum_congr rfl
  intro α _
  rw [BlockBand.QUE.Fourier.physical_eigenvalue_cyclic p H h.1 α s,
    physicalOrderedProfile_cyclic p H h α s]
  rfl

/-- The covariance holds almost surely under the physical Gaussian law. -/
theorem physicalOrderedMarkedConfig_cyclic_ae (p : Parameters) (model : p.GaussianRingModel)
    (E : ℝ) (s : ZMod p.n) :
    (fun H => physicalOrderedMarkedConfig p E (p.siteReindexMatrix (p.cyclicSiteEquiv s) H)) =ᵐ[
      (model.law : Measure p.SiteMatrix)]
      (fun H => globalMarkedRotation (-physicalProfileGrid p s) (physicalOrderedMarkedConfig p E H)) := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  exact physicalOrderedMarkedConfig_cyclic p E H ⟨hH,hsep⟩ s

/-- The canonical physical marked law is invariant under every grid rotation. -/
theorem canonicalPhysicalMarkedLaw_gridRotation (p : Parameters) (model : p.GaussianRingModel)
    (E : ℝ) (s : ZMod p.n) :
    globalMarkedRotationLaw (physicalProfileGrid p s) (model.canonicalPhysicalMarkedLaw E) =
      model.canonicalPhysicalMarkedLaw E := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (globalMarkedRotation (physicalProfileGrid p s))
    (Measure.map (physicalOrderedMarkedConfig p E) (model.law : Measure p.SiteMatrix)) = _
  rw [Measure.map_map (measurable_globalMarkedRotation _) (measurable_physicalOrderedMarkedConfig p E)]
  have hc := physicalOrderedMarkedConfig_cyclic_ae p model E (-s)
  simp only [physicalProfileGrid_neg, neg_neg] at hc
  change Measure.map (fun H => globalMarkedRotation (physicalProfileGrid p s)
    (physicalOrderedMarkedConfig p E H)) (model.law : Measure p.SiteMatrix) = _
  rw [← Measure.map_congr hc]
  change Measure.map (physicalOrderedMarkedConfig p E ∘ p.siteReindexMatrix (p.cyclicSiteEquiv (-s)))
    (model.law : Measure p.SiteMatrix) = _
  rw [← Measure.map_map (measurable_physicalOrderedMarkedConfig p E)
    (p.measurable_siteReindexMatrix _), model.map_cyclicMatrix]
  rfl

/-- The marked law of every finite realization is invariant under grid rotations. -/
theorem finiteRealization_markedLaw_gridRotation (p : Parameters) (R : FiniteRealization p)
    (E : ℝ) (s : ZMod p.n) :
    globalMarkedRotationLaw (physicalProfileGrid p s) (R.markedLaw E) = R.markedLaw E := by
  rw [finiteRealization_markedLaw_eq_canonical]
  exact canonicalPhysicalMarkedLaw_gridRotation p R.model E s
end BlockBand.QUE.Invariance
