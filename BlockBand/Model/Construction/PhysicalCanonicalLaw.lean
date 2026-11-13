module
public import BlockBand.Model.Construction.MarkedTranslation
public import BlockBand.Model.Construction.GaussianTranslationPhysical
public import BlockBand.QUE.Fourier.PhysicalWeightedMass
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Canonical marked law of every physical realization

For every spectral realization of a physical Gaussian model, the spectral profiles and marked
configurations agree almost surely with the canonical ones; hence the marked law of every finite
realization is the canonical physical marked law, and equals that of `constructFiniteRealization`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory
open scoped BigOperators

variable {p : Parameters} {model : p.GaussianRingModel}

theorem spectral_profile_eq_canonical_ae (spectral : p.SpectralRealization model) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ α : Fin p.N,
      spectral.profile H α = physicalOrderedProfile p H α := by
  filter_upwards [spectral.profile_ae, physicalOrderedProfile_ae p model,
    BlockBand.QUE.Haar.spectral_blockMass_eq_canonical_ae spectral] with H h1 h2 hb
  intro α
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding Torus).injective
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  have hleft := h1 α f.toContinuousMap
  have hright := h2 α f.toContinuousMap
  have hm (k : ZMod p.n) : BlockBand.QUE.Haar.physicalBlockMass spectral α H k =
      physicalOrderedBlockMass p H α k := hb α k
  change (∫ r, f r ∂(spectral.profile H α : Measure Torus)) =
    ∑ k : ZMod p.n, BlockBand.QUE.Haar.physicalBlockMass spectral α H k *
      f (QuotientAddGroup.mk ((k.val : ℝ)/p.n)) at hleft
  change (∫ r, f r ∂(physicalOrderedProfile p H α : Measure Torus)) =
    ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k *
      f (QuotientAddGroup.mk ((k.val : ℝ)/p.n)) at hright
  simp_rw [hm] at hleft
  exact hleft.trans hright.symm

theorem spectral_markedConfig_eq_canonical_ae (spectral : p.SpectralRealization model) (E : ℝ) :
    spectral.markedConfig E =ᵐ[(model.law : Measure p.SiteMatrix)] physicalOrderedMarkedConfig p E := by
  filter_upwards [spectral_profile_eq_canonical_ae spectral,
    BlockBand.QUE.Fourier.spectral_eigenvalue_eq_canonical_ae spectral,
    spectral.markedConfig_ae E, physicalOrderedMarkedConfig_ae p model E]
    with H hp he hc hcan
  apply markedPointMeasure_eq_of_marked_measure_eq
  rw [hc,hcan]
  apply Finset.sum_congr rfl
  intro α _
  rw [hp α, he α]

/-- The marked law of every finite realization equals its canonical law. -/
theorem finiteRealization_markedLaw_eq_canonical (R : FiniteRealization p) (E : ℝ) :
    R.markedLaw E = R.model.canonicalPhysicalMarkedLaw E := by
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.map_congr (spectral_markedConfig_eq_canonical_ae R.spectral E)

/-- Every finite physical realization has the same unfolded marked law as
`constructFiniteRealization`. -/
theorem finiteRealization_markedLaw_eq_constructed (R : FiniteRealization p) (E : ℝ) :
    R.markedLaw E = (constructFiniteRealization p).markedLaw E := by
  rw [finiteRealization_markedLaw_eq_canonical,
    constructFiniteRealization_markedLaw_eq_canonical]
  unfold Parameters.GaussianRingModel.canonicalPhysicalMarkedLaw
  rw [Parameters.physicalGaussianRingLaw_unique R.model p.constructGaussianRingModel]

end BlockBand.Model.Construction
