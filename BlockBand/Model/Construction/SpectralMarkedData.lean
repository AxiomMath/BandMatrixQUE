module

public import BlockBand.Model.Construction.SpectralSimplex
public import BlockBand.Model.Construction.SpectralAtomicContinuity

/-!
# Finite-dimensional marked spectral data

The physical marked configuration of a matrix factors through finite-dimensional data (unfolded
eigenvalues and block-weight profiles); this gives its measurability and continuity, and its
identification with the finite Dirac sum on Hermitian matrices with simple spectrum.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open MeasureTheory

/-- Finite-dimensional spectral locations and finite block-weight simplexes. -/
abbrev PhysicalSpectralData (p : Parameters) := Fin p.N → ℝ × PhysicalMassSimplex p

/-- The measurable spectral data of a raw matrix, with simplex defaults off the good locus. -/
def physicalSpectralData (p : Parameters) (H : p.SiteMatrix) : PhysicalSpectralData p :=
  fun α => (physicalOrderedEigenvalue p H α, physicalMassSimplex p H α)

/-- The spectral data map is measurable into a finite-dimensional Borel space. -/
theorem measurable_physicalSpectralData (p : Parameters) : Measurable (physicalSpectralData p) :=
  measurable_pi_iff.mpr fun α =>
    (measurable_physicalOrderedEigenvalue p α).prodMk (measurable_physicalMassSimplex p α)

/-- Physical unfolding and finite simplex profile as marked atom locations. -/
def physicalSpectralDataLocations (p : Parameters) (E : ℝ)
    (data : PhysicalSpectralData p) : Fin p.N → MarkedSpectralSpace := fun α =>
  (p.N * Parameters.semicircleDensity E * ((data α).1 - E),
    physicalSimplexProfile p (data α).2)

/-- Marked locations depend continuously on the finite-dimensional data. -/
theorem continuous_physicalSpectralDataLocations (p : Parameters) (E : ℝ) :
    Continuous (physicalSpectralDataLocations p E) := by
  apply continuous_pi
  intro α
  exact (((continuous_apply α).fst.sub continuous_const).const_mul
    (p.N * Parameters.semicircleDensity E)).prodMk
      ((continuous_physicalSimplexProfile p).comp (continuous_apply α).snd)

/-- Finite marked data mapped to the marked configuration. -/
def physicalSpectralDataMarkedConfig (p : Parameters) (E : ℝ)
    (data : PhysicalSpectralData p) : MarkedPointMeasure :=
  finiteAtomicMarkedPointMeasure (physicalSpectralDataLocations p E data)

/-- The data-to-marked-configuration map is continuous in the vague topology. -/
theorem continuous_physicalSpectralDataMarkedConfig (p : Parameters) (E : ℝ) :
    Continuous (physicalSpectralDataMarkedConfig p E) :=
  (continuous_finiteAtomicMarkedPointMeasure p.N).comp
    (continuous_physicalSpectralDataLocations p E)

/-- The finite-dimensional data-to-configuration map is Borel measurable. -/
theorem measurable_physicalSpectralDataMarkedConfig (p : Parameters) (E : ℝ) :
    Measurable (physicalSpectralDataMarkedConfig p E) :=
  (continuous_physicalSpectralDataMarkedConfig p E).measurable

/-- The physical unfolded marked configuration, on all raw matrices. -/
def physicalOrderedMarkedConfig (p : Parameters) (E : ℝ) (H : p.SiteMatrix) :
    MarkedPointMeasure := physicalSpectralDataMarkedConfig p E (physicalSpectralData p H)

/-- Measurability of the marked configuration, through the Borel data factorization. -/
theorem measurable_physicalOrderedMarkedConfig (p : Parameters) (E : ℝ) :
    Measurable (physicalOrderedMarkedConfig p E) :=
  (measurable_physicalSpectralDataMarkedConfig p E).comp (measurable_physicalSpectralData p)

/-- On the good locus, every marked atom is the physical eigenvalue/profile. -/
theorem physicalSpectralDataLocations_eq (p : Parameters) (E : ℝ) (H : p.SiteMatrix)
    (h : physicalProfileGood p H) (α : Fin p.N) :
    physicalSpectralDataLocations p E (physicalSpectralData p H) α =
      (p.N * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H α - E),
        physicalOrderedProfile p H α) := by
  simp only [physicalSpectralDataLocations, physicalSpectralData,
    physicalSimplexProfile_physicalMassSimplex p H h α]

/-- The marked configuration is the finite Dirac sum on every Hermitian matrix with simple
spectrum. -/
theorem physicalOrderedMarkedConfig_eq (p : Parameters) (E : ℝ) (H : p.SiteMatrix)
    (h : physicalProfileGood p H) :
    (physicalOrderedMarkedConfig p E H).marked.measure =
      ∑ α : Fin p.N, Measure.dirac
        (p.N * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H α - E),
          physicalOrderedProfile p H α) := by
  change finiteAtomicMeasure (physicalSpectralDataLocations p E (physicalSpectralData p H)) = _
  rw [finiteAtomicMeasure_eq_sum_dirac]
  apply Finset.sum_congr rfl
  intro α _
  rw [physicalSpectralDataLocations_eq p E H h α]

/-- The almost-sure marked-configuration identity under every physical Gaussian model. -/
theorem physicalOrderedMarkedConfig_ae (p : Parameters) (model : p.GaussianRingModel) (E : ℝ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      (physicalOrderedMarkedConfig p E H).marked.measure =
        ∑ α : Fin p.N, Measure.dirac
          (p.N * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H α - E),
            physicalOrderedProfile p H α) := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  exact physicalOrderedMarkedConfig_eq p E H ⟨hH, hsep⟩

end BlockBand.Model.Construction
