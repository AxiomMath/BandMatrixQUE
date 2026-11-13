module

public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Stationarity.MeanSpatialIntensity
public import BlockBand.QUE.Invariance.PhysicalRotationLimit
public import BlockBand.Model.Construction.PhysicalSpectralLaplace

/-!
# Stationarity of critical subsequential marked laws, conditional on unit intensity

For a critical sequence, every subsequential weak limit `ν` of the marked laws is spectrally
stationary and invariant under mark rotations; under `CriticalUnitIntensity` it also has uniform
mean spatial intensity (`criticalMeanSpatialIntensity_of_unitIntensity`). Together these give
`CriticalStationarity` (`criticalStationarity_of_unitIntensity`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Stationarity

open MeasureTheory Filter
open scoped Topology

/-- Bulk energies have positive semicircle density. -/
theorem semicircleDensity_pos_of_sq_lt {E : ℝ} (hE : E ^ 2 < 4) :
    0 < Parameters.semicircleDensity E := by
  unfold Parameters.semicircleDensity
  have h1 : 0 < Real.sqrt (4 - E ^ 2) := Real.sqrt_pos.mpr (by linarith)
  positivity

/-- **The stationarity proposition, mean-intensity clause**
(`Internal.Contracts.Inputs.CriticalMeanSpatialIntensity`). For every critical sequence with
ratio `τ > 0`, bond `b ∈ (0, 1/2)`, bulk energy `E² < 4`, all finite realizations, every
strictly increasing subsequence and every weak limit `ν` of the physical marked laws, the mean
mark-weighted intensity of `ν` is `du dr`. Hypotheses: `PSSS.SourceContract` (through the
rotation clause) and `CriticalUnitIntensity` (proved as
`Native.ErdosRiabov.criticalUnitIntensity_native_er`).
-/
theorem criticalMeanSpatialIntensity_of_unitIntensity
    (source : BlockBand.External.PSSS.SourceContract.{0})
    (h : Internal.Contracts.Inputs.CriticalUnitIntensity) :
    Internal.Contracts.Inputs.CriticalMeanSpatialIntensity := by
  intro τ s hτ b E hb hb' hE R φ hφ ν hlim
  exact hasUniformSpatialIntensity_of_unit_of_rotation ν
    (h τ s hτ b E hb hb' hE R φ hφ ν hlim)
    (QUE.Invariance.criticalSequence_marked_weakLimit_rotation_invariant source s hτ b E hb hb'
      (semicircleDensity_pos_of_sq_lt hE) R φ hφ ν hlim)

/-- **The stationarity proposition, all three clauses**
(`Internal.Contracts.Inputs.CriticalStationarity`): every critical subsequential marked law
(same quantifiers as above) is spectrally stationary, invariant under simultaneous mark
rotations, and has mean spatial intensity `du dr`. Hypotheses: `PSSS.SourceContract` and
`CriticalUnitIntensity`.
-/
theorem criticalStationarity_of_unitIntensity
    (source : BlockBand.External.PSSS.SourceContract.{0})
    (h : Internal.Contracts.Inputs.CriticalUnitIntensity) :
    Internal.Contracts.Inputs.CriticalStationarity := by
  intro τ s hτ b E hb hb' hE R φ hφ ν hlim
  exact ⟨Model.Construction.criticalSequence_marked_weakLimit_spectrallyStationary s hτ b E hb hb'
      hE R φ hφ ν hlim,
    QUE.Invariance.criticalSequence_marked_weakLimit_rotation_invariant source s hτ b E hb hb'
      (semicircleDensity_pos_of_sq_lt hE) R φ hφ ν hlim,
    criticalMeanSpatialIntensity_of_unitIntensity source h τ s hτ b E hb hb' hE R φ hφ ν hlim⟩

end BlockBand.Stationarity
