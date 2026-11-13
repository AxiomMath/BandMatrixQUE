module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoareaGoodSet
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalEigenvectorMassProfileMeasurable

/-!
# Measurable physical exceptional events for eigenpair coarea

The measurability of the exceptional events of the coarea theorem under the Gaussian-ring
law.  The full matrix is the normalized physical matrix, the exterior matrix is its principal
minor obtained by deleting the exposed physical block, and the retained mass is the
canonical phase-free measurable mass constructed from the ordered Lagrange projector.

The events (simple full spectrum, a pole-free selected energy, no common spectrum, positive
exposed mass) are shown measurable; their nullity is a separate statement, and no
absolute-continuity or conditional-density input is used.

Ordered ranks are zero-based.  All assertions are at fixed `n`, `W`, exposed block, and ordered
rank, with no asymptotic uniformity or limit.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Physical indices outside the exposed block `j`. -/
abbrev PhysicalExteriorIndex (p : Params) (j : Fin p.n) :=
  {x : PhysicalIndex p // x.1 ≠ j}

/-- The normalized physical principal minor outside block `j`. -/
def Law.normalizedPhysicalExteriorMatrix {p : Params} (M : Law p)
    (j : Fin p.n) (ω : M.Ω) : HermitianMatrix (PhysicalExteriorIndex p j) :=
  ⟨(M.normalizedPhysicalMatrix ω).1.submatrix Subtype.val Subtype.val,
    (M.normalizedPhysicalMatrix ω).2.submatrix Subtype.val⟩

/-- The physical exterior principal minor is measurable entrywise. -/
theorem Law.measurable_normalizedPhysicalExteriorMatrix {p : Params}
    (M : Law p) (j : Fin p.n) :
    Measurable (M.normalizedPhysicalExteriorMatrix j) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro a b
  exact (measurable_subtype_coe.comp M.measurable_normalizedPhysicalMatrix).eval_matrix

/-- The measurable event that the normalized physical matrix has simple
spectrum.  This is the physical discriminant good event. -/
def Law.physicalFullSimpleSpectrumEvent {p : Params} (M : Law p) : Set M.Ω :=
  M.normalizedPhysicalMatrix ⁻¹' physicalSimpleSpectrumMatrices p

/-- The physical full-simple-spectrum event is measurable. -/
theorem Law.measurableSet_physicalFullSimpleSpectrumEvent {p : Params}
    (M : Law p) : MeasurableSet M.physicalFullSimpleSpectrumEvent :=
  (measurableSet_physicalSimpleSpectrumMatrices p).preimage
    M.measurable_normalizedPhysicalMatrix

/-- At ordered full rank `r`, the selected physical energy avoids the spectrum
of the principal exterior matrix obtained by deleting block `j`. -/
def Law.physicalSelectedEnergyExteriorPoleFreeEvent {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) : Set M.Ω :=
  {ω | ∀ s : Fin (Fintype.card (PhysicalExteriorIndex p j)),
    orderedEigenvalue (M.normalizedPhysicalExteriorMatrix j ω) s ≠
      orderedEigenvalue (M.normalizedPhysicalMatrix ω) r}

/-- Selected-energy/exterior-pole avoidance is a measurable physical event. -/
theorem Law.measurableSet_physicalSelectedEnergyExteriorPoleFreeEvent
    {p : Params} (M : Law p) (j : Fin p.n)
    (r : Fin (PhysicalDimension p)) :
    MeasurableSet (M.physicalSelectedEnergyExteriorPoleFreeEvent j r) := by
  simp only [physicalSelectedEnergyExteriorPoleFreeEvent, ofPred_forall]
  apply MeasurableSet.iInter
  intro s
  have hext : Measurable (fun ω =>
      orderedEigenvalue (M.normalizedPhysicalExteriorMatrix j ω) s) :=
    (measurable_orderedEigenvalue s).comp
      (M.measurable_normalizedPhysicalExteriorMatrix j)
  have hfull : Measurable (fun ω =>
      orderedEigenvalue (M.normalizedPhysicalMatrix ω) r) :=
    (measurable_orderedEigenvalue r).comp M.measurable_normalizedPhysicalMatrix
  have h := ((measurableSet_singleton 0).preimage (hext.sub hfull)).compl
  convert h using 1
  ext ω
  simp [sub_eq_zero]

/-- Simultaneous avoidance of the exterior spectrum by every ordered physical
energy.  This is the common-spectrum-free event used by the global Schur cover. -/
def Law.physicalCommonSpectrumFreeEvent {p : Params} (M : Law p)
    (j : Fin p.n) : Set M.Ω :=
  ⋂ r : Fin (PhysicalDimension p),
    M.physicalSelectedEnergyExteriorPoleFreeEvent j r

/-- The physical common-spectrum-free event is measurable. -/
theorem Law.measurableSet_physicalCommonSpectrumFreeEvent {p : Params}
    (M : Law p) (j : Fin p.n) :
    MeasurableSet (M.physicalCommonSpectrumFreeEvent j) := by
  apply MeasurableSet.iInter
  intro r
  exact M.measurableSet_physicalSelectedEnergyExteriorPoleFreeEvent j r

/-- The canonical exposed-block mass of the selected ordered physical
eigenline is strictly positive.  The zero extension at collisions makes this a
globally defined, measurable predicate. -/
def Law.physicalSelectedExposedMassPositiveEvent {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) : Set M.Ω :=
  {ω | 0 < physicalMeasurableBlockMassWeight p r
    (M.normalizedPhysicalMatrix ω) j}

/-- Positivity of the selected exposed-pair mass is measurable. -/
theorem Law.measurableSet_physicalSelectedExposedMassPositiveEvent
    {p : Params} (M : Law p) (j : Fin p.n)
    (r : Fin (PhysicalDimension p)) :
    MeasurableSet (M.physicalSelectedExposedMassPositiveEvent j r) := by
  exact (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : NNReal))).preimage
    ((measurable_physicalMeasurableBlockMassWeight p r j).comp
      M.measurable_normalizedPhysicalMatrix)

/-- The exact measurable good event required for the selected-rank conditional
physical coarea theorem: full simplicity, no exterior pole at the selected
energy, and positive exposed mass. -/
def Law.physicalSelectedCoareaGoodEvent {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) : Set M.Ω :=
  M.physicalFullSimpleSpectrumEvent ∩
    M.physicalSelectedEnergyExteriorPoleFreeEvent j r ∩
      M.physicalSelectedExposedMassPositiveEvent j r

/-- The selected-rank physical coarea good event is measurable. -/
theorem Law.measurableSet_physicalSelectedCoareaGoodEvent {p : Params}
    (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    MeasurableSet (M.physicalSelectedCoareaGoodEvent j r) :=
  (M.measurableSet_physicalFullSimpleSpectrumEvent.inter
    (M.measurableSet_physicalSelectedEnergyExteriorPoleFreeEvent j r)).inter
      (M.measurableSet_physicalSelectedExposedMassPositiveEvent j r)

/-- The simultaneous physical coarea good event for every ordered rank. -/
def Law.physicalCoareaGoodEvent {p : Params} (M : Law p)
    (j : Fin p.n) : Set M.Ω :=
  ⋂ r : Fin (PhysicalDimension p), M.physicalSelectedCoareaGoodEvent j r

/-- The simultaneous all-ranks physical coarea good event is measurable. -/
theorem Law.measurableSet_physicalCoareaGoodEvent {p : Params}
    (M : Law p) (j : Fin p.n) :
    MeasurableSet (M.physicalCoareaGoodEvent j) := by
  apply MeasurableSet.iInter
  intro r
  exact M.measurableSet_physicalSelectedCoareaGoodEvent j r

end GaussianRing
end CoareaNative.BlockBand
