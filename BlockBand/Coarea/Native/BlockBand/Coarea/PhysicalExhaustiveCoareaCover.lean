module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalFixedRankCoareaFormula

/-!
# Exhaustive finite partitions for physical eigenpair coarea

Two pieces of the global-cover argument.  For fixed exterior coordinates, the pole-free energy
line is partitioned into the finitely many measurable strict-inertia sectors.  Independently,
the least-entry ordered-eigenline rule is a deterministic measurable, disjoint projective-chart
partition.

The final section states the exhaustion predicate for a `PhysicalCoareaPoleChartCover`: its
decoded union must equal the independently defined collision-free, fixed-rank good set.  A cover
satisfying it is constructed in `PhysicalExhaustiveCoareaCoverComplete`.

Ranks and inertias are zero-based; the physical sector keeps the one-based equation of the
paper through `physicalEigenpairFixedRank`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set

/-- The `k`-th pole-free exterior energy sector, indexed by strict negative inertia. -/
def physicalExteriorInertiaInterval (dR : ℕ)
    (R : HermitianCoordinateSpace dR) (k : Fin (dR + 1)) : Set ℝ :=
  {E | (R, E) ∈ coareaExteriorPoleFree dR ∧ shiftedInertia dR R E = k.val}

/-- Every exterior inertia sector is Borel measurable. -/
theorem measurableSet_physicalExteriorInertiaInterval (dR : ℕ)
    (R : HermitianCoordinateSpace dR) (k : Fin (dR + 1)) :
    MeasurableSet (physicalExteriorInertiaInterval dR R k) := by
  apply MeasurableSet.inter
  · exact (measurableSet_coareaExteriorPoleFree dR).preimage
      (measurable_const.prodMk measurable_id)
  · have hm : Measurable (fun E : ℝ => shiftedInertia dR R E) := by
      change Measurable ((fun z : HermitianCoordinateSpace dR × ℝ =>
        shiftedInertia dR z.1 z.2) ∘ fun E : ℝ => (R, E))
      exact (measurable_shiftedInertia dR).comp
        (measurable_const.prodMk measurable_id)
    exact (measurableSet_singleton k.val).preimage hm

/-- Distinct strict-inertia labels give disjoint pole intervals. -/
theorem disjoint_physicalExteriorInertiaInterval (dR : ℕ)
    (R : HermitianCoordinateSpace dR) {k l : Fin (dR + 1)} (hkl : k ≠ l) :
    Disjoint (physicalExteriorInertiaInterval dR R k)
      (physicalExteriorInertiaInterval dR R l) := by
  rw [Set.disjoint_left]
  intro E hk hl
  apply hkl
  apply Fin.ext
  exact hk.2.symm.trans hl.2

/-- The finite exterior inertia family has the disjointness field required by
`PhysicalCoareaPoleChartCover`. -/
theorem physicalExteriorInertiaInterval_pairwise_disjoint (dR : ℕ)
    (R : HermitianCoordinateSpace dR) :
    Pairwise (Function.onFun Disjoint
      (physicalExteriorInertiaInterval dR R)) := by
  intro k l hkl
  exact disjoint_physicalExteriorInertiaInterval dR R hkl

/-- The finite inertia sectors exhaust exactly the pole-free energy fibre. -/
theorem iUnion_physicalExteriorInertiaInterval (dR : ℕ)
    (R : HermitianCoordinateSpace dR) :
    (⋃ k : Fin (dR + 1), physicalExteriorInertiaInterval dR R k) =
      {E | (R, E) ∈ coareaExteriorPoleFree dR} := by
  ext E
  constructor
  · intro h
    simp only [Set.mem_iUnion] at h
    rcases h with ⟨k, hk⟩
    exact hk.1
  · intro hE
    have hle : shiftedInertia dR R E < dR + 1 := by
      simpa [shiftedInertia] using
        Nat.lt_succ_of_le (inertia_le_card (shiftedHermitianFinCoordinates dR R E))
    let k : Fin (dR + 1) := ⟨shiftedInertia dR R E, hle⟩
    exact Set.mem_iUnion.2 ⟨k, hE, rfl⟩

/-- The deterministic projective-chart cells for one ordered rank are measurable. -/
theorem measurableSet_physicalLeastProjectiveChartCell
    (d : ℕ) (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d) :
    MeasurableSet (orderedEigenpairReconstructionChartRegion d r p) :=
  measurableSet_orderedEigenpairReconstructionChartRegion d r p

/-- Distinct deterministic projective-chart cells do not overlap. -/
theorem disjoint_physicalLeastProjectiveChartCell
    {d : ℕ} (r : HermitianEigenRank d)
    {p q : OrderedEigenlineChartIndex d} (hpq : p ≠ q) :
    Disjoint (orderedEigenpairReconstructionChartRegion d r p)
      (orderedEigenpairReconstructionChartRegion d r q) :=
  disjoint_orderedEigenpairReconstructionChartRegion r hpq

/-- The deterministic projective-chart cells cover the full simple-spectrum subtype. -/
theorem iUnion_physicalLeastProjectiveChartCell
    (d : ℕ) (r : HermitianEigenRank d) :
    (⋃ p : OrderedEigenlineChartIndex d,
      orderedEigenpairReconstructionChartRegion d r p) = Set.univ :=
  iUnion_orderedEigenpairReconstructionChartRegion r

/-- Independently specified decoded good set for a finite pole cover: a decoded matrix
belongs exactly when it has a selected ordered chart representative satisfying
noncollision, the prescribed additive rank, and the cover's energy region.  This set
uses the full concrete chart sources, not the cover's possibly smaller sources. -/
def physicalCollisionFreeFixedRankGoodSet
    {κ : Type*} [Fintype κ] {dR d : ℕ} {α : ℕ}
    {R : HermitianCoordinateSpace dR}
    (C : PhysicalCoareaPoleChartCover κ (d := d) α R) :
    Set (HermitianCoordinateSpace d) :=
  ⋃ rp : HermitianEigenRank d × OrderedEigenlineChartIndex d,
    selectedEigenpairFinCoordinateChartDecode (ofLex rp.2).1 ''
      {x : HermitianCoordinateSpace d |
        eigenpairIncidenceCoordinates (ofLex rp.2).1 x ∈
          selectedOrderedEigenpairChartSource rp.1 rp.2 ∧
        (eigenpairGapMatrix
          (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).1
          (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).2.2.1).det ≠ 0 ∧
        physicalEigenpairFixedRank α R
          (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).1
          (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).2.2 ∧
        (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).1 ∈ C.energyRegion}

/-- Exact, non-circular exhaustion predicate for a physical coarea cover. -/
def PhysicalCoareaPoleChartCover.Exhaustive
    {κ : Type*} [Fintype κ] {dR d : ℕ} {α : ℕ}
    {R : HermitianCoordinateSpace dR}
    (C : PhysicalCoareaPoleChartCover κ (d := d) α R) : Prop :=
  C.decodedUnion = physicalCollisionFreeFixedRankGoodSet C

/-- Exhaustion is precisely equality with the independently specified full good set. -/
theorem PhysicalCoareaPoleChartCover.exhaustive_iff
    {κ : Type*} [Fintype κ] {dR d : ℕ} {α : ℕ}
    {R : HermitianCoordinateSpace dR}
    (C : PhysicalCoareaPoleChartCover κ (d := d) α R) :
    C.Exhaustive ↔
      C.decodedUnion = physicalCollisionFreeFixedRankGoodSet C := by
  rfl

/-- Every current cover is sound: its decoded union is contained in the independently
specified collision-free fixed-rank good set.  Exhaustiveness is the missing reverse
inclusion, rather than an unrecorded property of arbitrary local sources. -/
theorem PhysicalCoareaPoleChartCover.decodedUnion_subset_goodSet
    {κ : Type*} [Fintype κ] {dR d : ℕ} {α : ℕ}
    {R : HermitianCoordinateSpace dR}
    (C : PhysicalCoareaPoleChartCover κ (d := d) α R) :
    C.decodedUnion ⊆ physicalCollisionFreeFixedRankGoodSet C := by
  intro K hK
  simp only [PhysicalCoareaPoleChartCover.decodedUnion, Set.mem_iUnion] at hK
  rcases hK with ⟨arp, x, hx, rfl⟩
  simp only [physicalCollisionFreeFixedRankGoodSet, Set.mem_iUnion]
  refine ⟨(arp.2.1, arp.2.2), x, ?_, rfl⟩
  refine ⟨C.source_in_chart arp.1 arp.2.1 arp.2.2 hx,
    C.source_gap arp.1 arp.2.1 arp.2.2 x hx,
    C.source_rank arp.1 arp.2.1 arp.2.2 x hx, ?_⟩
  rw [← C.interval_iUnion]
  exact Set.mem_iUnion.2 ⟨arp.1, C.source_energy_mem arp.1 arp.2.1 arp.2.2 x hx⟩

/-- Because every physical cover is already sound, exhaustion reduces to the one
missing direction: every full good matrix must occur in some decoded source. -/
theorem PhysicalCoareaPoleChartCover.exhaustive_iff_goodSet_subset
    {κ : Type*} [Fintype κ] {dR d : ℕ} {α : ℕ}
    {R : HermitianCoordinateSpace dR}
    (C : PhysicalCoareaPoleChartCover κ (d := d) α R) :
    C.Exhaustive ↔
      physicalCollisionFreeFixedRankGoodSet C ⊆ C.decodedUnion := by
  constructor
  · intro h
    rw [h]
  · intro h
    apply Set.Subset.antisymm
    · exact C.decodedUnion_subset_goodSet
    · exact h

end CoareaNative.BlockBand
