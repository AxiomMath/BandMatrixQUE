module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalExhaustiveCoareaCover
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalFreshGUEDensity
public import BlockBand.Coarea.Native.BlockBand.LinearAlgebra.RegulatedSchurMeasurability

/-!
# Concrete exhaustive physical coarea cover

The selected ordered encoder is Borel measurable, so by Lusin–Souslin its chart image is
measurable.  Maximal physical sources are then disjointized by a deterministic finite priority
on pole/rank/chart indices.  The resulting `PhysicalCoareaPoleChartCover` exhausts the
independently specified collision-free fixed-rank good set
(`physicalExhaustiveCoareaPoleChartCover_exhaustive`).

All sizes and exterior data are fixed; no asymptotic or outer-randomness assertion is made.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set

/-- The selected affine eigenline coordinate is Borel measurable. -/
theorem measurable_selectedOrderedEigenlineAffineCoordinate
    {d : ℕ} (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d) :
    Measurable (selectedOrderedEigenlineAffineCoordinate r p) := by
  rw [measurable_pi_iff]
  intro j
  unfold selectedOrderedEigenlineAffineCoordinate projectiveEigenvectorChart
  have heval (a : Fin d) : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      orderedEigenlineSelection d r x a) := by
    exact (((continuous_apply a).comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℂ))).measurable).comp
        (measurable_orderedEigenlineSelection d r)
  exact (heval ((selectedCoordinateEquiv (ofLex p).1).symm (Sum.inr j))).div
    (heval ((selectedCoordinateEquiv (ofLex p).1).symm (Sum.inl Unit.unit)))

/-- The phase-fixed Householder matrix assembled from the selected affine coordinate is
Borel measurable. -/
theorem measurable_selectedOrderedHouseholderFrame
    {d : ℕ} (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d) :
    Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      phaseFixedHouseholderFrame (Sum.inl Unit.unit)
        (canonicalProjectiveUnitVector
          (selectedOrderedEigenlineAffineCoordinate r p x))) := by
  have hc : Measurable (fun z : Fin (d - 1) → ℂ =>
      canonicalProjectiveChartCoordinates z) := by
    rw [measurable_pi_iff]
    intro q
    rcases q with ⟨q, hq⟩
    rcases q with u | q
    · exact False.elim (hq (by cases u; rfl))
    · exact measurable_pi_apply q
  have hv : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      canonicalProjectiveUnitVector
        (selectedOrderedEigenlineAffineCoordinate r p x)) :=
    (measurable_projectiveUnitReconstruction (Sum.inl Unit.unit)).comp
      (hc.comp (measurable_selectedOrderedEigenlineAffineCoordinate r p))
  rw [Matrix.measurable_iff]
  intro a b
  rw [show (fun x : hermitianSimpleSpectrumCoordinates d =>
      phaseFixedHouseholderFrame (Sum.inl Unit.unit)
        (canonicalProjectiveUnitVector
          (selectedOrderedEigenlineAffineCoordinate r p x)) a b) =
      fun x => -(if a = b then 1 else 0) +
        (((1 + ((canonicalProjectiveUnitVector
          (selectedOrderedEigenlineAffineCoordinate r p x))
            (Sum.inl Unit.unit)).re)⁻¹ : ℝ) : ℂ) *
        phaseFixedHouseholderShift (Sum.inl Unit.unit)
          (canonicalProjectiveUnitVector
            (selectedOrderedEigenlineAffineCoordinate r p x)) a *
        star (phaseFixedHouseholderShift (Sum.inl Unit.unit)
          (canonicalProjectiveUnitVector
            (selectedOrderedEigenlineAffineCoordinate r p x)) b) by
      funext x
      exact phaseFixedHouseholderFrame_apply _ _ _ _]
  have heval (a : Unit ⊕ Fin (d - 1)) : Measurable (fun x =>
      (canonicalProjectiveUnitVector
        (selectedOrderedEigenlineAffineCoordinate r p x)) a) :=
    (((continuous_apply a).comp
      (PiLp.continuous_ofLp 2 (fun _ : Unit ⊕ Fin (d - 1) => ℂ))).measurable).comp hv
  have hshift (a : Unit ⊕ Fin (d - 1)) : Measurable (fun x =>
      phaseFixedHouseholderShift (Sum.inl Unit.unit)
        (canonicalProjectiveUnitVector
          (selectedOrderedEigenlineAffineCoordinate r p x)) a) := by
    unfold phaseFixedHouseholderShift
    exact (heval a).add measurable_const
  have hcoeff : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      ((((1 + (canonicalProjectiveUnitVector
        (selectedOrderedEigenlineAffineCoordinate r p x))
          (Sum.inl Unit.unit)).re)⁻¹ : ℝ) : ℂ)) := by
    apply Complex.measurable_ofReal.comp
    exact (measurable_const.add
      (Complex.measurable_re.comp (heval (Sum.inl Unit.unit)))).inv
  have hstar : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      star (phaseFixedHouseholderShift (Sum.inl Unit.unit)
        (canonicalProjectiveUnitVector
          (selectedOrderedEigenlineAffineCoordinate r p x)) b)) := by
    exact Complex.continuous_conj.measurable.comp (hshift b)
  exact measurable_const.add ((hcoeff.mul (hshift a)).mul hstar)

/-- The complementary Hermitian block read from the selected moving frame is Borel
measurable. -/
theorem measurable_selectedOrderedEigenpairComplementBlock
    {d : ℕ} (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d) :
    Measurable (selectedOrderedEigenpairComplementBlock r p) := by
  apply Measurable.subtype_mk
  let hH := measurable_selectedOrderedHouseholderFrame r p
  have hA : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      (selectedCoordinateHermitianReindex (ofLex p).1
        (⟨hermitianOfFinCoordinates d x.1,
          (hermitianOfFinCoordinates d x.1).2⟩ : RealHermitianMatrix (Fin d))).1) := by
    rw [Matrix.measurable_iff]
    intro a b
    exact (measurable_subtype_coe.comp
      ((measurable_hermitianOfFinCoordinates d).comp measurable_subtype_coe)).eval_matrix
  have hC : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      (phaseFixedHouseholderFrame (Sum.inl Unit.unit)
        (canonicalProjectiveUnitVector
          (selectedOrderedEigenlineAffineCoordinate r p x)))ᴴ *
      (selectedCoordinateHermitianReindex (ofLex p).1
        (⟨hermitianOfFinCoordinates d x.1,
          (hermitianOfFinCoordinates d x.1).2⟩ : RealHermitianMatrix (Fin d))).1 *
      phaseFixedHouseholderFrame (Sum.inl Unit.unit)
        (canonicalProjectiveUnitVector
          (selectedOrderedEigenlineAffineCoordinate r p x))) :=
    Measurable.matrixMul
      (Measurable.matrixMul (Measurable.matrixConjTranspose hH) hA) hH
  rw [Matrix.measurable_iff]
  intro a b
  exact (Matrix.measurable_iff.mp hC (Sum.inr a) (Sum.inr b))

/-- The full selected ordered eigenpair encoder is Borel measurable. -/
theorem measurable_selectedOrderedEigenpairChartEncode
    {d : ℕ} (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d) :
    Measurable (selectedOrderedEigenpairChartEncode r p) := by
  apply Measurable.prodMk
  · exact (measurable_orderedEigenvalue_hermitianOfFinCoordinates d r).comp
      measurable_subtype_coe
  · exact (measurable_selectedOrderedEigenlineAffineCoordinate r p).prodMk
      (measurable_selectedOrderedEigenpairComplementBlock r p)

/-- The encoder is injective on its deterministic chart region. -/
theorem injOn_selectedOrderedEigenpairChartEncode
    {d : ℕ} (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d) :
    Set.InjOn (selectedOrderedEigenpairChartEncode r p)
      (orderedEigenpairReconstructionChartRegion d r p) := by
  intro x hx y hy hxy
  apply Subtype.ext
  have hdx := selectedOrderedEigenpairChart_decode_encode r p x hx
  have hdy := selectedOrderedEigenpairChart_decode_encode r p y hy
  have hmat : hermitianOfFinCoordinates d x.1 =
      hermitianOfFinCoordinates d y.1 := by
    apply Subtype.ext
    calc
      (hermitianOfFinCoordinates d x.1).1 =
          (selectedEigenpairChartDecode (ofLex p).1
            (selectedOrderedEigenpairChartEncode r p x)).1 :=
        (congrArg Subtype.val hdx).symm
      _ = (selectedEigenpairChartDecode (ofLex p).1
            (selectedOrderedEigenpairChartEncode r p y)).1 := by rw [hxy]
      _ = (hermitianOfFinCoordinates d y.1).1 :=
        congrArg Subtype.val hdy
  have hleft (z : HermitianCoordinateSpace d) :
      finCoordinatesOfHermitian (hermitianOfFinCoordinates d z) = z := by
    funext j
    change coordinatesOfHermitian (hermitianOfFinCoordinates d z)
      ((hermitianCoordinateEquivFin d).symm j) = z j
    rw [hermitianOfFinCoordinates]
    simp [coordinatesOfHermitian_hermitianOfCoordinates]
  exact (hleft x.1).symm.trans
    ((congrArg finCoordinatesOfHermitian hmat).trans (hleft y.1))

/-- Lusin–Souslin gives the measurability of the full chart source. -/
theorem measurableSet_selectedOrderedEigenpairChartSource_complete
    {d : ℕ} (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d) :
    MeasurableSet (selectedOrderedEigenpairChartSource r p) := by
  let : StandardBorelSpace (hermitianSimpleSpectrumCoordinates d) :=
    (measurableSet_hermitianSimpleSpectrumCoordinates d).standardBorel
  let e := selectedEigenpairFinCoordinateLinearEquiv (ofLex p).1
  let f : hermitianSimpleSpectrumCoordinates d → HermitianCoordinateSpace d :=
    fun x => e.symm (selectedOrderedEigenpairChartEncode r p x)
  have he : Measurable e.symm :=
    e.symm.toLinearMap.continuous_of_finiteDimensional.measurable
  have hf : Measurable f :=
    he.comp (measurable_selectedOrderedEigenpairChartEncode r p)
  have hfinj : Set.InjOn f
      (orderedEigenpairReconstructionChartRegion d r p) :=
    e.symm.injective.injOn.comp
      (injOn_selectedOrderedEigenpairChartEncode r p)
      (Set.mapsTo_image _ _)
  have himage : MeasurableSet
      (f '' orderedEigenpairReconstructionChartRegion d r p) :=
    MeasurableSet.image_of_measurable_injOn
      (measurableSet_orderedEigenpairReconstructionChartRegion d r p)
      hf hfinj
  rw [show selectedOrderedEigenpairChartSource r p =
      e.symm ⁻¹' (f '' orderedEigenpairReconstructionChartRegion d r p) by
    ext y
    simp only [selectedOrderedEigenpairChartSource, Set.mem_image,
      Set.mem_preimage, f, e]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, e.symm.injective hxy⟩]
  exact himage.preimage he

/-- The maximal measurable source before deterministic overlap removal. -/
def physicalMaximalCoareaSource {dR d : ℕ} (α : ℕ)
    (R : HermitianCoordinateSpace dR) (k : Fin (dR + 1))
    (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d) :
    Set (HermitianCoordinateSpace d) :=
  {x | eigenpairIncidenceCoordinates (ofLex p).1 x ∈
      selectedOrderedEigenpairChartSource r p} ∩
  ({x | coareaGapWeight (d - 1)
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      ((hermitianFinCoordinatesLinearEquiv (d - 1)).symm
        (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2) ≠ 0} ∩
  ({x | physicalEigenpairFixedRank α R
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2} ∩
  {x | (eigenpairIncidenceCoordinates (ofLex p).1 x).1 ∈
      physicalExteriorInertiaInterval dR R k}))

/-- Incidence coordinates are Borel measurable. -/
theorem measurable_eigenpairIncidenceCoordinates_complete
    {d : ℕ} (i : Fin d) :
    Measurable (eigenpairIncidenceCoordinates i) :=
  (selectedEigenpairFinCoordinateLinearEquiv i).toLinearMap
    |>.continuous_of_finiteDimensional.measurable

/-- The incidence energy coordinate is Borel measurable. -/
theorem measurable_eigenpairIncidenceEnergy_complete
    {d : ℕ} (i : Fin d) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      (eigenpairIncidenceCoordinates i x).1) :=
  measurable_fst.comp (measurable_eigenpairIncidenceCoordinates_complete i)

/-- The complementary Hermitian finite-coordinate readback is Borel measurable. -/
theorem measurable_eigenpairIncidenceComplementCoordinates_complete
    {d : ℕ} (i : Fin d) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      (hermitianFinCoordinatesLinearEquiv (d - 1)).symm
        (eigenpairIncidenceCoordinates i x).2.2) :=
  (hermitianFinCoordinatesLinearEquiv (d - 1)).symm.toLinearMap
    |>.continuous_of_finiteDimensional.measurable.comp
      (measurable_snd.comp
        (measurable_snd.comp (measurable_eigenpairIncidenceCoordinates_complete i)))

/-- The complementary gap weight in incidence coordinates is Borel measurable. -/
theorem measurable_eigenpairIncidenceGapWeight_complete
    {d : ℕ} (i : Fin d) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      coareaGapWeight (d - 1)
        (eigenpairIncidenceCoordinates i x).1
        ((hermitianFinCoordinatesLinearEquiv (d - 1)).symm
          (eigenpairIncidenceCoordinates i x).2.2)) :=
  by
    change Measurable ((fun z : ℝ × HermitianCoordinateSpace (d - 1) =>
      coareaGapWeight (d - 1) z.1 z.2) ∘
        fun x : HermitianCoordinateSpace d =>
          ((eigenpairIncidenceCoordinates i x).1,
            (hermitianFinCoordinatesLinearEquiv (d - 1)).symm
              (eigenpairIncidenceCoordinates i x).2.2))
    exact (measurable_coareaGapWeight (d - 1)).comp
      ((measurable_eigenpairIncidenceEnergy_complete i).prodMk
        (measurable_eigenpairIncidenceComplementCoordinates_complete i))

/-- The exterior-energy-complement sector coordinate is Borel measurable. -/
theorem measurable_eigenpairIncidenceSectorCoordinates_complete
    {dR d : ℕ} (R : HermitianCoordinateSpace dR) (i : Fin d) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      (R, ((eigenpairIncidenceCoordinates i x).1,
        (hermitianFinCoordinatesLinearEquiv (d - 1)).symm
          (eigenpairIncidenceCoordinates i x).2.2))) :=
  measurable_const.prodMk
    ((measurable_eigenpairIncidenceEnergy_complete i).prodMk
      (measurable_eigenpairIncidenceComplementCoordinates_complete i))

/-- Every maximal pole/rank/chart source is Borel measurable. -/
theorem measurableSet_physicalMaximalCoareaSource
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (k : Fin (dR + 1)) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    MeasurableSet (physicalMaximalCoareaSource α R k r p) := by
  let i := (ofLex p).1
  have hchartSet : MeasurableSet {x : HermitianCoordinateSpace d |
      eigenpairIncidenceCoordinates i x ∈
        selectedOrderedEigenpairChartSource r p} :=
    (measurableSet_selectedOrderedEigenpairChartSource_complete r p).preimage
      (measurable_eigenpairIncidenceCoordinates_complete i)
  have hgapSet : MeasurableSet {x : HermitianCoordinateSpace d |
      coareaGapWeight (d - 1)
        (eigenpairIncidenceCoordinates i x).1
        ((hermitianFinCoordinatesLinearEquiv (d - 1)).symm
          (eigenpairIncidenceCoordinates i x).2.2) ≠ 0} :=
    ((measurableSet_singleton 0).preimage
      (measurable_eigenpairIncidenceGapWeight_complete i)).compl
  have hrankSet : MeasurableSet {x : HermitianCoordinateSpace d |
      physicalEigenpairFixedRank α R
        (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.2} := by
    change MeasurableSet ((fun x : HermitianCoordinateSpace d =>
      (R, ((eigenpairIncidenceCoordinates i x).1,
        (hermitianFinCoordinatesLinearEquiv (d - 1)).symm
          (eigenpairIncidenceCoordinates i x).2.2))) ⁻¹'
            coareaRankSector dR (d - 1) α)
    exact (measurableSet_coareaRankSector dR (d - 1) α).preimage
      (measurable_eigenpairIncidenceSectorCoordinates_complete R i)
  have henergySet : MeasurableSet {x : HermitianCoordinateSpace d |
      (eigenpairIncidenceCoordinates i x).1 ∈
        physicalExteriorInertiaInterval dR R k} :=
    (measurableSet_physicalExteriorInertiaInterval dR R k).preimage
      (measurable_eigenpairIncidenceEnergy_complete i)
  unfold physicalMaximalCoareaSource
  exact hchartSet.inter (hgapSet.inter (hrankSet.inter henergySet))

/-- The maximal-source gap condition is the required nonzero determinant condition. -/
theorem physicalMaximalCoareaSource_gap
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (k : Fin (dR + 1)) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) {x : HermitianCoordinateSpace d}
    (hx : x ∈ physicalMaximalCoareaSource α R k r p) :
    (eigenpairGapMatrix
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2.1).det ≠ 0 := by
  intro hzero
  apply hx.2.1
  have hB := (hermitianFinCoordinatesLinearEquiv (d - 1)).apply_symm_apply
    (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2
  change hermitianOfFinCoordinates (d - 1)
      ((hermitianFinCoordinatesLinearEquiv (d - 1)).symm
        (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2) =
    (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2 at hB
  rw [coareaGapWeight, eigenpairLocalRealJacobianDensity_eq_normSq_det,
    hB, hzero, Complex.normSq_zero]

/-- Maximal sources map into their selected ordered chart. -/
theorem physicalMaximalCoareaSource_in_chart
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (k : Fin (dR + 1)) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    physicalMaximalCoareaSource α R k r p ⊆
      {x | eigenpairIncidenceCoordinates (ofLex p).1 x ∈
        selectedOrderedEigenpairChartSource r p} := fun _ hx => hx.1

/-- Maximal sources satisfy the exact physical additive rank sector. -/
theorem physicalMaximalCoareaSource_rank
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (k : Fin (dR + 1)) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) {x : HermitianCoordinateSpace d}
    (hx : x ∈ physicalMaximalCoareaSource α R k r p) :
    physicalEigenpairFixedRank α R
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2 := hx.2.2.1

/-- Finite pole/rank/projective-chart index type. -/
abbrev PhysicalCoareaCoverIndex (dR d : ℕ) :=
  Fin (dR + 1) × HermitianEigenRank d × OrderedEigenlineChartIndex d

/-- Canonical finite priority used only to remove decoded overlaps deterministically. -/
noncomputable def physicalCoareaCoverPriority (dR d : ℕ) :
    PhysicalCoareaCoverIndex dR d ≃ Fin (Fintype.card (PhysicalCoareaCoverIndex dR d)) :=
  Fintype.equivFin _

/-- The decoded image of one maximal pole/rank/chart source. -/
def physicalMaximalDecodedImage {dR d : ℕ} (α : ℕ)
    (R : HermitianCoordinateSpace dR) (i : PhysicalCoareaCoverIndex dR d) :
    Set (HermitianCoordinateSpace d) :=
  selectedEigenpairFinCoordinateChartDecode (ofLex i.2.2).1 ''
    physicalMaximalCoareaSource α R i.1 i.2.1 i.2.2

/-- Every maximal decoded image is Borel measurable. -/
theorem measurableSet_physicalMaximalDecodedImage
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (i : PhysicalCoareaCoverIndex dR d) :
    MeasurableSet (physicalMaximalDecodedImage α R i) := by
  exact MeasurableSet.image_of_measurable_injOn
    (measurableSet_physicalMaximalCoareaSource α R i.1 i.2.1 i.2.2)
    (measurable_selectedEigenpairFinCoordinateChartDecode _)
    ((injOn_selectedEigenpairFinCoordinateChartDecode_fixedRankSource i.2.1 i.2.2).mono
      (physicalMaximalCoareaSource_in_chart α R i.1 i.2.1 i.2.2))

/-- Deterministic source obtained by assigning every decoded matrix to the earliest
maximal pole/rank/chart representative. -/
def physicalDisjointCoareaSource {dR d : ℕ} (α : ℕ)
    (R : HermitianCoordinateSpace dR) (i : PhysicalCoareaCoverIndex dR d) :
    Set (HermitianCoordinateSpace d) :=
  physicalMaximalCoareaSource α R i.1 i.2.1 i.2.2 \
    selectedEigenpairFinCoordinateChartDecode (ofLex i.2.2).1 ⁻¹'
      (⋃ j : PhysicalCoareaCoverIndex dR d,
        if physicalCoareaCoverPriority dR d j < physicalCoareaCoverPriority dR d i then
          physicalMaximalDecodedImage α R j else ∅)

/-- Deterministically disjointized sources remain Borel measurable. -/
theorem measurableSet_physicalDisjointCoareaSource
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (i : PhysicalCoareaCoverIndex dR d) :
    MeasurableSet (physicalDisjointCoareaSource α R i) := by
  apply MeasurableSet.diff
  · exact measurableSet_physicalMaximalCoareaSource α R i.1 i.2.1 i.2.2
  · apply MeasurableSet.preimage
    · apply MeasurableSet.iUnion
      intro j
      split_ifs
      · exact measurableSet_physicalMaximalDecodedImage α R j
      · exact MeasurableSet.empty
    · exact measurable_selectedEigenpairFinCoordinateChartDecode _

/-- Disjointization only removes points from the corresponding maximal source. -/
theorem physicalDisjointCoareaSource_subset_maximal
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (i : PhysicalCoareaCoverIndex dR d) :
    physicalDisjointCoareaSource α R i ⊆
      physicalMaximalCoareaSource α R i.1 i.2.1 i.2.2 :=
  Set.sdiff_subset

/-- Decoded images of the deterministically assigned sources are pairwise disjoint. -/
theorem physicalDisjointCoareaSource_decoded_pairwise
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR) :
    Pairwise (Function.onFun Disjoint
      (fun i : PhysicalCoareaCoverIndex dR d =>
        selectedEigenpairFinCoordinateChartDecode (ofLex i.2.2).1 ''
          physicalDisjointCoareaSource α R i)) := by
  intro i j hij
  change Disjoint
    (selectedEigenpairFinCoordinateChartDecode (ofLex i.2.2).1 ''
      physicalDisjointCoareaSource α R i)
    (selectedEigenpairFinCoordinateChartDecode (ofLex j.2.2).1 ''
      physicalDisjointCoareaSource α R j)
  rw [Set.disjoint_left]
  intro K hi hj
  rcases hi with ⟨xi, hxi, rfl⟩
  rcases hj with ⟨xj, hxj, hdecode⟩
  have hpne : physicalCoareaCoverPriority dR d i ≠
      physicalCoareaCoverPriority dR d j := fun h =>
    hij ((physicalCoareaCoverPriority dR d).injective h)
  rcases lt_or_gt_of_ne hpne with hp | hp
  · apply hxj.2
    apply Set.mem_iUnion.2
    refine ⟨i, ?_⟩
    simp only [hp, ↓reduceIte]
    exact ⟨xi, hxi.1, hdecode.symm⟩
  · apply hxi.2
    apply Set.mem_iUnion.2
    refine ⟨j, ?_⟩
    simp only [hp, ↓reduceIte]
    exact ⟨xj, hxj.1, hdecode⟩

/-- Disjointization preserves the union of all maximal decoded images. -/
theorem iUnion_decoded_physicalDisjointCoareaSource
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR) :
    (⋃ i : PhysicalCoareaCoverIndex dR d,
      selectedEigenpairFinCoordinateChartDecode (ofLex i.2.2).1 ''
        physicalDisjointCoareaSource α R i) =
    ⋃ i : PhysicalCoareaCoverIndex dR d, physicalMaximalDecodedImage α R i := by
  classical
  apply Set.Subset.antisymm
  · apply Set.iUnion_mono
    intro i
    exact Set.image_mono (physicalDisjointCoareaSource_subset_maximal α R i)
  · intro K hK
    simp only [Set.mem_iUnion] at hK ⊢
    let candidates : Finset (PhysicalCoareaCoverIndex dR d) :=
      Finset.univ.filter fun i => K ∈ physicalMaximalDecodedImage α R i
    have hcandidates : candidates.Nonempty := by
      rcases hK with ⟨i, hi⟩
      exact ⟨i, by simp [candidates, hi]⟩
    let priorities : Finset
        (Fin (Fintype.card (PhysicalCoareaCoverIndex dR d))) :=
      candidates.image (physicalCoareaCoverPriority dR d)
    have hpriorities : priorities.Nonempty := by
      rcases hcandidates with ⟨j, hj⟩
      exact ⟨physicalCoareaCoverPriority dR d j,
        Finset.mem_image.2 ⟨j, hj, rfl⟩⟩
    let m := priorities.min' hpriorities
    let i := (physicalCoareaCoverPriority dR d).symm m
    have hic : i ∈ candidates := by
      have hm : m ∈ priorities := priorities.min'_mem hpriorities
      rcases Finset.mem_image.mp hm with ⟨j, hj, hjm⟩
      have hji : j = i := by
        apply (physicalCoareaCoverPriority dR d).injective
        simpa [i] using hjm
      simpa [hji] using hj
    have hi : K ∈ physicalMaximalDecodedImage α R i := by
      exact (Finset.mem_filter.mp hic).2
    rcases hi with ⟨x, hx, hdecode⟩
    refine ⟨i, x, ⟨hx, ?_⟩, hdecode⟩
    intro hlower
    change selectedEigenpairFinCoordinateChartDecode (ofLex i.2.2).1 x ∈
      (⋃ j : PhysicalCoareaCoverIndex dR d,
        if physicalCoareaCoverPriority dR d j <
            physicalCoareaCoverPriority dR d i then
          physicalMaximalDecodedImage α R j else ∅) at hlower
    simp only [Set.mem_iUnion] at hlower
    rcases hlower with ⟨j, hj⟩
    split_ifs at hj with hp
    · have hj' : K ∈ physicalMaximalDecodedImage α R j := by
        rw [hdecode] at hj
        exact hj
      have hjc : j ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj'
      have hpj : physicalCoareaCoverPriority dR d j ∈ priorities :=
        Finset.mem_image.2 ⟨j, hjc, rfl⟩
      have hle : physicalCoareaCoverPriority dR d i ≤
          physicalCoareaCoverPriority dR d j := by
        have hmle := priorities.min'_le
          (physicalCoareaCoverPriority dR d j) hpj
        simpa [i, m] using hmle
      exact (not_lt_of_ge hle) hp
    · simp at hj

/-- The concrete finite measurable disjoint pole/rank/projective-chart cover. -/
noncomputable def physicalExhaustiveCoareaPoleChartCover
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR) :
    PhysicalCoareaPoleChartCover (Fin (dR + 1)) (d := d) α R where
  energyRegion := {E | (R, E) ∈ coareaExteriorPoleFree dR}
  interval := physicalExteriorInertiaInterval dR R
  interval_iUnion := iUnion_physicalExteriorInertiaInterval dR R
  source k r p := physicalDisjointCoareaSource α R (k, r, p)
  interval_pairwise_disjoint := physicalExteriorInertiaInterval_pairwise_disjoint dR R
  decodedImage_pairwise_disjoint := by
    simpa only using physicalDisjointCoareaSource_decoded_pairwise α R
  source_measurable k r p :=
    measurableSet_physicalDisjointCoareaSource α R (k, r, p)
  source_in_chart k r p :=
    (physicalDisjointCoareaSource_subset_maximal α R (k, r, p)).trans
      (physicalMaximalCoareaSource_in_chart α R k r p)
  source_gap k r p x hx :=
    physicalMaximalCoareaSource_gap α R k r p
      (physicalDisjointCoareaSource_subset_maximal α R (k, r, p) hx)
  source_rank k r p x hx :=
    physicalMaximalCoareaSource_rank α R k r p
      (physicalDisjointCoareaSource_subset_maximal α R (k, r, p) hx)
  source_energy_mem k r p x hx :=
    (physicalDisjointCoareaSource_subset_maximal α R (k, r, p) hx).2.2.2

/-- The concrete cover's decoded union is exactly the union of all maximal decoded
pole/rank/chart sources; deterministic disjointization loses no matrix. -/
theorem physicalExhaustiveCoareaPoleChartCover_decodedUnion_eq_iUnion_maximal
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR) :
    (physicalExhaustiveCoareaPoleChartCover α R).decodedUnion =
      ⋃ i : PhysicalCoareaCoverIndex dR d,
        physicalMaximalDecodedImage α R i := by
  change (⋃ i : PhysicalCoareaCoverIndex dR d,
      selectedEigenpairFinCoordinateChartDecode (ofLex i.2.2).1 ''
        physicalDisjointCoareaSource α R i) = _
  exact iUnion_decoded_physicalDisjointCoareaSource α R

/-- The union of maximal sources is precisely the independently specified physical
collision-free fixed-rank good set. -/
theorem iUnion_physicalMaximalDecodedImage_eq_goodSet
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR) :
    (⋃ i : PhysicalCoareaCoverIndex dR d,
        physicalMaximalDecodedImage α R i) =
      physicalCollisionFreeFixedRankGoodSet
        (physicalExhaustiveCoareaPoleChartCover α R) := by
  ext K
  unfold physicalMaximalDecodedImage physicalCollisionFreeFixedRankGoodSet
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, x, hx, rfl⟩
    refine ⟨(i.2.1, i.2.2), x, ?_, rfl⟩
    exact ⟨hx.1, physicalMaximalCoareaSource_gap α R i.1 i.2.1 i.2.2 hx,
      hx.2.2.1, hx.2.2.2.1⟩
  · rintro ⟨rp, x, hx, rfl⟩
    have hle : shiftedInertia dR R
        (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).1 < dR + 1 := by
      simpa [shiftedInertia] using Nat.lt_succ_of_le
        (inertia_le_card (shiftedHermitianFinCoordinates dR R
          (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).1))
    let k : Fin (dR + 1) :=
      ⟨shiftedInertia dR R
        (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).1, hle⟩
    refine ⟨(k, rp), x, ?_, rfl⟩
    refine ⟨hx.1, ?_, hx.2.2.1, ?_⟩
    · intro hgap
      have hB := (hermitianFinCoordinatesLinearEquiv (d - 1)).apply_symm_apply
        (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).2.2
      change hermitianOfFinCoordinates (d - 1)
          ((hermitianFinCoordinatesLinearEquiv (d - 1)).symm
            (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).2.2) =
        (eigenpairIncidenceCoordinates (ofLex rp.2).1 x).2.2 at hB
      rw [coareaGapWeight, eigenpairLocalRealJacobianDensity_eq_normSq_det, hB,
        Complex.normSq_eq_zero] at hgap
      exact hx.2.1 hgap
    · exact ⟨hx.2.2.2, rfl⟩

/-- The concrete finite measurable disjoint cover is exhaustive on the full physical
collision-free fixed-rank good set. -/
theorem physicalExhaustiveCoareaPoleChartCover_exhaustive
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR) :
    (physicalExhaustiveCoareaPoleChartCover (d := d) α R).Exhaustive := by
  rw [PhysicalCoareaPoleChartCover.exhaustive_iff,
    physicalExhaustiveCoareaPoleChartCover_decodedUnion_eq_iUnion_maximal,
    iUnion_physicalMaximalDecodedImage_eq_goodSet]

end CoareaNative.BlockBand
