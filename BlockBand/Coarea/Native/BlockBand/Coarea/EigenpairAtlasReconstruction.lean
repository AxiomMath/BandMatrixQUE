module

public import BlockBand.Coarea.Native.BlockBand.Coarea.OrderedEigenlineSelection
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairJacobianLocal

/-!
# Phase-fixed ordered eigenpair reconstruction charts

This module packages the global, measurable part of the Hermitian eigenpair atlas.
On the full-measure simple-spectrum coordinate space, each ordered eigenvalue is
paired with the measurable phase-fixed unit eigenvector selected from the least
nonzero entry of its Lagrange projector.  The least-chart regions are measurable,
pairwise disjoint, and cover the simple-spectrum locus.

The reconstruction data retain the exact rank-one Lagrange projection and the
complementary ambient matrix.  Consequently reconstruction is exact and the data
map, as well as every restricted chart, is injective.  This is a global measurable
atlas precursor.  It does not contain the analytic step needed by
`EigenpairCoareaAtlas`: real coordinates on the orthogonal complement, a smooth
unitary completion of the selected vector on each chart, and the derivative formula
for that nonlinear reconstruction map.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix Set

/-- Redundant but exact ordered eigenpair reconstruction data.

The four components are the selected energy, its phase-fixed unit vector, the
rank-one spectral projection, and the complementary matrix.  Retaining the
projection avoids making an unjustified identification with a globally smooth
unitary frame. -/
abbrev OrderedEigenpairReconstructionData (d : ℕ) :=
  ℝ × (EuclideanSpace ℂ (Fin d) ×
    (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ))

/-- Reconstruct the ambient Hermitian matrix from the exact projection and its
complement. -/
def reconstructOrderedEigenpair (d : ℕ)
    (y : OrderedEigenpairReconstructionData d) : Matrix (Fin d) (Fin d) ℂ :=
  y.2.2.2 + (y.1 : ℂ) • y.2.2.1

/-- The global measurable ordered eigenpair data on the simple-spectrum locus. -/
def orderedEigenpairReconstructionData (d : ℕ) (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    OrderedEigenpairReconstructionData d :=
  let E := orderedEigenvalue (hermitianOfFinCoordinates d x.1) r
  let P := hermitianLagrangeSpectralProjector d r x.1
  (E, (orderedEigenlineSelection d r x,
    (P, (hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ) -
      (E : ℂ) • P)))

/-- The ordered eigenpair data are Borel measurable in explicit real Hermitian
coordinates. -/
theorem measurable_orderedEigenpairReconstructionData
    (d : ℕ) (r : HermitianEigenRank d) :
    Measurable (orderedEigenpairReconstructionData d r) := by
  have hE : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      orderedEigenvalue (hermitianOfFinCoordinates d x.1) r) :=
    (measurable_orderedEigenvalue_hermitianOfFinCoordinates d r).comp
      measurable_subtype_coe
  have hA : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      (hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ)) :=
    measurable_subtype_coe.comp
      ((measurable_hermitianOfFinCoordinates d).comp measurable_subtype_coe)
  have hP : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      hermitianLagrangeSpectralProjector d r x.1) :=
    (measurable_hermitianLagrangeSpectralProjector d r).comp
      measurable_subtype_coe
  have hcomplement : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      (hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ) -
        ((orderedEigenvalue (hermitianOfFinCoordinates d x.1) r : ℝ) : ℂ) •
          hermitianLagrangeSpectralProjector d r x.1) := by
    apply Measurable.of_eval_matrix
    intro i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact hA.eval_matrix.sub (hE.complex_ofReal.mul hP.eval_matrix)
  exact hE.prodMk ((measurable_orderedEigenlineSelection d r).prodMk
    (hP.prodMk hcomplement))

/-- Reconstruction of the global ordered eigenpair data returns the original
ambient Hermitian matrix exactly. -/
@[simp] theorem reconstructOrderedEigenpair_orderedEigenpairReconstructionData
    {d : ℕ} (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    reconstructOrderedEigenpair d (orderedEigenpairReconstructionData d r x) =
      (hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ) := by
  simp [reconstructOrderedEigenpair, orderedEigenpairReconstructionData]

/-- The global ordered eigenpair data map is injective.  Exact reconstruction
recovers the ambient Hermitian matrix, and explicit Hermitian coordinates are a
linear equivalence. -/
theorem injective_orderedEigenpairReconstructionData
    {d : ℕ} (r : HermitianEigenRank d) :
    Function.Injective (orderedEigenpairReconstructionData d r) := by
  intro x y hxy
  have hA := congrArg (reconstructOrderedEigenpair d) hxy
  simp only [reconstructOrderedEigenpair_orderedEigenpairReconstructionData] at hA
  apply Subtype.ext
  have hH : hermitianOfFinCoordinates d x.1 =
      hermitianOfFinCoordinates d y.1 := Subtype.ext hA
  have hc := congrArg coordinatesOfHermitian hH
  simp only [hermitianOfFinCoordinates,
    coordinatesOfHermitian_hermitianOfCoordinates] at hc
  funext i
  have hi := congrFun hc ((hermitianCoordinateEquivFin d).symm i)
  simpa using hi

/-- The source of one disjoint least-entry reconstruction chart. -/
def orderedEigenpairReconstructionChartRegion
    (d : ℕ) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    Set (hermitianSimpleSpectrumCoordinates d) :=
  leastOrderedEigenlineChartRegion d r p

/-- Every least-entry reconstruction chart region is measurable. -/
theorem measurableSet_orderedEigenpairReconstructionChartRegion
    (d : ℕ) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    MeasurableSet (orderedEigenpairReconstructionChartRegion d r p) :=
  measurableSet_leastOrderedEigenlineChartRegion d r p

/-- Distinct least-entry chart regions are disjoint. -/
theorem disjoint_orderedEigenpairReconstructionChartRegion
    {d : ℕ} (r : HermitianEigenRank d)
    {p q : OrderedEigenlineChartIndex d} (hpq : p ≠ q) :
    Disjoint (orderedEigenpairReconstructionChartRegion d r p)
      (orderedEigenpairReconstructionChartRegion d r q) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  have hp : leastOrderedEigenlineChart d r x = p :=
    (leastOrderedEigenlineChart_eq_iff r x p).2 hxp
  have hq : leastOrderedEigenlineChart d r x = q :=
    (leastOrderedEigenlineChart_eq_iff r x q).2 hxq
  exact hpq (hp.symm.trans hq)

/-- The finite disjoint least-entry chart regions cover the whole
simple-spectrum coordinate space. -/
theorem iUnion_orderedEigenpairReconstructionChartRegion
    {d : ℕ} (r : HermitianEigenRank d) :
    (⋃ p : OrderedEigenlineChartIndex d,
      orderedEigenpairReconstructionChartRegion d r p) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨leastOrderedEigenlineChart d r x,
    (leastOrderedEigenlineChart_eq_iff r x _).1 rfl⟩

/-- One phase-fixed ordered eigenpair reconstruction chart.  The formula is
global; its chart label records the measurable region on which that entry is
the lexicographically first nonzero projector entry. -/
def orderedEigenpairReconstructionChart
    (d : ℕ) (r : HermitianEigenRank d)
    (_p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    OrderedEigenpairReconstructionData d :=
  orderedEigenpairReconstructionData d r x

/-- Each fixed reconstruction chart is measurable. -/
theorem measurable_orderedEigenpairReconstructionChart
    (d : ℕ) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    Measurable (orderedEigenpairReconstructionChart d r p) :=
  measurable_orderedEigenpairReconstructionData d r

/-- Each reconstruction chart is injective on its measurable source. -/
theorem injOn_orderedEigenpairReconstructionChart
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    Set.InjOn (orderedEigenpairReconstructionChart d r p)
      (orderedEigenpairReconstructionChartRegion d r p) :=
  (injective_orderedEigenpairReconstructionData r).injOn

/-- Reconstruction is a left inverse on every fixed chart region. -/
theorem reconstructOrderedEigenpair_chart
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    reconstructOrderedEigenpair d
      (orderedEigenpairReconstructionChart d r p x) =
      (hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ) :=
  reconstructOrderedEigenpair_orderedEigenpairReconstructionData r x

/-- The union of the finite chart images is exactly the range of the global
ordered eigenpair data map. -/
theorem iUnion_image_orderedEigenpairReconstructionChart
    {d : ℕ} (r : HermitianEigenRank d) :
    (⋃ p : OrderedEigenlineChartIndex d,
      orderedEigenpairReconstructionChart d r p ''
        orderedEigenpairReconstructionChartRegion d r p) =
      Set.range (orderedEigenpairReconstructionData d r) := by
  apply Set.Subset.antisymm
  · intro y hy
    simp only [Set.mem_iUnion, Set.mem_image] at hy
    obtain ⟨p, x, hx, rfl⟩ := hy
    exact ⟨x, rfl⟩
  · rintro y ⟨x, rfl⟩
    refine Set.mem_iUnion.2
      ⟨leastOrderedEigenlineChart d r x, ?_⟩
    exact ⟨x, (leastOrderedEigenlineChart_eq_iff r x _).1 rfl, rfl⟩

/-- The analytic data turning the measurable reconstruction precursor into the
local coordinate charts required by coarea: a same-dimensional real coordinate
map obtained from a smooth unitary completion of the selected eigenvector, its
inverse identities, and the identification of its derivative with the canonical
local block-triangular differential.  The `source` facts and the exact
reconstruction are proved above. -/
structure OrderedEigenpairSmoothChartCompletion (d : ℕ)
    (r : HermitianEigenRank d) where
  source : OrderedEigenlineChartIndex d → Set (HermitianCoordinateSpace d)
  decode : OrderedEigenlineChartIndex d →
    HermitianCoordinateSpace d → HermitianCoordinateSpace d
  encode : OrderedEigenlineChartIndex d →
    hermitianSimpleSpectrumCoordinates d → HermitianCoordinateSpace d
  deriv : OrderedEigenlineChartIndex d → HermitianCoordinateSpace d →
    HermitianCoordinateSpace d →L[ℝ] HermitianCoordinateSpace d
  gapDensity : OrderedEigenlineChartIndex d → HermitianCoordinateSpace d → ℝ
  source_measurable : ∀ p, MeasurableSet (source p)
  decode_mem_simple : ∀ p y, y ∈ source p →
    decode p y ∈ hermitianSimpleSpectrumCoordinates d
  decode_mem_region : ∀ p y (hy : y ∈ source p),
    (⟨decode p y, decode_mem_simple p y hy⟩ :
      hermitianSimpleSpectrumCoordinates d) ∈
      orderedEigenpairReconstructionChartRegion d r p
  encode_mem : ∀ p x,
    x ∈ orderedEigenpairReconstructionChartRegion d r p →
      encode p x ∈ source p
  decode_encode : ∀ p x,
    x ∈ orderedEigenpairReconstructionChartRegion d r p →
      decode p (encode p x) = x.1
  encode_decode : ∀ p y (hy : y ∈ source p),
    encode p ⟨decode p y, decode_mem_simple p y hy⟩ = y
  decode_hasFDerivWithinAt : ∀ p y, y ∈ source p →
    HasFDerivWithinAt (decode p) (deriv p y) (source p) y
  abs_det_deriv_eq_gapDensity : ∀ p y, y ∈ source p →
    |(deriv p y).det| = gapDensity p y

/-- The inverse identities in a smooth completion force each decoding chart
to be injective on its source. -/
theorem OrderedEigenpairSmoothChartCompletion.decode_injOn
    {d : ℕ} {r : HermitianEigenRank d}
    (C : OrderedEigenpairSmoothChartCompletion d r)
    (p : OrderedEigenlineChartIndex d) :
    Set.InjOn (C.decode p) (C.source p) := by
  intro y₁ hy₁ y₂ hy₂ h
  calc
    y₁ = C.encode p
        ⟨C.decode p y₁, C.decode_mem_simple p y₁ hy₁⟩ :=
      (C.encode_decode p y₁ hy₁).symm
    _ = C.encode p
        ⟨C.decode p y₂, C.decode_mem_simple p y₂ hy₂⟩ := by
      congr 2
    _ = y₂ := C.encode_decode p y₂ hy₂

/-- A completed smooth chart has exactly the corresponding measurable
least-entry region as its image. -/
theorem OrderedEigenpairSmoothChartCompletion.decode_image
    {d : ℕ} {r : HermitianEigenRank d}
    (C : OrderedEigenpairSmoothChartCompletion d r)
    (p : OrderedEigenlineChartIndex d) :
    C.decode p '' C.source p =
      Subtype.val '' orderedEigenpairReconstructionChartRegion d r p := by
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    exact ⟨⟨C.decode p y, C.decode_mem_simple p y hy⟩,
      C.decode_mem_region p y hy, rfl⟩
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨C.encode p x, C.encode_mem p x hx,
      C.decode_encode p x hx⟩

/-- Consequently, a smooth completion covers exactly the entire
simple-spectrum locus, with the chart disjointization already supplied by the
least-entry regions. -/
theorem OrderedEigenpairSmoothChartCompletion.iUnion_decode_image
    {d : ℕ} {r : HermitianEigenRank d}
    (C : OrderedEigenpairSmoothChartCompletion d r) :
    (⋃ p : OrderedEigenlineChartIndex d, C.decode p '' C.source p) =
      hermitianSimpleSpectrumCoordinates d := by
  apply Set.Subset.antisymm
  · intro z hz
    simp only [Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨p, y, hy, rfl⟩ := hz
    exact C.decode_mem_simple p y hy
  · intro z hz
    let x : hermitianSimpleSpectrumCoordinates d := ⟨z, hz⟩
    let p := leastOrderedEigenlineChart d r x
    refine Set.mem_iUnion.2 ⟨p, ?_⟩
    refine ⟨C.encode p x, C.encode_mem p x ?_, ?_⟩
    · exact (leastOrderedEigenlineChart_eq_iff r x p).1 rfl
    · exact C.decode_encode p x
        ((leastOrderedEigenlineChart_eq_iff r x p).1 rfl)

end CoareaNative.BlockBand
