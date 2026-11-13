module

public import BlockBand.Coarea.Native.BlockBand.Coarea.SelectedEigenpairChartInverse
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairContDiff
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairLocalInverse

/-!
# Concrete finite ordered-eigenpair chart atlas

This module packages the fixed-rank chart data constructed by the explicit
phase-fixed Householder formulas.  For a fixed ordered rank and least-entry
chart, the domain is the simple-spectrum chart region and the target is
exactly the image of the explicit energy/projective/complement encoder.  The
decoder supplies the inverse.

The same decoder on the coherent finite-dimensional carrier is identified
with the previously defined finite-coordinate nonlinear decoder and is
therefore globally `C¹`.  No local homeomorphism is claimed: the local
inverse `coherentSelectedEigenpairLocalHomeomorph` takes the equality between
the readback Fréchet derivative and the canonical gap equivalence as a
hypothesis.  This module proves the exact chart bijection and the global `C¹`
regularity of the decoder; no Jacobian statement is made.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Set Matrix

/-- Matrices in one fixed least-entry ordered-eigenline chart. -/
abbrev ConcreteOrderedEigenpairChartDomain
    (d : ℕ) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :=
  ↥(orderedEigenpairReconstructionChartRegion d r p)

/-- Coordinate triples in the image of the explicit fixed chart. -/
abbrev ConcreteOrderedEigenpairChartTarget
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :=
  ↥(selectedOrderedEigenpairChartSource r p)

/-- The concrete chart encoder, restricted to its matrix domain. -/
def concreteOrderedEigenpairChartEncode
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    ConcreteOrderedEigenpairChartDomain d r p →
      ConcreteOrderedEigenpairChartTarget r p :=
  fun x => ⟨selectedOrderedEigenpairChartEncode r p x.1,
    ⟨x.1, x.2, rfl⟩⟩

/-- Coordinate recovery from a decoded Hermitian matrix. -/
def selectedOrderedEigenpairDecodedCoordinates
    {d : ℕ} (p : OrderedEigenlineChartIndex d)
    (y : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    HermitianCoordinateSpace d :=
  finCoordinatesOfHermitian
    (selectedEigenpairChartDecode (ofLex p).1 y)

/-- Decoded coordinates of target data equal the coordinates of the
unique source matrix that encoded them. -/
theorem selectedOrderedEigenpairDecodedCoordinates_eq_source
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (y : EigenpairHermitianBlockCoordinates (Fin (d - 1)))
    (hy : y ∈ selectedOrderedEigenpairChartSource r p) :
    ∀ x : hermitianSimpleSpectrumCoordinates d,
      x ∈ orderedEigenpairReconstructionChartRegion d r p →
      selectedOrderedEigenpairChartEncode r p x = y →
      selectedOrderedEigenpairDecodedCoordinates p y = x.1 := by
  intro x hx hxy
  subst y
  have hdecode := selectedOrderedEigenpairChart_decode_encode r p x hx
  unfold selectedOrderedEigenpairDecodedCoordinates
  rw [hdecode]
  funext j
  change coordinatesOfHermitian (hermitianOfFinCoordinates d x.1)
    ((hermitianCoordinateEquivFin d).symm j) = x.1 j
  rw [hermitianOfFinCoordinates]
  simp [coordinatesOfHermitian_hermitianOfCoordinates]

/-- The nonlinear decoder maps target data back into the fixed
least-entry simple-spectrum chart. -/
def concreteOrderedEigenpairChartDecode
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    ConcreteOrderedEigenpairChartTarget r p →
      ConcreteOrderedEigenpairChartDomain d r p := by
  intro y
  have hs : selectedOrderedEigenpairDecodedCoordinates p y.1 ∈
      hermitianSimpleSpectrumCoordinates d := by
    exact selectedOrderedEigenpairChartDecode_mem_simple r p y.1 y.2
  refine ⟨⟨selectedOrderedEigenpairDecodedCoordinates p y.1, hs⟩, ?_⟩
  have hy := y.2
  rcases y.2 with ⟨x, hx, hxy⟩
  have hcoord := selectedOrderedEigenpairDecodedCoordinates_eq_source
    r p y.1 hy x hx hxy
  simpa [hcoord] using hx

/-- Decoding after encoding is the identity on the chart domain. -/
@[simp] theorem concreteOrderedEigenpairChart_decode_encode
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : ConcreteOrderedEigenpairChartDomain d r p) :
    concreteOrderedEigenpairChartDecode r p
      (concreteOrderedEigenpairChartEncode r p x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  exact selectedOrderedEigenpairDecodedCoordinates_eq_source r p
    (concreteOrderedEigenpairChartEncode r p x).1
    (concreteOrderedEigenpairChartEncode r p x).2 x.1 x.2 rfl

/-- Encoding after decoding is the identity on the coordinate target. -/
@[simp] theorem concreteOrderedEigenpairChart_encode_decode
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (y : ConcreteOrderedEigenpairChartTarget r p) :
    concreteOrderedEigenpairChartEncode r p
      (concreteOrderedEigenpairChartDecode r p y) = y := by
  apply Subtype.ext
  exact selectedOrderedEigenpairChart_encode_decode r p y.1 y.2

/-- Concrete two-sided chart equivalence, built from the explicit encoder and decoder. -/
def concreteOrderedEigenpairChartEquiv
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    ConcreteOrderedEigenpairChartDomain d r p ≃
      ConcreteOrderedEigenpairChartTarget r p where
  toFun := concreteOrderedEigenpairChartEncode r p
  invFun := concreteOrderedEigenpairChartDecode r p
  left_inv := concreteOrderedEigenpairChart_decode_encode r p
  right_inv := concreteOrderedEigenpairChart_encode_decode r p

/-- The zero-tangent block reconstruction is the canonical block-diagonal
matrix used by the coherent decoder. -/
@[simp] theorem eigenpairBlockReconstruction_zero_tangent
    {n : Type*} [Fintype n] [DecidableEq n]
    (y : EigenpairHermitianBlockCoordinates n) :
    ((eigenpairHermitianBlockLinearEquiv n).symm
      (y.1, ((0 : n → ℂ), y.2.2))).1 =
        eigenpairCanonicalMatrix y.1 y.2.2.1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [eigenpairHermitianBlockLinearEquiv_symm_apply,
      decodeEigenpairHermitianBlocks, eigenpairCanonicalMatrix,
      eigenpairTangentColumn]

/-- The coherent nonlinear decoder is definitionally the finite-coordinate
selected decoder, transported through the coherent carrier. -/
theorem coherentSelectedEigenpairDecode_eq_finiteCoordinateDecode
    {d : ℕ} (i : Fin d) (x : CoherentHermitianCoordinates d) :
    coherentSelectedEigenpairDecode i x =
      ⟨selectedEigenpairFinCoordinateChartDecode i x.value⟩ := by
  apply congrArg CoherentAnalyticCarrier.mk
  rw [selectedEigenpairFinCoordinateChartDecode_eq_read]
  apply congrArg (selectedMatrixFinCoordinateReadCLM i)
  ext a b
  simp [coherentComplexMatrixEquiv, coherentEigenpairConjugation,
    coherentEigenpairConjugationEuclidean,
    coherentSelectedProjectiveInputCLM, coherentSelectedBlockInputLinearMap,
    coherentProjectiveHouseholderFrame, coherentProjectiveUnitReconstruction,
    coherentLift, coherentCarrierWrapCLM, coherentAnalyticCarrierLinearEquiv,
    euclideanMatrixLinearEquiv, canonicalEigenpairProjectiveInputLinearMap,
    canonicalProjectiveChartCoordinatesLinearMap,
    canonicalProjectiveUnitVector, canonicalBlockDiagonalLinearMap,
    canonicalEigenpairChartDecode]
  rfl

/-- Consequently the concrete coherent decoder used by every selected chart
is globally `C¹`; this is the regularity hypothesis of
`coherentSelectedEigenpairLocalHomeomorph`. -/
theorem contDiff_concreteSelectedEigenpairDecode
    {d : ℕ} (i : Fin d) :
    ContDiff ℝ 1 (coherentSelectedEigenpairDecode i) :=
  contDiff_coherentSelectedEigenpairDecode i

/-- At an encoded chart point, coherent decoding agrees exactly with
matrix decoding followed by finite Hermitian coordinate extraction. -/
theorem coherentSelectedEigenpairDecode_encoded
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (hx : x ∈ orderedEigenpairReconstructionChartRegion d r p) :
    coherentSelectedEigenpairDecode (ofLex p).1
      ⟨(selectedEigenpairFinCoordinateLinearEquiv (ofLex p).1).symm
        (selectedOrderedEigenpairChartEncode r p x)⟩ = ⟨x.1⟩ := by
  rw [coherentSelectedEigenpairDecode_eq_finiteCoordinateDecode]
  congr 1
  have hdecode := selectedOrderedEigenpairChart_decode_encode r p x hx
  unfold selectedEigenpairFinCoordinateChartDecode
  rw [(selectedEigenpairFinCoordinateLinearEquiv (ofLex p).1).apply_symm_apply]
  change (selectedEigenpairFinCoordinateLinearEquiv (ofLex p).1).symm
      (selectedCoordinateEigenpairLinearEquiv (ofLex p).1
        (selectedEigenpairChartDecode (ofLex p).1
          (selectedOrderedEigenpairChartEncode r p x))) = x.1
  rw [hdecode]
  exact (selectedEigenpairFinCoordinateLinearEquiv (ofLex p).1).symm_apply_apply x.1

end CoareaNative.BlockBand
