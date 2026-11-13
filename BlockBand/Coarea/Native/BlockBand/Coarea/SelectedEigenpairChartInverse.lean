module

public import BlockBand.Coarea.Native.BlockBand.Coarea.OrderedEigenlineSelection
public import BlockBand.Coarea.Native.BlockBand.Coarea.NonlinearEigenpairChartDecode

/-!
# Inverse formulas for a selected ordered eigenpair chart

On a fixed least-entry chart of the simple-spectrum Hermitian locus, this
module records the nonlinear coordinates used by the phase-fixed
Householder decoder.  They consist of the ordered energy, the affine
projective coordinate of the selected eigenline at the chart pivot, and the
lower-right Hermitian block after conjugating by the same phase-fixed frame.
The two inverse identities below are algebraic statements on the chart
source; no smoothness assertion is made.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix Set

/-- A unit vector whose pivot is positive real is recovered by taking its
affine chart and applying phase-fixed unit reconstruction. -/
theorem projectiveUnitReconstruction_chart_of_phaseFixed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v k = ((v k).re : ℂ))
    (hpos : 0 < (v k).re) :
    projectiveUnitReconstruction k (projectiveEigenvectorChart k v) = v := by
  have hvk : v k ≠ 0 := by
    rw [hreal]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  rw [projectiveUnitReconstruction, projectiveEigenvectorReconstruction_chart k v hvk,
    projectiveAffineRepresentative, norm_smul, hv]
  have hnorm : ‖(v k)⁻¹‖ = ((v k).re)⁻¹ := by
    let a := (v k).re
    change ‖(v k)⁻¹‖ = a⁻¹
    rw [hreal]
    simp [a, abs_of_pos hpos]
  rw [hnorm, mul_one, inv_inv]
  apply PiLp.ext
  intro j
  simp only [PiLp.smul_apply, smul_eq_mul]
  change (((v k).re : ℂ) * ((v k)⁻¹ * v j)) = v j
  rw [← hreal]
  field_simp

/-- Affine projective coordinates of the selected ordered eigenline, written
in the complementary indexing used by the nonlinear decoder. -/
def selectedOrderedEigenlineAffineCoordinate
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) : Fin (d - 1) → ℂ :=
  fun j =>
    projectiveEigenvectorChart (Sum.inl Unit.unit)
      (WithLp.toLp 2 (fun a : Unit ⊕ Fin (d - 1) =>
        orderedEigenlineSelection d r x
          ((selectedCoordinateEquiv (ofLex p).1).symm a)))
      ⟨Sum.inr j, by simp⟩

/-- The selected eigenline, after putting the pivot first, is exactly the
canonical phase-fixed vector decoded from its affine coordinate. -/
theorem canonicalProjectiveUnitVector_selectedOrderedEigenlineAffineCoordinate
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (hx : x ∈ orderedEigenpairReconstructionChartRegion d r p) :
    canonicalProjectiveUnitVector
        (selectedOrderedEigenlineAffineCoordinate r p x) =
      WithLp.toLp 2 (fun a : Unit ⊕ Fin (d - 1) =>
        orderedEigenlineSelection d r x
          ((selectedCoordinateEquiv (ofLex p).1).symm a)) := by
  let i : Fin d := (ofLex p).1
  let v : EuclideanSpace ℂ (Fin d) := orderedEigenlineSelection d r x
  let w : EuclideanSpace ℂ (Unit ⊕ Fin (d - 1)) :=
    WithLp.toLp 2 (fun a => v ((selectedCoordinateEquiv i).symm a))
  have hi : leastOrderedEigenlineChart d r x = p :=
    (leastOrderedEigenlineChart_eq_iff r x p).2 hx
  have hwi : w (Sum.inl Unit.unit) =
      ((w (Sum.inl Unit.unit)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · change (v i).im = 0
      rw [show i = (ofLex (leastOrderedEigenlineChart d r x)).1 by rw [hi]]
      have : (v (ofLex (leastOrderedEigenlineChart d r x)).1).im = 0 := by
        change (orderedEigenlineSelection d r x
          (ofLex (leastOrderedEigenlineChart d r x)).1).im = 0
        rw [orderedEigenlineSelection_eq_candidate]
        exact orderedEigenlineChartCandidate_selectedCoordinate_im r _ x
      exact this
  have hwpos : 0 < (w (Sum.inl Unit.unit)).re := by
    change 0 < (v i).re
    rw [show i = (ofLex (leastOrderedEigenlineChart d r x)).1 by rw [hi]]
    exact orderedEigenlineSelection_selectedCoordinate_re_pos r x
  have hwnorm : ‖w‖ = 1 := by
    have hs :
        (∑ a : Unit ⊕ Fin (d - 1), ‖w a‖ ^ 2) =
          ∑ j : Fin d, ‖v j‖ ^ 2 := by
      simpa [w] using
        (Equiv.sum_comp (selectedCoordinateEquiv i).symm
          (fun j : Fin d => ‖v j‖ ^ 2))
    rw [EuclideanSpace.norm_eq, hs]
    simpa [EuclideanSpace.norm_eq] using norm_orderedEigenlineSelection r x
  have hrec := projectiveUnitReconstruction_chart_of_phaseFixed
    (Sum.inl Unit.unit) w hwnorm hwi hwpos
  have hz : canonicalProjectiveChartCoordinates
      (selectedOrderedEigenlineAffineCoordinate r p x) =
      projectiveEigenvectorChart (Sum.inl Unit.unit) w := by
    funext j
    rcases j with ⟨a, ha⟩
    rcases a with u | j
    · exact False.elim (ha (by cases u; rfl))
    · rfl
  rw [canonicalProjectiveUnitVector, hz]
  exact hrec

/-- The complementary Hermitian block after reindexing the pivot first and
conjugating by the phase-fixed Householder frame of the selected eigenline. -/
def selectedOrderedEigenpairComplementBlock
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    RealHermitianMatrix (Fin (d - 1)) :=
  let i := (ofLex p).1
  let A : RealHermitianMatrix (Fin d) :=
    ⟨hermitianOfFinCoordinates d x.1, (hermitianOfFinCoordinates d x.1).2⟩
  let A' := selectedCoordinateHermitianReindex i A
  let z := selectedOrderedEigenlineAffineCoordinate r p x
  let H := phaseFixedHouseholderFrame (Sum.inl Unit.unit)
    (canonicalProjectiveUnitVector z)
  let C : RealHermitianMatrix (Unit ⊕ Fin (d - 1)) :=
    ⟨Hᴴ * A'.1 * H,
      isHermitian_unitaryConjugation H A'.1 A'.2⟩
  ⟨C.1.submatrix Sum.inr Sum.inr, isHermitian_submatrix_inr C⟩

/-- Explicit nonlinear chart data: ordered energy, affine projective
coordinate at the fixed pivot, and the complementary Hermitian block in the
phase-fixed Householder frame. -/
def selectedOrderedEigenpairChartEncode
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (orderedEigenvalue (hermitianOfFinCoordinates d x.1) r,
    (selectedOrderedEigenlineAffineCoordinate r p x,
      selectedOrderedEigenpairComplementBlock r p x))

/-- Coordinate source of a fixed ordered chart: precisely the data
encoded by matrices in its least-entry simple-spectrum region. -/
def selectedOrderedEigenpairChartSource
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    Set (EigenpairHermitianBlockCoordinates (Fin (d - 1))) :=
  selectedOrderedEigenpairChartEncode r p ''
    orderedEigenpairReconstructionChartRegion d r p

/-- After reindexing the pivot first, the selected ordered eigenline still
satisfies the ordered eigenvector equation. -/
theorem selectedCoordinateReindex_mulVec_selectedEigenline
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (hx : x ∈ orderedEigenpairReconstructionChartRegion d r p) :
    let i := (ofLex p).1
    let A : RealHermitianMatrix (Fin d) :=
      ⟨hermitianOfFinCoordinates d x.1, (hermitianOfFinCoordinates d x.1).2⟩
    let A' := selectedCoordinateHermitianReindex i A
    let z := selectedOrderedEigenlineAffineCoordinate r p x
    A'.1.mulVec (canonicalProjectiveUnitVector z) =
      ((orderedEigenvalue (hermitianOfFinCoordinates d x.1) r : ℝ) : ℂ) •
        canonicalProjectiveUnitVector z := by
  dsimp only
  rw [canonicalProjectiveUnitVector_selectedOrderedEigenlineAffineCoordinate
    r p x hx]
  have heig := orderedEigenlineSelection_eigenvector r x
  funext a
  change (∑ j, (hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ)
      ((selectedCoordinateEquiv (ofLex p).1).symm a)
      ((selectedCoordinateEquiv (ofLex p).1).symm j) *
      orderedEigenlineSelection d r x
        ((selectedCoordinateEquiv (ofLex p).1).symm j)) = _
  have hsum := Equiv.sum_comp
    (selectedCoordinateEquiv (ofLex p).1).symm
    (fun j : Fin d =>
      (hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ)
        ((selectedCoordinateEquiv (ofLex p).1).symm a) j *
        orderedEigenlineSelection d r x j)
  rw [hsum]
  have h := congrFun heig ((selectedCoordinateEquiv (ofLex p).1).symm a)
  change (∑ j,
      (hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ)
        ((selectedCoordinateEquiv (ofLex p).1).symm a) j *
        orderedEigenlineSelection d r x j) =
      ((orderedEigenvalue (hermitianOfFinCoordinates d x.1) r : ℂ) *
        orderedEigenlineSelection d r x
          ((selectedCoordinateEquiv (ofLex p).1).symm a)) at h
  simpa using h

/-- In the moving phase-fixed frame, a chart matrix is exactly block
diagonal with its ordered energy and encoded complementary block. -/
theorem selectedOrderedEigenpair_conjugated_eq_canonical
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (hx : x ∈ orderedEigenpairReconstructionChartRegion d r p) :
    let i := (ofLex p).1
    let A : RealHermitianMatrix (Fin d) :=
      ⟨hermitianOfFinCoordinates d x.1, (hermitianOfFinCoordinates d x.1).2⟩
    let A' := selectedCoordinateHermitianReindex i A
    let z := selectedOrderedEigenlineAffineCoordinate r p x
    let H := phaseFixedHouseholderFrame (Sum.inl Unit.unit)
      (canonicalProjectiveUnitVector z)
    Hᴴ * A'.1 * H =
      eigenpairCanonicalMatrix
        (orderedEigenvalue (hermitianOfFinCoordinates d x.1) r)
        (selectedOrderedEigenpairComplementBlock r p x).1 := by
  dsimp only
  let z := selectedOrderedEigenlineAffineCoordinate r p x
  let v := canonicalProjectiveUnitVector z
  let H := phaseFixedHouseholderFrame (Sum.inl Unit.unit) v
  let A : RealHermitianMatrix (Fin d) :=
    ⟨hermitianOfFinCoordinates d x.1, (hermitianOfFinCoordinates d x.1).2⟩
  let A' := selectedCoordinateHermitianReindex (ofLex p).1 A
  let E : ℂ :=
    ((orderedEigenvalue (hermitianOfFinCoordinates d x.1) r : ℝ) : ℂ)
  have hAv : A'.1.mulVec v = E • v :=
    selectedCoordinateReindex_mulVec_selectedEigenline r p x hx
  have hHe : H.mulVec (phaseFixedCoordinateVector (Sum.inl Unit.unit)) = v :=
    phaseFixedHouseholderFrame_mulVec_canonicalProjectiveUnitVector z
  have hunit : Hᴴ * H = (1 : Matrix (Unit ⊕ Fin (d - 1))
      (Unit ⊕ Fin (d - 1)) ℂ) := by
    apply phaseFixedHouseholderFrame_unitary
    · exact norm_canonicalProjectiveUnitVector z
    · apply Complex.ext
      · rfl
      · rw [canonicalProjectiveUnitVector_selected]
        simp
    · exact canonicalProjectiveUnitVector_selected_re_pos z
  have hcol : (Hᴴ * A'.1 * H).mulVec
      (phaseFixedCoordinateVector (Sum.inl Unit.unit)) =
        E • phaseFixedCoordinateVector (Sum.inl Unit.unit) := by
    calc
      (Hᴴ * A'.1 * H).mulVec (phaseFixedCoordinateVector (Sum.inl Unit.unit)) =
          Hᴴ.mulVec (A'.1.mulVec
            (H.mulVec (phaseFixedCoordinateVector (Sum.inl Unit.unit)))) := by
              rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = Hᴴ.mulVec (A'.1.mulVec v) := by rw [hHe]
      _ = Hᴴ.mulVec (E • v) := by rw [hAv]
      _ = E • Hᴴ.mulVec v := Matrix.mulVec_smul _ _ _
      _ = E • Hᴴ.mulVec
          (H.mulVec (phaseFixedCoordinateVector (Sum.inl Unit.unit))) := by rw [hHe]
      _ = E • phaseFixedCoordinateVector (Sum.inl Unit.unit) := by
        congr 1
        calc
          Hᴴ.mulVec (H.mulVec
              (phaseFixedCoordinateVector (Sum.inl Unit.unit))) =
              (Hᴴ * H).mulVec
                (phaseFixedCoordinateVector (Sum.inl Unit.unit)) :=
            Matrix.mulVec_mulVec
              (phaseFixedCoordinateVector (Sum.inl Unit.unit)) Hᴴ H
          _ = phaseFixedCoordinateVector (Sum.inl Unit.unit) := by
            rw [hunit]
            simp
  let C : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
    Hᴴ * A'.1 * H
  have hC : C.IsHermitian := isHermitian_unitaryConjugation H A'.1 A'.2
  ext a b
  rcases a with u | a <;> rcases b with w | b
  · cases u
    cases w
    have h := congrFun hcol (Sum.inl Unit.unit)
    simpa [C, E, eigenpairCanonicalMatrix, phaseFixedCoordinateVector,
      Matrix.mulVec] using h
  · cases u
    change C (Sum.inl Unit.unit) (Sum.inr b) = 0
    rw [← hC.apply (Sum.inl Unit.unit) (Sum.inr b)]
    have h := congrFun hcol (Sum.inr b)
    simpa [phaseFixedCoordinateVector, Matrix.mulVec] using congrArg star h
  · have h := congrFun hcol (Sum.inr a)
    change C (Sum.inr a) (Sum.inl Unit.unit) = 0
    simpa [phaseFixedCoordinateVector, Matrix.mulVec] using h
  · change C (Sum.inr a) (Sum.inr b) =
      (selectedOrderedEigenpairComplementBlock r p x).1 a b
    rfl

/-- Decoding the explicit data of a matrix in the fixed chart returns
that matrix exactly. -/
theorem selectedOrderedEigenpairChart_decode_encode
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (hx : x ∈ orderedEigenpairReconstructionChartRegion d r p) :
    selectedEigenpairChartDecode (ofLex p).1
      (selectedOrderedEigenpairChartEncode r p x) =
        ⟨hermitianOfFinCoordinates d x.1,
          (hermitianOfFinCoordinates d x.1).2⟩ := by
  let i := (ofLex p).1
  let A : RealHermitianMatrix (Fin d) :=
    ⟨hermitianOfFinCoordinates d x.1, (hermitianOfFinCoordinates d x.1).2⟩
  let A' := selectedCoordinateHermitianReindex i A
  let z := selectedOrderedEigenlineAffineCoordinate r p x
  let H := phaseFixedHouseholderFrame (Sum.inl Unit.unit)
    (canonicalProjectiveUnitVector z)
  have hconj : Hᴴ * A'.1 * H =
      eigenpairCanonicalMatrix
        (orderedEigenvalue (hermitianOfFinCoordinates d x.1) r)
        (selectedOrderedEigenpairComplementBlock r p x).1 :=
    selectedOrderedEigenpair_conjugated_eq_canonical r p x hx
  have hunit : Hᴴ * H = (1 : Matrix (Unit ⊕ Fin (d - 1))
      (Unit ⊕ Fin (d - 1)) ℂ) := by
    apply phaseFixedHouseholderFrame_unitary
    · exact norm_canonicalProjectiveUnitVector z
    · apply Complex.ext
      · rfl
      · rw [canonicalProjectiveUnitVector_selected]
        simp
    · exact canonicalProjectiveUnitVector_selected_re_pos z
  have hdecode : (canonicalEigenpairChartDecode
      (selectedOrderedEigenpairChartEncode r p x)).1 = A'.1 := by
    change H *
      ((eigenpairHermitianBlockLinearEquiv (Fin (d - 1))).symm
        (orderedEigenvalue (hermitianOfFinCoordinates d x.1) r,
          ((0 : Fin (d - 1) → ℂ),
            selectedOrderedEigenpairComplementBlock r p x))).1 * Hᴴ = A'.1
    have hD : ((eigenpairHermitianBlockLinearEquiv (Fin (d - 1))).symm
        (orderedEigenvalue (hermitianOfFinCoordinates d x.1) r,
          ((0 : Fin (d - 1) → ℂ),
            selectedOrderedEigenpairComplementBlock r p x))).1 =
        eigenpairCanonicalMatrix
          (orderedEigenvalue (hermitianOfFinCoordinates d x.1) r)
          (selectedOrderedEigenpairComplementBlock r p x).1 := by
      ext a b
      rcases a with a | a <;> rcases b with b | b <;>
        simp [eigenpairHermitianBlockLinearEquiv_symm_apply,
          decodeEigenpairHermitianBlocks, eigenpairCanonicalMatrix,
          eigenpairTangentColumn]
    rw [hD, ← hconj]
    change H * (Hᴴ * A'.1 * H) * Hᴴ = A'.1
    exact (unitaryConjugationLinearEquiv H hunit).left_inv A'.1
  apply Subtype.ext
  change (selectedCoordinateHermitianUnreindex i
    (canonicalEigenpairChartDecode (selectedOrderedEigenpairChartEncode r p x))).1 = A.1
  rw [show canonicalEigenpairChartDecode
      (selectedOrderedEigenpairChartEncode r p x) = A' by
    apply Subtype.ext
    exact hdecode]
  exact congrArg Subtype.val (selectedCoordinateHermitian_unreindex_reindex i A)

/-- Finite-ordinal Hermitian coordinates of a matrix. -/
def finCoordinatesOfHermitian {d : ℕ}
    (A : HermitianMatrix (Fin d)) : HermitianCoordinateSpace d :=
  fun j => coordinatesOfHermitian A ((hermitianCoordinateEquivFin d).symm j)

@[simp] theorem hermitianOfFinCoordinates_finCoordinatesOfHermitian
    {d : ℕ} (A : HermitianMatrix (Fin d)) :
    hermitianOfFinCoordinates d (finCoordinatesOfHermitian A) = A := by
  unfold hermitianOfFinCoordinates finCoordinatesOfHermitian
  rw [show
      (fun j => coordinatesOfHermitian A ((hermitianCoordinateEquivFin d).symm j)) ∘
          hermitianCoordinateEquivFin d = coordinatesOfHermitian A by
    funext j
    simp]
  exact hermitianOfCoordinates_coordinatesOfHermitian A

/-- Decoding data from the source again has simple spectrum. -/
theorem selectedOrderedEigenpairChartDecode_mem_simple
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (y : EigenpairHermitianBlockCoordinates (Fin (d - 1)))
    (hy : y ∈ selectedOrderedEigenpairChartSource r p) :
    finCoordinatesOfHermitian (selectedEigenpairChartDecode (ofLex p).1 y) ∈
      hermitianSimpleSpectrumCoordinates d := by
  rcases hy with ⟨x, hx, rfl⟩
  rw [selectedOrderedEigenpairChart_decode_encode r p x hx]
  change (hermitianOfFinCoordinates d
    (finCoordinatesOfHermitian
      ⟨hermitianOfFinCoordinates d x.1, (hermitianOfFinCoordinates d x.1).2⟩) :
      Matrix (Fin d) (Fin d) ℂ).charpoly.Separable
  rw [hermitianOfFinCoordinates_finCoordinatesOfHermitian]
  exact x.2

/-- Encoding after decoding is the identity on the chart source. -/
theorem selectedOrderedEigenpairChart_encode_decode
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (y : EigenpairHermitianBlockCoordinates (Fin (d - 1)))
    (hy : y ∈ selectedOrderedEigenpairChartSource r p) :
    selectedOrderedEigenpairChartEncode r p
      ⟨finCoordinatesOfHermitian
          (selectedEigenpairChartDecode (ofLex p).1 y),
        selectedOrderedEigenpairChartDecode_mem_simple r p y hy⟩ = y := by
  rcases hy with ⟨x, hx, rfl⟩
  have hdecode := selectedOrderedEigenpairChart_decode_encode r p x hx
  have hcoords : finCoordinatesOfHermitian
      (selectedEigenpairChartDecode (ofLex p).1
        (selectedOrderedEigenpairChartEncode r p x)) = x.1 := by
    rw [hdecode]
    apply funext
    intro j
    change coordinatesOfHermitian (hermitianOfFinCoordinates d x.1)
      ((hermitianCoordinateEquivFin d).symm j) = x.1 j
    rw [hermitianOfFinCoordinates]
    simp [coordinatesOfHermitian_hermitianOfCoordinates]
  congr 1
  exact Subtype.ext hcoords

end CoareaNative.BlockBand
