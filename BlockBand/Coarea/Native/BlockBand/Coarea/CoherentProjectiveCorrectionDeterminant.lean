module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairGlobalDeterminant
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairMatrixDifferential
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentProjectiveHouseholderSmooth

/-!
# Arbitrary-chart differential underlying the coherent projective correction

This module carries out the product-rule/readback step at an arbitrary affine
projective coordinate.  Unlike the zero-slice calculation, the Householder
term is the global differential from
`CoherentProjectiveHouseholderSmooth`.  The resulting explicit three-term map
is proved to be the Fréchet derivative of `H(z) D(E,B) H(z)ᴴ`, both
before and after selected Hermitian-coordinate readback.

The determinant of the normalized projective block is computed from this map:
after conjugating the explicit map below by the base Householder frame, one
exposes its block-triangular form and applies the real rank-one determinant
lemma to the normalized affine tangent map.  No zero-slice restriction is used
here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

/-- The derivative of an arbitrary coherent Householder entry,
pulled back from projective coordinates to the full selected Hermitian input. -/
def coherentEigenpairHouseholderEntryDifferentialAt {d : ℕ} (i : Fin d)
    (x : CoherentHermitianCoordinates d) (a b : Unit ⊕ Fin (d - 1)) :
    CoherentHermitianCoordinates d →L[ℝ] ℂ :=
  (coherentProjectiveHouseholderFrameEntryDifferentialAt
      (Sum.inl Unit.unit) a b (coherentSelectedProjectiveInputCLM i x)).comp
    (coherentSelectedProjectiveInputCLM i)

/-- The pulled-back global Householder entry differential is exact at every
coherent input. -/
theorem hasFDerivAt_coherentEigenpairHouseholderEntry_global {d : ℕ}
    (i : Fin d) (x : CoherentHermitianCoordinates d)
    (a b : Unit ⊕ Fin (d - 1)) :
    HasFDerivAt (fun y : CoherentHermitianCoordinates d =>
      coherentProjectiveHouseholderFrame (Sum.inl Unit.unit)
        (coherentSelectedProjectiveInputCLM i y) a b)
      (coherentEigenpairHouseholderEntryDifferentialAt i x a b) x := by
  exact (hasFDerivAt_coherentProjectiveHouseholderFrameEntry
    (Sum.inl Unit.unit) a b (coherentSelectedProjectiveInputCLM i x)).comp
      x (coherentSelectedProjectiveInputCLM i).hasFDerivAt

/-- The explicit three-term product-rule differential of a matrix entry of
`H D Hᴴ` at an arbitrary coherent input. -/
def coherentEigenpairConjugationEntryDifferentialAt {d : ℕ} (i : Fin d)
    (x : CoherentHermitianCoordinates d) (a b : Unit ⊕ Fin (d - 1)) :
    CoherentHermitianCoordinates d →L[ℝ] ℂ :=
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let P := coherentSelectedProjectiveInputCLM i
  let H := coherentProjectiveHouseholderFrame e (P x)
  let D := fun p q => coherentBlockDiagonalEntryCLM i p q x
  let H' := fun p q => coherentEigenpairHouseholderEntryDifferentialAt i x p q
  let D' := fun p q => coherentBlockDiagonalEntryCLM i p q
  ∑ c, (
    (∑ q, H a q * D q c) •
        (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp (H' b c)) +
      star (H b c) •
        (∑ q, (H a q • D' q c + D q c • H' a q)))

/-- At every affine chart point, the preceding three-term expression is the
scalar derivative of the corresponding conjugated matrix entry. -/
theorem hasFDerivAt_coherentEigenpairConjugationEntry_global {d : ℕ}
    (i : Fin d) (x : CoherentHermitianCoordinates d)
    (a b : Unit ⊕ Fin (d - 1)) :
    HasFDerivAt (coherentEigenpairConjugationEntry i a b)
      (coherentEigenpairConjugationEntryDifferentialAt i x a b) x := by
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let P := coherentSelectedProjectiveInputCLM i
  have hH (p q : Unit ⊕ Fin (d - 1)) :=
    hasFDerivAt_coherentEigenpairHouseholderEntry_global i x p q
  have hD (p q : Unit ⊕ Fin (d - 1)) :
      HasFDerivAt (fun y : CoherentHermitianCoordinates d =>
        coherentBlockDiagonalEntryCLM i p q y)
        (coherentBlockDiagonalEntryCLM i p q) x :=
    (coherentBlockDiagonalEntryCLM i p q).hasFDerivAt
  change HasFDerivAt (fun y => ∑ c, (∑ q,
    coherentProjectiveHouseholderFrame e (P y) a q *
      coherentBlockDiagonalEntryCLM i q c y) *
    star (coherentProjectiveHouseholderFrame e (P y) b c)) _ x
  have hinner (c : Unit ⊕ Fin (d - 1)) :=
    HasFDerivAt.sum (u := Finset.univ) (x := x) fun q _ =>
      (hH a q).mul (hD q c)
  have hout := HasFDerivAt.sum (u := Finset.univ) (x := x) fun c _ =>
    hinner c |>.mul (hH b c).star
  convert hout using 1
  · funext y
    simp only [Finset.sum_apply, Pi.mul_apply]
    rfl
  · apply ContinuousLinearMap.ext
    intro u
    simp only [coherentEigenpairConjugationEntryDifferentialAt,
      Finset.sum_apply, Pi.mul_apply]

/-- Entrywise packing of the arbitrary-point product-rule differential. -/
def coherentEigenpairMatrixDifferentialAt {d : ℕ} (i : Fin d)
    (x : CoherentHermitianCoordinates d) :
    CoherentHermitianCoordinates d →L[ℝ]
      Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
    coherentEigenpairConjugationEntryDifferentialAt i x a b

/-- Euclidean packing of the arbitrary-point product-rule differential. -/
def coherentEigenpairEuclideanDifferentialAt {d : ℕ} (i : Fin d)
    (x : CoherentHermitianCoordinates d) :
    CoherentHermitianCoordinates d →L[ℝ]
      EuclideanSpace ℂ
        ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) :=
  ((LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv
        ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) ℂ).symm.toLinearEquiv.restrictScalars ℝ)) :
      (((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) → ℂ) ≃L[ℝ]
        EuclideanSpace ℂ
          ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1)))).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun ab =>
      coherentEigenpairConjugationEntryDifferentialAt i x ab.1 ab.2)

/-- Coherent-matrix packing of the arbitrary-point product-rule differential. -/
def coherentEigenpairPackedMatrixDifferentialAt {d : ℕ} (i : Fin d)
    (x : CoherentHermitianCoordinates d) :
    CoherentHermitianCoordinates d →L[ℝ]
      CoherentComplexMatrix (Unit ⊕ Fin (d - 1)) :=
  (coherentCarrierWrapCLM
    (EuclideanSpace ℂ
      ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))))).comp
    (coherentEigenpairEuclideanDifferentialAt i x)

/-- The Euclidean coherent conjugation has the explicit arbitrary-point
product-rule derivative. -/
theorem hasFDerivAt_coherentEigenpairConjugationEuclidean_global {d : ℕ}
    (i : Fin d) (x : CoherentHermitianCoordinates d) :
    HasFDerivAt (coherentEigenpairConjugationEuclidean i)
      (coherentEigenpairEuclideanDifferentialAt i x) x := by
  have hfun : HasFDerivAt
      (fun y : CoherentHermitianCoordinates d => fun
        ab : (Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1)) =>
          coherentEigenpairConjugationEntry i ab.1 ab.2 y)
      (ContinuousLinearMap.pi fun ab =>
        coherentEigenpairConjugationEntryDifferentialAt i x ab.1 ab.2) x := by
    rw [hasFDerivAt_pi]
    intro ab
    exact hasFDerivAt_coherentEigenpairConjugationEntry_global i x ab.1 ab.2
  let eR : EuclideanSpace ℂ
      ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) ≃L[ℝ]
      (((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) → ℂ) :=
    LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv _ ℂ).toLinearEquiv.restrictScalars ℝ)
  have h := eR.symm.hasFDerivAt.comp x hfun
  convert h using 1
  · funext y
    rfl
  · rfl

/-- The coherently packed joint reconstruction has the explicit arbitrary-point
product-rule derivative. -/
theorem hasFDerivAt_coherentEigenpairConjugation_explicit_global {d : ℕ}
    (i : Fin d) (x : CoherentHermitianCoordinates d) :
    HasFDerivAt (coherentEigenpairConjugation i)
      (coherentEigenpairPackedMatrixDifferentialAt i x) x := by
  have h := (coherentCarrierWrapCLM
      (EuclideanSpace ℂ
        ((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))))).hasFDerivAt.comp
    x (hasFDerivAt_coherentEigenpairConjugationEuclidean_global i x)
  convert h using 1 <;> rfl

/-- Selected-coordinate readback of the explicit arbitrary-point differential. -/
def coherentEigenpairReadbackMatrixDifferentialAt {d : ℕ} (i : Fin d)
    (x : CoherentHermitianCoordinates d) :
    CoherentHermitianCoordinates d →L[ℝ] CoherentHermitianCoordinates d :=
  (coherentSelectedMatrixReadbackCLM i).comp
    (coherentEigenpairPackedMatrixDifferentialAt i x)

/-- The selected decoder has the explicit readback derivative at every
arbitrary affine-projective input. -/
theorem hasFDerivAt_coherentSelectedEigenpairDecode_explicit_global {d : ℕ}
    (i : Fin d) (x : CoherentHermitianCoordinates d) :
    HasFDerivAt (coherentSelectedEigenpairDecode i)
      (coherentEigenpairReadbackMatrixDifferentialAt i x) x := by
  exact (coherentSelectedMatrixReadbackCLM i).hasFDerivAt.comp x
    (hasFDerivAt_coherentEigenpairConjugation_explicit_global i x)

/-- The Fréchet derivative at an arbitrary global eigenpair input is
exactly the explicit Householder product-rule/readback map. -/
theorem fderiv_coherentSelectedEigenpairDecode_globalInput_eq_explicit {d : ℕ}
    (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    fderiv ℝ (coherentSelectedEigenpairDecode i)
        (coherentEigenpairGlobalInput i E z B) =
      coherentEigenpairReadbackMatrixDifferentialAt i
        (coherentEigenpairGlobalInput i E z B) :=
  (hasFDerivAt_coherentSelectedEigenpairDecode_explicit_global i
    (coherentEigenpairGlobalInput i E z B)).fderiv

/-- Consequently, the projective correction itself is an entirely explicit
composition: inverse gap differential followed by the arbitrary-point
Householder product-rule/readback map.  This is the determinant expression on
which the remaining block-triangular/rank-one calculation must operate. -/
theorem coherentEigenpairProjectiveCorrection_eq_explicit {d : ℕ}
    (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    coherentEigenpairProjectiveCorrection i E z B hgap =
      ((coherentEigenpairGapDifferential i E B).equivOfDetNeZero
        (det_coherentEigenpairGapDifferential_ne_zero i E B hgap)).symm.toLinearMap.comp
      (coherentEigenpairReadbackMatrixDifferentialAt i
        (coherentEigenpairGlobalInput i E z B)).toLinearMap := by
  rw [coherentEigenpairProjectiveCorrection,
    fderiv_coherentSelectedEigenpairDecode_globalInput_eq_explicit]

/-- Maximal exact determinant reduction after expanding the arbitrary
point differential.  Proving that its left factor is the normalized affine
projective density is now a concrete determinant calculation on the explicit
three-term map, with no hidden analytic derivative. -/
theorem abs_det_fderiv_coherentSelectedEigenpairDecode_eq_explicit_correction_mul_normSq
    {d : ℕ} (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    |LinearMap.det ((fderiv ℝ (coherentSelectedEigenpairDecode i)
      (coherentEigenpairGlobalInput i E z B)).toLinearMap)| =
      |LinearMap.det
        (((coherentEigenpairGapDifferential i E B).equivOfDetNeZero
          (det_coherentEigenpairGapDifferential_ne_zero i E B hgap)).symm.toLinearMap.comp
        (coherentEigenpairReadbackMatrixDifferentialAt i
          (coherentEigenpairGlobalInput i E z B)).toLinearMap)| *
        Complex.normSq (eigenpairGapMatrix E B.1).det := by
  rw [abs_det_fderiv_coherentSelectedEigenpairDecode_eq_correction_mul_normSq
    i E z B hgap, coherentEigenpairProjectiveCorrection_eq_explicit]

end CoareaNative.BlockBand
