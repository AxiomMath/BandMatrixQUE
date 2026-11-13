module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairConjugationDerivative

/-!
# Explicit scalar derivatives for coherent eigenpair conjugation

This module retains the exact continuous-linear terms in the entrywise product
rule for `H(z) D(E,B) H(z)ᴴ` at a zero-projective slice.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

/-- The coherent selected zero-projective input. -/
def coherentEigenpairZeroInput {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    CoherentHermitianCoordinates d :=
  ⟨selectedEigenpairZeroSliceCoordinates i E B⟩

/-- The phase-fixed coherent unit vector at the selected zero slice. -/
def coherentEigenpairZeroUnit {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    CoherentUnitVector (Unit ⊕ Fin (d - 1)) :=
  coherentProjectiveUnitReconstruction (Sum.inl Unit.unit)
    (coherentSelectedProjectiveInputCLM i
      (coherentEigenpairZeroInput i E B))

/-- Named derivative of a Householder entry with respect to full coherent
Hermitian input coordinates. -/
def coherentEigenpairHouseholderEntryDifferential {d : ℕ}
    (i : Fin d) (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1)))
    (a b : Unit ⊕ Fin (d - 1)) :
    CoherentHermitianCoordinates d →L[ℝ] ℂ :=
  (coherentPhaseFixedHouseholderFrameEntryDifferential
      (Sum.inl Unit.unit) a b (coherentEigenpairZeroUnit i E B)).comp
    ((coherentProjectiveChartTangentInsertion (Sum.inl Unit.unit)).comp
      (coherentSelectedProjectiveInputCLM i))

/-- Named derivative of a block-diagonal entry. -/
def coherentEigenpairBlockEntryDifferential {d : ℕ}
    (i : Fin d) (_E : ℝ) (_B : RealHermitianMatrix (Fin (d - 1)))
    (a b : Unit ⊕ Fin (d - 1)) :
    CoherentHermitianCoordinates d →L[ℝ] ℂ :=
  coherentBlockDiagonalEntryCLM i a b

/-- The scalar `(a,b)` entry of coherent joint conjugation. -/
def coherentEigenpairConjugationEntry {d : ℕ} (i : Fin d)
    (a b : Unit ⊕ Fin (d - 1)) (x : CoherentHermitianCoordinates d) : ℂ :=
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let H := coherentProjectiveHouseholderFrame e
    (coherentSelectedProjectiveInputCLM i x)
  let D := canonicalBlockDiagonalLinearMap
    (coherentSelectedBlockInputLinearMap i x)
  (H * D * Matrix.conjTranspose H) a b

/-- The explicit three-term nested finite-sum product-rule differential for
one output entry. -/
def coherentEigenpairConjugationEntryDifferential {d : ℕ}
    (i : Fin d) (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1)))
    (a b : Unit ⊕ Fin (d - 1)) :
    CoherentHermitianCoordinates d →L[ℝ] ℂ :=
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let x0 := coherentEigenpairZeroInput i E B
  let P := coherentSelectedProjectiveInputCLM i
  let H0 := coherentProjectiveHouseholderFrame e (P x0)
  let D0 := fun p q => coherentBlockDiagonalEntryCLM i p q x0
  let H' := fun p q => coherentEigenpairHouseholderEntryDifferential i E B p q
  let D' := fun p q => coherentEigenpairBlockEntryDifferential i E B p q
  ∑ c, (
    (∑ z, H0 a z * D0 z c) •
        (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp (H' b c)) +
      star (H0 b c) •
        (∑ z, (H0 a z • D' z c + D0 z c • H' a z)))

@[simp] theorem coherentSelectedProjectiveInput_zeroInput
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    coherentSelectedProjectiveInputCLM i
        (coherentEigenpairZeroInput i E B) =
      (⟨0⟩ : CoherentProjectiveCoordinates
        (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1))) :=
  coherentSelectedProjectiveInputCLM_zeroSlice i E B

/-- Exact zero-slice derivative of every coherent Householder entry. -/
theorem hasFDerivAt_coherentEigenpairHouseholderEntry_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (a b : Unit ⊕ Fin (d - 1)) :
    HasFDerivAt (fun x : CoherentHermitianCoordinates d =>
      coherentProjectiveHouseholderFrame (Sum.inl Unit.unit)
        (coherentSelectedProjectiveInputCLM i x) a b)
      (coherentEigenpairHouseholderEntryDifferential i E B a b)
      (coherentEigenpairZeroInput i E B) := by
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let x0 := coherentEigenpairZeroInput i E B
  let P := coherentSelectedProjectiveInputCLM i
  have hP0 : P x0 = (⟨0⟩ : CoherentProjectiveCoordinates e) :=
    coherentSelectedProjectiveInput_zeroInput i E B
  have hu := hasFDerivAt_coherentProjectiveUnitReconstruction_zero e
  rw [← hP0] at hu
  have hu' := hu.comp x0 P.hasFDerivAt
  have hv : 1 + ((coherentProjectiveUnitReconstruction e (P x0)).value e).re ≠ 0 := by
    rw [hP0]
    simp [coherentProjectiveUnitReconstruction, coherentLift,
      projectiveSelectedVector, projectiveEigenvectorReconstruction]
  have hH := hasFDerivAt_coherentPhaseFixedHouseholderFrameEntry e a b
    (coherentProjectiveUnitReconstruction e (P x0)) hv
  have h := hH.comp x0 hu'
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro u
    rfl

/-- Block entries have their named linear derivative everywhere. -/
theorem hasFDerivAt_coherentEigenpairBlockEntry_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (a b : Unit ⊕ Fin (d - 1)) :
    HasFDerivAt (fun x : CoherentHermitianCoordinates d =>
      coherentBlockDiagonalEntryCLM i a b x)
      (coherentEigenpairBlockEntryDifferential i E B a b)
      (coherentEigenpairZeroInput i E B) :=
  (coherentBlockDiagonalEntryCLM i a b).hasFDerivAt

/-- Scalar product-rule theorem for every entry of `H D Hᴴ`. -/
theorem hasFDerivAt_coherentEigenpairConjugationEntry_zero
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (a b : Unit ⊕ Fin (d - 1)) :
    HasFDerivAt (coherentEigenpairConjugationEntry i a b)
      (coherentEigenpairConjugationEntryDifferential i E B a b)
      (coherentEigenpairZeroInput i E B) := by
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let x0 := coherentEigenpairZeroInput i E B
  let P := coherentSelectedProjectiveInputCLM i
  have hH (p q : Unit ⊕ Fin (d - 1)) :=
    hasFDerivAt_coherentEigenpairHouseholderEntry_zero i E B p q
  have hD (p q : Unit ⊕ Fin (d - 1)) :=
    hasFDerivAt_coherentEigenpairBlockEntry_zero i E B p q
  change HasFDerivAt (fun x => ∑ c, (∑ z,
    coherentProjectiveHouseholderFrame e (P x) a z *
      coherentBlockDiagonalEntryCLM i z c x) *
    star (coherentProjectiveHouseholderFrame e (P x) b c)) _ x0
  have hinner (c : Unit ⊕ Fin (d - 1)) :=
    HasFDerivAt.sum (u := Finset.univ) (x := x0) fun z _ =>
      (hH a z).mul (hD z c)
  have hout := HasFDerivAt.sum (u := Finset.univ) (x := x0) fun c _ =>
    hinner c |>.mul (hH b c).star
  convert hout using 1
  · funext x
    simp only [Finset.sum_apply, Pi.mul_apply]
    rfl
  · apply ContinuousLinearMap.ext
    intro u
    simp only [coherentEigenpairConjugationEntryDifferential, Finset.sum_apply,
      Pi.mul_apply]
    rfl

end CoareaNative.BlockBand
