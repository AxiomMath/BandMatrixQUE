module

public import BlockBand.Coarea.Native.BlockBand.Coarea.NonlinearEigenpairLocalJacobian
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairDerivativeIdentification
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Local inverse for the coherent selected eigenpair decoder

This module states the inverse-function step under two explicit hypotheses.
The nonvanishing condition `det (E I - B) ≠ 0` already supplies the canonical
continuous-linear equivalence on the zero slice.  After transport to the
coherent carrier, the two hypotheses are:

* the final equality between the computed readback derivative and that
  transported canonical equivalence; and
* `C¹` regularity of the coherent decoder near the base point.

Under precisely these two hypotheses, Mathlib's inverse function theorem gives
an `OpenPartialHomeomorph` whose underlying map is the coherent selected
decoder and whose source contains the zero-slice point.  Strict
differentiability comes from the `C¹` hypothesis, not from pointwise
differentiability.  Both hypotheses are proved in sibling modules:
`coherentSelectedEigenpairDerivativeIdentified_of_gap` and
`contDiffAt_coherentSelectedEigenpairDecode`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

/-- The coherent selected zero-slice base point used in the local inverse theorem. -/
def coherentSelectedEigenpairZeroInput {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    CoherentHermitianCoordinates d :=
  ⟨selectedEigenpairZeroSliceCoordinates i E B⟩

/-- Selected block coordinates as a continuous-linear equivalence from the
coherent Hermitian coordinate carrier. -/
def coherentSelectedBlockContinuousLinearEquiv {d : ℕ} (i : Fin d) :
    CoherentHermitianCoordinates d ≃L[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (coherentHermitianCoordinatesEquiv d).trans
    (selectedEigenpairFinCoordinateLinearEquiv i).toContinuousLinearEquiv

/-- The canonical nonsingular zero-slice differential, transported to the
coherent Hermitian coordinate carrier. -/
def coherentSelectedEigenpairCanonicalContinuousLinearEquiv
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    CoherentHermitianCoordinates d ≃L[ℝ] CoherentHermitianCoordinates d :=
  (coherentSelectedBlockContinuousLinearEquiv i).trans
    ((selectedEigenpairCoordinateChartAlgebraicContinuousLinearEquiv
      i E B hgap).trans
        (coherentSelectedBlockContinuousLinearEquiv i).symm)

/-- The zero-slice identification needed by the inverse function theorem: the
readback derivative agrees with the canonical nonsingular gap differential after
coherent transport.  It is proved as
`coherentSelectedEigenpairDerivativeIdentified_of_gap`. -/
def CoherentSelectedEigenpairDerivativeIdentified
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) : Prop :=
  coherentSelectedEigenpairReadbackDifferential i E B =
    (coherentSelectedEigenpairCanonicalContinuousLinearEquiv i E B hgap :
      CoherentHermitianCoordinates d →L[ℝ] CoherentHermitianCoordinates d)

/-- Once the exact derivative identification is supplied, the coherent
selected decoder has the canonical invertible Fréchet derivative at the zero
slice. -/
theorem hasFDerivAt_coherentSelectedEigenpairDecode_zero_equiv
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0)
    (hident : CoherentSelectedEigenpairDerivativeIdentified i E B hgap) :
    HasFDerivAt (coherentSelectedEigenpairDecode i)
      (coherentSelectedEigenpairCanonicalContinuousLinearEquiv i E B hgap :
        CoherentHermitianCoordinates d →L[ℝ] CoherentHermitianCoordinates d)
      (coherentSelectedEigenpairZeroInput i E B) := by
  rw [← hident]
  exact hasFDerivAt_coherentSelectedEigenpairDecode_zero i E B

/-- `C¹` regularity plus the exact derivative identification yields the strict
invertible derivative required by the inverse function theorem.  This theorem
records the bridge explicitly instead of treating ordinary differentiability
at one point as if it implied strict differentiability. -/
theorem hasStrictFDerivAt_coherentSelectedEigenpairDecode_zero_equiv
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0)
    (hcont : ContDiffAt ℝ 1 (coherentSelectedEigenpairDecode i)
      (coherentSelectedEigenpairZeroInput i E B))
    (hident : CoherentSelectedEigenpairDerivativeIdentified i E B hgap) :
    HasStrictFDerivAt (coherentSelectedEigenpairDecode i)
      (coherentSelectedEigenpairCanonicalContinuousLinearEquiv i E B hgap :
        CoherentHermitianCoordinates d →L[ℝ] CoherentHermitianCoordinates d)
      (coherentSelectedEigenpairZeroInput i E B) := by
  exact hcont.hasStrictFDerivAt'
    (hasFDerivAt_coherentSelectedEigenpairDecode_zero_equiv
      i E B hgap hident) (by norm_num)

/-- The local inverse-function theorem for the coherent selected
decoder at a nondegenerate zero slice.  Its underlying map is exactly
`coherentSelectedEigenpairDecode i`; the following lemmas expose the source
and target membership guaranteed at the base point. -/
def coherentSelectedEigenpairLocalHomeomorph
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0)
    (hcont : ContDiffAt ℝ 1 (coherentSelectedEigenpairDecode i)
      (coherentSelectedEigenpairZeroInput i E B))
    (hident : CoherentSelectedEigenpairDerivativeIdentified i E B hgap) :
    OpenPartialHomeomorph (CoherentHermitianCoordinates d)
      (CoherentHermitianCoordinates d) :=
  (hasStrictFDerivAt_coherentSelectedEigenpairDecode_zero_equiv
    i E B hgap hcont hident).toOpenPartialHomeomorph
      (coherentSelectedEigenpairDecode i)

@[simp] theorem coherentSelectedEigenpairLocalHomeomorph_coe
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0)
    (hcont : ContDiffAt ℝ 1 (coherentSelectedEigenpairDecode i)
      (coherentSelectedEigenpairZeroInput i E B))
    (hident : CoherentSelectedEigenpairDerivativeIdentified i E B hgap) :
    (coherentSelectedEigenpairLocalHomeomorph i E B hgap hcont hident :
      CoherentHermitianCoordinates d → CoherentHermitianCoordinates d) =
        coherentSelectedEigenpairDecode i := by
  rfl

/-- The zero-slice point belongs to the source neighborhood of the local
homeomorphism. -/
theorem coherentSelectedEigenpairZeroInput_mem_localHomeomorph_source
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0)
    (hcont : ContDiffAt ℝ 1 (coherentSelectedEigenpairDecode i)
      (coherentSelectedEigenpairZeroInput i E B))
    (hident : CoherentSelectedEigenpairDerivativeIdentified i E B hgap) :
    coherentSelectedEigenpairZeroInput i E B ∈
      (coherentSelectedEigenpairLocalHomeomorph
        i E B hgap hcont hident).source := by
  exact (hasStrictFDerivAt_coherentSelectedEigenpairDecode_zero_equiv
    i E B hgap hcont hident).mem_toOpenPartialHomeomorph_source

/-- The image of the zero-slice point belongs to the target neighborhood of
the local homeomorphism. -/
theorem coherentSelectedEigenpairDecode_zero_mem_localHomeomorph_target
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0)
    (hcont : ContDiffAt ℝ 1 (coherentSelectedEigenpairDecode i)
      (coherentSelectedEigenpairZeroInput i E B))
    (hident : CoherentSelectedEigenpairDerivativeIdentified i E B hgap) :
    coherentSelectedEigenpairDecode i (coherentSelectedEigenpairZeroInput i E B) ∈
      (coherentSelectedEigenpairLocalHomeomorph
        i E B hgap hcont hident).target := by
  exact (hasStrictFDerivAt_coherentSelectedEigenpairDecode_zero_equiv
    i E B hgap hcont hident).image_mem_toOpenPartialHomeomorph_target

/-- The inverse branch has the inverse canonical differential at the image of
the zero slice. -/
theorem hasStrictFDerivAt_coherentSelectedEigenpairLocalHomeomorph_symm
    {d : ℕ} (i : Fin d) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0)
    (hcont : ContDiffAt ℝ 1 (coherentSelectedEigenpairDecode i)
      (coherentSelectedEigenpairZeroInput i E B))
    (hident : CoherentSelectedEigenpairDerivativeIdentified i E B hgap) :
    HasStrictFDerivAt
      (coherentSelectedEigenpairLocalHomeomorph
        i E B hgap hcont hident).symm
      ((coherentSelectedEigenpairCanonicalContinuousLinearEquiv
        i E B hgap).symm :
          CoherentHermitianCoordinates d →L[ℝ]
            CoherentHermitianCoordinates d)
      (coherentSelectedEigenpairDecode i
        (coherentSelectedEigenpairZeroInput i E B)) := by
  exact (hasStrictFDerivAt_coherentSelectedEigenpairDecode_zero_equiv
    i E B hgap hcont hident).to_localInverse

end CoareaNative.BlockBand
