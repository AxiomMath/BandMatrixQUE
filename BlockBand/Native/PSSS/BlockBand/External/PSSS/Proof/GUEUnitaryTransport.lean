module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.FixedVector
public import BlockBand.Native.PSSS.BlockBand.Coarea.PhysicalFreshGUEDensity
public import BlockBand.Native.PSSS.BlockBand.Coarea.NonlinearEigenpairSmoothDerivative

/-!
# Deterministic unitary transport of the canonical coordinate GUE split

This module isolates the exact deterministic and density-preserving part of
unitary transport for the repository's canonical finite-product GUE law.  It
does not introduce the absent public `BlockBand.GUE` measure.

For every fixed unitary matrix, conjugation is packaged as a real-linear
equivalence on Hermitian matrices and, through the exact finite-coordinate
reconstruction equivalence, as a real-linear equivalence on GUE coordinates.
The map is measurable, preserves the Hilbert–Schmidt quadratic form and hence
the exact positive-variance GUE density, and transports the proved first-row /
compression independence to conjugated blocks.

The remaining law-level step is stated only in this documentation, not as an
assumption: one must prove that this coordinate equivalence preserves Lebesgue
volume (equivalently that its real determinant has absolute value one).  The
current library has Hilbert–Schmidt invariance but no compatible
Hilbert–Schmidt inner-product/isometry structure on the Hermitian coordinate
equivalence.  Until that Jacobian fact and an arbitrary-unit-vector completion
are available, equality of the conjugated canonical GUE pushforward law and the
original law is not claimed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- The canonical Hermitian GUE matrix law of variance `t`, as the pushforward of the
coordinate law. -/
def canonicalHermitianGUEPushforward (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Measure (HermitianMatrix (Fin N)) :=
  Measure.map (hermitianGUEBlock N)
    (hermitianGUECoordinateMeasure N t ht)

/-- Conjugation of a Hermitian matrix by a fixed unitary frame. -/
def conjugateHermitian {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (A : HermitianMatrix (Fin N)) : HermitianMatrix (Fin N) :=
  ⟨Uᴴ * A.1 * U, isHermitian_unitaryConjugation U A.1 A.2⟩

/-- Fixed-frame Hermitian conjugation is measurable. -/
theorem measurable_conjugateHermitian {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) :
    Measurable (conjugateHermitian U) := by
  unfold conjugateHermitian
  fun_prop

/-- Unitary conjugation restricted to the real Hermitian space. -/
def unitaryHermitianConjugationLinearEquiv {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    RealHermitianMatrix (Fin N) ≃ₗ[ℝ] RealHermitianMatrix (Fin N) :=
  realHermitianUnitaryConjugationLinearEquiv U hU

/-- The coordinate action induced by unitary conjugation. -/
def unitaryGUECoordinateLinearEquiv {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    HermitianCoordinateSpace N ≃ₗ[ℝ] HermitianCoordinateSpace N :=
  (hermitianFinCoordinatesLinearEquiv N).trans
    ((unitaryHermitianConjugationLinearEquiv U hU).trans
      (hermitianFinCoordinatesLinearEquiv N).symm)

/-- Reconstruction intertwines coordinate transport with matrix conjugation. -/
theorem hermitianGUEBlock_unitaryGUECoordinateLinearEquiv {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (x : HermitianCoordinateSpace N) :
    hermitianGUEBlock N (unitaryGUECoordinateLinearEquiv U hU x) =
      conjugateHermitian U (hermitianGUEBlock N x) := by
  change (hermitianFinCoordinatesLinearEquiv N)
      ((hermitianFinCoordinatesLinearEquiv N).symm
        ((realHermitianUnitaryConjugationLinearEquiv U hU)
          ((hermitianFinCoordinatesLinearEquiv N) x))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The induced coordinate change is measurable. -/
theorem measurable_unitaryGUECoordinateLinearEquiv {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    Measurable (unitaryGUECoordinateLinearEquiv U hU) := by
  exact (unitaryGUECoordinateLinearEquiv U hU).toLinearMap
    |>.continuous_of_finiteDimensional.measurable

/-- Matrix-law unitary invariance is exactly reduced to invariance of the
explicit coordinate product measure under the induced coordinate equivalence.
No law equality is assumed in this identity. -/
theorem map_conjugate_canonicalHermitianGUEPushforward {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    Measure.map (conjugateHermitian U)
        (canonicalHermitianGUEPushforward N t ht) =
      Measure.map (hermitianGUEBlock N)
        (Measure.map (unitaryGUECoordinateLinearEquiv U hU)
          (hermitianGUECoordinateMeasure N t ht)) := by
  unfold canonicalHermitianGUEPushforward
  rw [Measure.map_map (measurable_conjugateHermitian U)
    (measurable_hermitianGUEBlock N)]
  rw [Measure.map_map (measurable_hermitianGUEBlock N)
    (measurable_unitaryGUECoordinateLinearEquiv U hU)]
  congr 1
  funext x
  simpa only [Function.comp_apply] using
    (hermitianGUEBlock_unitaryGUECoordinateLinearEquiv U hU x).symm

/-- Fixed unitary conjugation preserves the exact Hilbert–Schmidt quadratic
form used in the canonical GUE density. -/
theorem hilbertSchmidtNormSq_conjugateHermitian {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (A : HermitianMatrix (Fin N)) :
    hilbertSchmidtNormSq (conjugateHermitian U A).1 =
      hilbertSchmidtNormSq A.1 := by
  change hilbertSchmidtNormSq (Uᴴ * A.1 * U) = _
  have h := hilbertSchmidtNormSq_unitary_conj Uᴴ A.1
    (by simpa using (mul_eq_one_comm.mp hU))
  simpa only [Matrix.conjTranspose_conjTranspose] using h

/-- The exact positive-variance GUE density is invariant under every fixed
unitary coordinate change.  This is density invariance; the separate Lebesgue
Jacobian-one statement is still needed for measure invariance. -/
theorem hermitianGUEDensity_unitaryGUECoordinateLinearEquiv {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (t : ℝ) (x : HermitianCoordinateSpace N) :
    hermitianGUEDensity N t
        (hermitianGUEBlock N (unitaryGUECoordinateLinearEquiv U hU x)) =
      hermitianGUEDensity N t (hermitianGUEBlock N x) := by
  rw [hermitianGUEBlock_unitaryGUECoordinateLinearEquiv]
  unfold hermitianGUEDensity
  rw [hilbertSchmidtNormSq_conjugateHermitian U hU]

/-- If a unitary frame sends the first coordinate vector to `φ`, conjugating a
matrix turns multiplication by `φ` into multiplication by the first coordinate,
up to the adjoint unitary.  This is the deterministic vector identity needed
before the Schur-complement reduction. -/
theorem conjugateHermitian_mulVec_firstCoordinate {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (A : HermitianMatrix (Fin N))
    (i : Fin N) (φ : Fin N → ℂ)
    (hφ : U *ᵥ phaseFixedCoordinateVector i = φ) :
    (conjugateHermitian U A).1 *ᵥ phaseFixedCoordinateVector i =
      Uᴴ *ᵥ (A.1 *ᵥ φ) := by
  change (Uᴴ * A.1 * U) *ᵥ phaseFixedCoordinateVector i =
    Uᴴ *ᵥ (A.1 *ᵥ φ)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hφ]

/-- Conjugated first-row reconstruction. -/
def conjugatedFirstRowGUEHermitian {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ)
    (u : FirstRowGUECoordinate N → ℝ) : HermitianMatrix (Fin N) :=
  conjugateHermitian U (firstRowGUEHermitian N u)

/-- Conjugated compression reconstruction. -/
def conjugatedCompressionGUEHermitian {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ)
    (u : CompressionGUECoordinate N → ℝ) : HermitianMatrix (Fin N) :=
  conjugateHermitian U (compressionGUEHermitian N u)

/-- Both conjugated reconstruction maps are measurable. -/
theorem measurable_conjugatedFirstRowGUEHermitian {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) :
    Measurable (conjugatedFirstRowGUEHermitian U) :=
  (measurable_conjugateHermitian U).comp
    (measurable_firstRowGUEHermitian N)

/-- Measurability of the conjugated compression reconstruction. -/
theorem measurable_conjugatedCompressionGUEHermitian {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) :
    Measurable (conjugatedCompressionGUEHermitian U) :=
  (measurable_conjugateHermitian U).comp
    (measurable_compressionGUEHermitian N)

/-- Conjugation transports the exact first-row/compression matrix sum. -/
theorem conjugatedFirstRow_add_conjugatedCompression {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ)
    (x : HermitianCoordinateSpace N) :
    (conjugatedFirstRowGUEHermitian U (firstRowGUECoordinates N x)).1 +
      (conjugatedCompressionGUEHermitian U
        (compressionGUECoordinates N x)).1 =
      (conjugateHermitian U (hermitianGUEBlock N x)).1 := by
  unfold conjugatedFirstRowGUEHermitian
    conjugatedCompressionGUEHermitian conjugateHermitian
  change Uᴴ *
      (firstRowGUEHermitian N (firstRowGUECoordinates N x)).1 * U +
    Uᴴ * (compressionGUEHermitian N
      (compressionGUECoordinates N x)).1 * U =
    Uᴴ * (hermitianGUEBlock N x).1 * U
  rw [← add_mul, ← mul_add,
    firstRowGUEHermitian_add_compressionGUEHermitian]

/-- The conjugated first-row block and conjugated compression remain
independent under the original canonical coordinate product law. -/
theorem indepFun_conjugatedFirstRow_compression_GUEHermitian
    {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (t : ℝ) (ht : 0 ≤ t) :
    IndepFun
      (fun x => conjugatedFirstRowGUEHermitian U
        (firstRowGUECoordinates N x))
      (fun x => conjugatedCompressionGUEHermitian U
        (compressionGUECoordinates N x))
      (hermitianGUECoordinateMeasure N t ht) := by
  simpa only [Function.comp_def] using
    (indepFun_firstRow_compression_GUECoordinates N t ht).comp
      (measurable_conjugatedFirstRowGUEHermitian U)
      (measurable_conjugatedCompressionGUEHermitian U)

/-- Exact joint-law product factorization of the two conjugated blocks. -/
theorem map_conjugatedFirstRow_compression_eq_prod
    {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (t : ℝ) (ht : 0 ≤ t) :
    Measure.map
        (fun x : HermitianCoordinateSpace N =>
          (conjugatedFirstRowGUEHermitian U (firstRowGUECoordinates N x),
            conjugatedCompressionGUEHermitian U
              (compressionGUECoordinates N x)))
        (hermitianGUECoordinateMeasure N t ht) =
      (Measure.map
          (fun x => conjugatedFirstRowGUEHermitian U
            (firstRowGUECoordinates N x))
          (hermitianGUECoordinateMeasure N t ht)).prod
        (Measure.map
          (fun x => conjugatedCompressionGUEHermitian U
            (compressionGUECoordinates N x))
          (hermitianGUECoordinateMeasure N t ht)) := by
  apply (indepFun_conjugatedFirstRow_compression_GUEHermitian U t ht).map_prod_eq_prod_map_map
  · exact (measurable_conjugatedFirstRowGUEHermitian U).comp
      (measurable_firstRowGUECoordinates N) |>.aemeasurable
  · exact (measurable_conjugatedCompressionGUEHermitian U).comp
      (measurable_compressionGUECoordinates N) |>.aemeasurable

end PSSSNative.BlockBand.PSSS
