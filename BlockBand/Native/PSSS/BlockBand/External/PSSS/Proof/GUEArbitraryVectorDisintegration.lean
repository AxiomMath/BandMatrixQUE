module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEUnitaryJacobian
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Arbitrary-vector unitary completion and canonical GUE disintegration

This module completes a unit vector to an orthonormal frame, turns that frame
into an explicit unitary matrix whose zeroth column is the vector, and combines
fixed-unitary invariance with the canonical first-row/compression product split.
The construction requires `0 < N`; a unit vector cannot exist when `N = 0`.
The same construction includes `N = 1`, where the completed frame has its
single prescribed column.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- The Euclidean `ℓ²` interpretation of a complex coordinate vector. -/
def complexEuclideanVector {N : ℕ} (φ : Fin N → ℂ) :
    EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 φ

/-- A unit vector in positive dimension extends to an orthonormal basis whose
zeroth vector is the prescribed vector.  This also covers `N = 1` without a
separate noncanonical choice. -/
theorem exists_orthonormalBasis_zero_eq_unitVector {N : ℕ} (hN : 0 < N)
    (φ : Fin N → ℂ) (hφ : ‖complexEuclideanVector φ‖ = 1) :
    ∃ b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)),
      b ⟨0, hN⟩ = complexEuclideanVector φ := by
  let i₀ : Fin N := ⟨0, hN⟩
  let v : Fin N → EuclideanSpace ℂ (Fin N) := fun _ => complexEuclideanVector φ
  have hv : Orthonormal ℂ (({i₀} : Set (Fin N)).domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    simpa [v] using hφ
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin N) (by simp)
  refine ⟨b, ?_⟩
  simpa [i₀, v] using hb i₀ (Set.mem_singleton i₀)

/-- Matrix whose `j`th column is the `j`th vector of an orthonormal basis. -/
def orthonormalBasisMatrix {N : ℕ}
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    Matrix (Fin N) (Fin N) ℂ := fun i j => (b j).ofLp i

/-- The column matrix of an orthonormal basis is unitary. -/
theorem orthonormalBasisMatrix_unitary {N : ℕ}
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    (orthonormalBasisMatrix b)ᴴ * orthonormalBasisMatrix b = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ k, star ((b i).ofLp k) * (b j).ofLp k) =
    if i = j then 1 else 0
  calc
    ∑ k, star ((b i).ofLp k) * (b j).ofLp k =
        ∑ k, inner ℂ ((b i).ofLp k) ((b j).ofLp k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (RCLike.inner_apply' _ _).symm
    _ = _ := by rw [← PiLp.inner_apply, b.inner_eq_ite i j]

/-- Multiplication by the column matrix sends a coordinate vector to the
corresponding orthonormal-basis vector. -/
theorem orthonormalBasisMatrix_mulVec_coordinate {N : ℕ}
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    orthonormalBasisMatrix b *ᵥ phaseFixedCoordinateVector i = (b i).ofLp := by
  rw [phaseFixedCoordinateVector, Matrix.mulVec_single_one]
  rfl

/-- Every unit vector in positive dimension is the zeroth column of an
explicit unitary matrix. -/
theorem exists_unitaryMatrix_mulVec_zero_eq_unitVector {N : ℕ} (hN : 0 < N)
    (φ : Fin N → ℂ) (hφ : ‖complexEuclideanVector φ‖ = 1) :
    ∃ U : Matrix (Fin N) (Fin N) ℂ,
      Uᴴ * U = 1 ∧ U *ᵥ phaseFixedCoordinateVector ⟨0, hN⟩ = φ := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_zero_eq_unitVector hN φ hφ
  refine ⟨orthonormalBasisMatrix b, orthonormalBasisMatrix_unitary b, ?_⟩
  rw [orthonormalBasisMatrix_mulVec_coordinate]
  exact congrArg WithLp.ofLp hb

/-- Exact arbitrary-unit-vector package needed by the Schur-complement step:
there is a unitary frame with zeroth column `φ`; conjugation preserves the
canonical GUE matrix law; and the conjugated first-row and compression blocks
have the product joint law and reconstruct the conjugated matrix.
No disintegration or law equivalence is assumed. -/
theorem exists_arbitraryUnitVector_GUE_disintegration {N : ℕ} (hN : 0 < N)
    (φ : Fin N → ℂ) (hφ : ‖complexEuclideanVector φ‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ U : Matrix (Fin N) (Fin N) ℂ,
      Uᴴ * U = 1 ∧
      U *ᵥ phaseFixedCoordinateVector ⟨0, hN⟩ = φ ∧
      Measure.map (conjugateHermitian U)
          (canonicalHermitianGUEPushforward N t ht) =
        canonicalHermitianGUEPushforward N t ht ∧
      (∀ A : HermitianMatrix (Fin N),
        (conjugateHermitian U A).1 *ᵥ
            phaseFixedCoordinateVector ⟨0, hN⟩ =
          Uᴴ *ᵥ (A.1 *ᵥ φ)) ∧
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
            (hermitianGUECoordinateMeasure N t ht)) ∧
      ∀ x : HermitianCoordinateSpace N,
        (conjugatedFirstRowGUEHermitian U (firstRowGUECoordinates N x)).1 +
          (conjugatedCompressionGUEHermitian U
            (compressionGUECoordinates N x)).1 =
          (conjugateHermitian U (hermitianGUEBlock N x)).1 := by
  obtain ⟨U, hU, hUφ⟩ :=
    exists_unitaryMatrix_mulVec_zero_eq_unitVector hN φ hφ
  refine ⟨U, hU, hUφ,
    map_conjugate_canonicalHermitianGUEPushforward_invariant U hU t ht,
    ?_, map_conjugatedFirstRow_compression_eq_prod U t ht, ?_⟩
  · intro A
    exact conjugateHermitian_mulVec_firstCoordinate U A ⟨0, hN⟩ φ hUφ
  exact conjugatedFirstRow_add_conjugatedCompression U

end PSSSNative.BlockBand.PSSS
