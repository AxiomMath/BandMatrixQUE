module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.BlockGUELawTransport

/-!
# Public normalized-GUE block-product adapter

This module constructs the product of the public single-block `GUE`
laws, its block-diagonal assembly, and the exact coordinate readback into the
`BlockGUE.indexLE` convention.  The readback automatically handles the fact
that the sigma-index upper ordering may reverse the standard `Fin d` strict
upper ordering: it reads the assembled Hermitian entry in the chosen sigma
orientation, so its imaginary component acquires precisely the required sign.

The final identities are deterministic and measure-theoretic map adapters.
The probabilistic content reduces to the equality of two explicit finite
product measures.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BlockGUE

/-- One public Hermitian GUE matrix for every block. -/
abbrev PublicBlockSample {k : ℕ} (d : Fin k → ℕ) :=
  ∀ j, HermitianMatrix (Fin (d j))

/-- Independent product of the public normalized GUE laws
`GUE_{d_j}(1/d_j)`. -/
def publicBlockProductMeasure {k : ℕ} (d : Fin k → ℕ)
    (_hd : ∀ j, 0 < d j) : Measure (PublicBlockSample d) :=
  Measure.pi fun j =>
    (GUE (d j) (1 / (d j : ℝ)) : Measure (HermitianMatrix (Fin (d j))))

instance publicBlockProductMeasure.instIsProbabilityMeasure {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) :
    IsProbabilityMeasure (publicBlockProductMeasure d hd) := by
  unfold publicBlockProductMeasure
  infer_instance

/-- Evaluation of one Hermitian-matrix entry is measurable. -/
theorem measurable_hermitianMatrix_entry {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (x y : ι) :
    Measurable (fun H : HermitianMatrix ι => H.1 x y) := by
  have hc : Measurable (fun H : HermitianMatrix ι => H.1) :=
    measurable_subtype_coe
  have hx : Measurable (fun H : HermitianMatrix ι => H.1 x) :=
    (measurable_pi_apply x).comp hc
  exact (measurable_pi_apply y).comp hx

/-- Raw block-diagonal assembly on the sigma index. -/
def publicBlockDiagonalRaw {k : ℕ} {d : Fin k → ℕ}
    (H : PublicBlockSample d) : Matrix (Index d) (Index d) ℂ :=
  fun x y => if h : x.1 = y.1 then (H x.1).1 x.2 (h ▸ y.2) else 0

/-- Public block-diagonal assembly is Hermitian. -/
theorem publicBlockDiagonalRaw_isHermitian {k : ℕ} {d : Fin k → ℕ}
    (H : PublicBlockSample d) : (publicBlockDiagonalRaw H).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  by_cases h : x.1 = y.1
  · rcases x with ⟨j, x⟩
    rcases y with ⟨j', y⟩
    simp only at h
    subst j'
    simpa [publicBlockDiagonalRaw, Matrix.conjTranspose_apply] using
      congrFun (congrFun (H j).property x) y
  · have h' : y.1 ≠ x.1 := Ne.symm h
    simp [publicBlockDiagonalRaw, Matrix.conjTranspose_apply, h, h']

/-- Assemble the public block samples into one Hermitian sigma-index matrix. -/
def publicBlockDiagonal {k : ℕ} {d : Fin k → ℕ}
    (H : PublicBlockSample d) : HermitianMatrix (Index d) :=
  ⟨publicBlockDiagonalRaw H, publicBlockDiagonalRaw_isHermitian H⟩

/-- Block-diagonal assembly is measurable. -/
theorem measurable_publicBlockDiagonal {k : ℕ} (d : Fin k → ℕ) :
    Measurable (@publicBlockDiagonal k d) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro x y
  unfold publicBlockDiagonalRaw
  split_ifs with h
  · exact (measurable_hermitianMatrix_entry x.2 (h ▸ y.2)).comp
      (measurable_pi_apply x.1)
  · exact measurable_const

/-- The public normalized block-GUE matrix law. -/
def publicBlockProductMatrixMeasure {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) : Measure (HermitianMatrix (Index d)) :=
  Measure.map publicBlockDiagonal (publicBlockProductMeasure d hd)

/-- Read the public block assembly in the exact `BlockGUE.indexLE` upper
orientation.  This is the explicit ordering adapter. -/
def publicBlockUpperCoordinates {k : ℕ} {d : Fin k → ℕ}
    (H : PublicBlockSample d) (q : UpperPair d) : UpperRealPair :=
  (((publicBlockDiagonal H).1 q.1.1 q.1.2).re,
    ((publicBlockDiagonal H).1 q.1.1 q.1.2).im)

/-- The explicit public-to-sigma upper-coordinate adapter is measurable. -/
theorem measurable_publicBlockUpperCoordinates {k : ℕ} (d : Fin k → ℕ) :
    Measurable (@publicBlockUpperCoordinates k d) := by
  rw [measurable_pi_iff]
  intro q
  have he : Measurable (fun H : PublicBlockSample d =>
      (publicBlockDiagonal H).1 q.1.1 q.1.2) :=
    (measurable_hermitianMatrix_entry q.1.1 q.1.2).comp
      (measurable_publicBlockDiagonal d)
  exact (Complex.measurable_re.comp he).prodMk
    (Complex.measurable_im.comp he)

/-- Reading and reconstructing in the sigma upper ordering returns the public
block-diagonal matrix pointwise. -/
theorem matrixOfUpperCoordinates_publicBlockUpperCoordinates {k : ℕ}
    {d : Fin k → ℕ} (H : PublicBlockSample d) :
    matrixOfUpperCoordinates d (publicBlockUpperCoordinates H) =
      publicBlockDiagonal H := by
  apply Subtype.ext
  ext x y
  by_cases hxy : x = y
  · subst y
    change matrixOfUpperCoordinatesRaw d (publicBlockUpperCoordinates H) x x =
      (publicBlockDiagonal H).1 x x
    rw [show matrixOfUpperCoordinatesRaw d (publicBlockUpperCoordinates H) x x =
        (((publicBlockDiagonal H).1 x x).re : ℂ) by
      simp [matrixOfUpperCoordinatesRaw, publicBlockUpperCoordinates]]
    exact (publicBlockDiagonal H).property.coe_re_apply_self x
  · by_cases hle : indexLE d x y
    · change matrixOfUpperCoordinatesRaw d (publicBlockUpperCoordinates H) x y =
        (publicBlockDiagonal H).1 x y
      simp [matrixOfUpperCoordinatesRaw, publicBlockUpperCoordinates,
        complexOfUpperRealPair, hxy, hle]
    · have hherm := congrFun
        (congrFun (publicBlockDiagonal H).property y) x
      simp only [Matrix.conjTranspose_apply] at hherm
      change matrixOfUpperCoordinatesRaw d (publicBlockUpperCoordinates H) x y =
        (publicBlockDiagonal H).1 x y
      simp [matrixOfUpperCoordinatesRaw, publicBlockUpperCoordinates,
        complexOfUpperRealPair, hxy, hle, ← hherm]

/-- The public block-product matrix law factors exactly through the explicit
sigma-order coordinate adapter. -/
theorem publicBlockProductMatrixMeasure_eq_map_upperCoordinates {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) :
    publicBlockProductMatrixMeasure d hd =
      Measure.map (matrixOfUpperCoordinates d)
        (Measure.map publicBlockUpperCoordinates
          (publicBlockProductMeasure d hd)) := by
  unfold publicBlockProductMatrixMeasure
  rw [Measure.map_map (measurable_matrixOfUpperCoordinates d)
    (measurable_publicBlockUpperCoordinates d)]
  apply Measure.map_congr
  filter_upwards with H
  exact (matrixOfUpperCoordinates_publicBlockUpperCoordinates H).symm

/-- Deterministic deformation of the public block-product law. -/
def publicDeformedBlockProductMeasure {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) (A₀ : HermitianMatrix (Index d)) :
    Measure (HermitianMatrix (Index d)) :=
  Measure.map (fun H : HermitianMatrix (Index d) =>
    (⟨A₀.1 + H.1, A₀.2.add H.2⟩ : HermitianMatrix (Index d)))
    (publicBlockProductMatrixMeasure d hd)

/-- Deformation commutes with public block-diagonal assembly. -/
theorem publicDeformedBlockProductMeasure_eq_map_assembly {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 0 < d j)
    (A₀ : HermitianMatrix (Index d)) :
    publicDeformedBlockProductMeasure d hd A₀ =
      Measure.map (fun H : PublicBlockSample d =>
        (⟨A₀.1 + (publicBlockDiagonal H).1,
          A₀.2.add (publicBlockDiagonal H).2⟩ : HermitianMatrix (Index d)))
        (publicBlockProductMeasure d hd) := by
  unfold publicDeformedBlockProductMeasure publicBlockProductMatrixMeasure
  rw [Measure.map_map (by fun_prop) (measurable_publicBlockDiagonal d)]
  rfl

end BlockGUE
end PSSSNative.BlockBand
