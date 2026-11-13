module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.ArbitraryQTransport
public import BlockBand.Native.PSSS.BlockBand.Coarea.PhysicalHermitianGaussianSplit
public import Mathlib.Probability.Independence.Basic

/-!
# First-row/compression split for the canonical finite-product GUE law

This module isolates the measure-theoretic input needed for the fixed-vector
inverse tail estimate.  It works with the normalized GUE
construction `GUE`: independent real Hermitian coordinates, with diagonal variance
`t` and real and imaginary strict-upper variances `t/2`.

The first-row coordinate tuple and its complementary tuple are proved
independent, their joint pushforward is proved to factor as the product of its
marginals, and their zero-filled Hermitian reconstructions sum pointwise to the
original GUE matrix.  No fixed-vector tail estimate is proved here: it would also
need the rotation of an arbitrary fixed vector to the first basis vector, i.e. the
unitary invariance of the `BlockBand.GUE` matrix measure.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- A finite Hermitian coordinate belongs to the first row when it is the
first diagonal coordinate or the real/imaginary part of a strict-upper entry
whose first endpoint is zero. -/
def IsFirstRowGUECoordinate (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N))) : Prop :=
  match (hermitianCoordinateEquivFin N).symm k with
  | .inl i => i.val = 0
  | .inr (.inl ij) => ij.1.1.val = 0
  | .inr (.inr ij) => ij.1.1.val = 0

instance (N : ℕ) (k : Fin (Fintype.card (HermitianCoordinate N))) :
    Decidable (IsFirstRowGUECoordinate N k) := by
  unfold IsFirstRowGUECoordinate
  split <;> infer_instance

/-- Indices of the first diagonal coordinate and first-row strict-upper real
and imaginary coordinates. -/
abbrev FirstRowGUECoordinate (N : ℕ) :=
  ↥(Finset.univ.filter (IsFirstRowGUECoordinate N))

/-- All Hermitian coordinates not belonging to the first row. -/
abbrev CompressionGUECoordinate (N : ℕ) :=
  ↥(Finset.univ.filter (fun k => ¬ IsFirstRowGUECoordinate N k))

/-- Restriction of the full real-coordinate tuple to the first row. -/
def firstRowGUECoordinates (N : ℕ) (x : HermitianCoordinateSpace N) :
    FirstRowGUECoordinate N → ℝ := fun k => x k.1

/-- Restriction of the full real-coordinate tuple to the complementary
principal compression. -/
def compressionGUECoordinates (N : ℕ) (x : HermitianCoordinateSpace N) :
    CompressionGUECoordinate N → ℝ := fun k => x k.1

/-- The first-row restriction map is Borel measurable. -/
theorem measurable_firstRowGUECoordinates (N : ℕ) :
    Measurable (firstRowGUECoordinates N) := by
  unfold firstRowGUECoordinates
  exact measurable_pi_iff.mpr fun k => measurable_pi_apply k.1

/-- The compression restriction map is Borel measurable. -/
theorem measurable_compressionGUECoordinates (N : ℕ) :
    Measurable (compressionGUECoordinates N) := by
  unfold compressionGUECoordinates
  exact measurable_pi_iff.mpr fun k => measurable_pi_apply k.1

/-- Under the explicit finite-product Hermitian GUE law, the full first-row
real coordinate tuple is independent of the full complementary tuple. -/
theorem indepFun_firstRow_compression_GUECoordinates
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    IndepFun (firstRowGUECoordinates N) (compressionGUECoordinates N)
      (hermitianGUECoordinateMeasure N t ht) := by
  classical
  change IndepFun
    (fun x (k : ↥(Finset.univ.filter (IsFirstRowGUECoordinate N))) => x k.1)
    (fun x (k : ↥(Finset.univ.filter
      (fun k => ¬ IsFirstRowGUECoordinate N k))) => x k.1)
    (hermitianGUECoordinateMeasure N t ht)
  apply iIndepFun.indepFun_finset
      (f := fun k (x : HermitianCoordinateSpace N) => x k)
      (μ := hermitianGUECoordinateMeasure N t ht)
      (Finset.univ.filter (IsFirstRowGUECoordinate N))
      (Finset.univ.filter (fun k => ¬ IsFirstRowGUECoordinate N k))
  · rw [Finset.disjoint_left]
    intro k hkS hkT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkS hkT
    exact hkT hkS
  · exact iIndepFun_hermitianGUECoordinates N t ht
  · exact fun _ => measurable_pi_apply _

/-- Zero-fill a first-row tuple into the full finite Hermitian coordinate
space. -/
def extendFirstRowGUECoordinates (N : ℕ)
    (u : FirstRowGUECoordinate N → ℝ) : HermitianCoordinateSpace N :=
  fun k => if h : IsFirstRowGUECoordinate N k then
    u ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩⟩ else 0

/-- Zero-fill a complementary tuple into the full finite Hermitian coordinate
space. -/
def extendCompressionGUECoordinates (N : ℕ)
    (u : CompressionGUECoordinate N → ℝ) : HermitianCoordinateSpace N :=
  fun k => if h : ¬ IsFirstRowGUECoordinate N k then
    u ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩⟩ else 0

/-- First-row zero filling is measurable. -/
theorem measurable_extendFirstRowGUECoordinates (N : ℕ) :
    Measurable (extendFirstRowGUECoordinates N) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases h : IsFirstRowGUECoordinate N k
  · simp only [extendFirstRowGUECoordinates, dite_eq_left h]
    exact measurable_pi_apply _
  · simp only [extendFirstRowGUECoordinates, dite_eq_right h]
    exact measurable_const

/-- Compression zero filling is measurable. -/
theorem measurable_extendCompressionGUECoordinates (N : ℕ) :
    Measurable (extendCompressionGUECoordinates N) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases h : ¬ IsFirstRowGUECoordinate N k
  · simp only [extendCompressionGUECoordinates, dite_eq_left h]
    exact measurable_pi_apply _
  · simp only [extendCompressionGUECoordinates, dite_eq_right h]
    exact measurable_const

/-- The two restricted tuples reconstruct every full real coordinate exactly. -/
theorem extendFirstRow_add_extendCompression (N : ℕ)
    (x : HermitianCoordinateSpace N) :
    extendFirstRowGUECoordinates N (firstRowGUECoordinates N x) +
      extendCompressionGUECoordinates N (compressionGUECoordinates N x) = x := by
  funext k
  by_cases h : IsFirstRowGUECoordinate N k
  · simp [extendFirstRowGUECoordinates, extendCompressionGUECoordinates,
      firstRowGUECoordinates, h]
  · simp [extendFirstRowGUECoordinates, extendCompressionGUECoordinates,
      compressionGUECoordinates, h]

/-- Hermitian reconstruction of the first row with the compression set to
zero. -/
def firstRowGUEHermitian (N : ℕ) (u : FirstRowGUECoordinate N → ℝ) :
    HermitianMatrix (Fin N) :=
  hermitianGUEBlock N (extendFirstRowGUECoordinates N u)

/-- Hermitian reconstruction of the complementary principal compression with
the first row and column set to zero. -/
def compressionGUEHermitian (N : ℕ)
    (u : CompressionGUECoordinate N → ℝ) : HermitianMatrix (Fin N) :=
  hermitianGUEBlock N (extendCompressionGUECoordinates N u)

/-- First-row Hermitian reconstruction is measurable. -/
theorem measurable_firstRowGUEHermitian (N : ℕ) :
    Measurable (firstRowGUEHermitian N) := by
  exact (measurable_hermitianGUEBlock N).comp
    (measurable_extendFirstRowGUECoordinates N)

/-- Compression Hermitian reconstruction is measurable. -/
theorem measurable_compressionGUEHermitian (N : ℕ) :
    Measurable (compressionGUEHermitian N) := by
  exact (measurable_hermitianGUEBlock N).comp
    (measurable_extendCompressionGUECoordinates N)

/-- The reconstructed first-row matrix and compression matrix sum to the
original explicit GUE matrix. -/
theorem firstRowGUEHermitian_add_compressionGUEHermitian
    (N : ℕ) (x : HermitianCoordinateSpace N) :
    (firstRowGUEHermitian N (firstRowGUECoordinates N x)).1 +
      (compressionGUEHermitian N (compressionGUECoordinates N x)).1 =
      (hermitianGUEBlock N x).1 := by
  change hermitianMatrixOfCoordinates
      ((extendFirstRowGUECoordinates N (firstRowGUECoordinates N x)) ∘
        hermitianCoordinateEquivFin N) +
    hermitianMatrixOfCoordinates
      ((extendCompressionGUECoordinates N (compressionGUECoordinates N x)) ∘
        hermitianCoordinateEquivFin N) =
    hermitianMatrixOfCoordinates (x ∘ hermitianCoordinateEquivFin N)
  change (hermitianCoordinatesLinearMap N)
      ((extendFirstRowGUECoordinates N (firstRowGUECoordinates N x)) ∘
        hermitianCoordinateEquivFin N) +
    (hermitianCoordinatesLinearMap N)
      ((extendCompressionGUECoordinates N (compressionGUECoordinates N x)) ∘
        hermitianCoordinateEquivFin N) =
    (hermitianCoordinatesLinearMap N) (x ∘ hermitianCoordinateEquivFin N)
  rw [← map_add]
  congr 1
  funext c
  exact congrFun (extendFirstRow_add_extendCompression N x)
    (hermitianCoordinateEquivFin N c)

end PSSSNative.BlockBand.PSSS
