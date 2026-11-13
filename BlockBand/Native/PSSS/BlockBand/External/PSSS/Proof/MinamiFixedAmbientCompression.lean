module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiMovingCountMeasurability
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECompressionProjection
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.RankOneCompression
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCanonicalSchurMeasurability

/-!
# Ambient compression along a selected-block direction

A unit direction in one block is extended by zero to the full block index, and the full public
deformation is reconstructed from its exterior sample and a selected matrix argument. The file
defines the compression of this reconstructed deformation along the extended direction.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- Embed a selected-block direction into the full public sigma index, with
zero coordinates on every other block. -/
def selectedAmbientDirection {k : ℕ} {dims : Fin k → ℕ} (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) :
    EuclideanSpace ℂ (BlockGUE.Index dims) :=
  WithLp.toLp 2 (fun x => if h : x.1 = j then WithLp.ofLp φ (h ▸ x.2) else 0)

/-- The ambient direction agrees with the original direction on the selected
fiber. -/
@[simp] theorem selectedAmbientDirection_apply_selected
    {k : ℕ} {dims : Fin k → ℕ} (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) (a : Fin (dims j)) :
    WithLp.ofLp (selectedAmbientDirection j φ) ⟨j, a⟩ = WithLp.ofLp φ a := by
  simp [selectedAmbientDirection]

/-- Extension by zero preserves the selected direction's Euclidean norm. -/
@[simp] theorem norm_selectedAmbientDirection
    {k : ℕ} {dims : Fin k → ℕ} (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) :
    ‖selectedAmbientDirection j φ‖ = ‖φ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp [selectedAmbientDirection]
  · intro i _ hij
    simp [selectedAmbientDirection, hij]
  · simp

/-- Totalized singleton selected sample reconstructed from an arbitrary matrix
argument.  On projected Hermitian inputs the Hermitian-part operation is the
identity. -/
def selectedSampleOfMatrix {k : ℕ} {dims : Fin k → ℕ} (j : Fin k)
    (X : Matrix (Fin (dims j)) (Fin (dims j)) ℂ) :
    BlockProductDisintegration.SelectedSample dims j := fun q =>
  let h : q.1 = j := not_ne_iff.mp q.2
  h.symm ▸
    (⟨PSSSNative.BlockBand.matrixHermitianPart X,
      PSSSNative.BlockBand.matrixHermitianPart_isHermitian X⟩ :
      HermitianMatrix (Fin (dims j)))

/-- Reconstruct the full public deformation from its exterior sample and the
selected matrix argument. -/
def reconstructedFullDeformation {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (X : Matrix (Fin (dims j)) (Fin (dims j)) ℂ) :
    HermitianMatrix (BlockGUE.Index dims) :=
  publicBlockDeformation A₀
    ((BlockProductDisintegration.split dims j).symm
      (Gext, selectedSampleOfMatrix j X))

/-- The ambient compression, along the selected direction `φ`, of the full deformation
reconstructed from the exterior sample and the selected matrix `X`. -/
def reconstructedFullCompression {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j)))
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (X : Matrix (Fin (dims j)) (Fin (dims j)) ℂ) :
    HermitianMatrix (BlockGUE.Index dims) :=
  compressHermitian (reconstructedFullDeformation A₀ j Gext X)
    (selectedAmbientDirection j φ)

/-- The projection `Pφ V Pφ` of a Hermitian matrix is its own Hermitian part. -/
theorem matrixHermitianPart_orthProj_mul_hermitian_mul_orthProj
    {N : ℕ} (φ : EuclideanSpace ℂ (Fin N)) (V : HermitianMatrix (Fin N)) :
    PSSSNative.BlockBand.matrixHermitianPart
      (orthProj φ * V.1 * orthProj φ) = orthProj φ * V.1 * orthProj φ := by
  let P := orthProj φ
  have hP : Pᴴ = P := orthogonalProjector_conjTranspose φ
  have hraw : (P * V.1 * P).IsHermitian := by
    rw [Matrix.IsHermitian]
    simp only [Matrix.conjTranspose_mul, hP, V.2.eq]
    noncomm_ring
  rw [PSSSNative.BlockBand.matrixHermitianPart]
  rw [show (P * V.1 * P)ᴴ = P * V.1 * P from hraw.eq]
  ext x y
  simp
  ring

end PSSSNative.BlockBand.PSSS
