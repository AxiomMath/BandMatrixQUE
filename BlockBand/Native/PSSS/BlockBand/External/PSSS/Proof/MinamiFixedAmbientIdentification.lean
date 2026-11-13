module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedAmbientCompression

/-!
# Identification of the fixed-target ambient compression

This module proves the algebraic bridge required by PSSS formula (2.13)
of arXiv:1608.02922.  Replacing the selected public GUE block by
its projection away from the selected sphere direction does not change the
full ambient compression.  This concerns the fixed target count only; the
auxiliary radial count remains on `Ioo (-xi) xi` in later modules.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- Embed a selected-block matrix as a matrix on the full public sigma index,
with zero entries off the selected diagonal block. -/
def selectedAmbientMatrix {k : ℕ} {dims : Fin k → ℕ} (j : Fin k)
    (X : Matrix (Fin (dims j)) (Fin (dims j)) ℂ) :
    Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ := fun x y =>
  if hx : x.1 = j then
    if hy : y.1 = j then X (hx ▸ x.2) (hy ▸ y.2) else 0
  else 0

/-- Multiplication by the ambient projector on both sides is multiplication by
`orthProj` on the embedded selected block. -/
theorem orthogonalProjector_mul_selectedAmbientMatrix_mul
    {k : ℕ} {dims : Fin k → ℕ} (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j)))
    (X : Matrix (Fin (dims j)) (Fin (dims j)) ℂ) :
    orthogonalProjector (selectedAmbientDirection j φ) *
        selectedAmbientMatrix j X *
        orthogonalProjector (selectedAmbientDirection j φ) =
      selectedAmbientMatrix j (orthProj φ * X * orthProj φ) := by
  classical
  ext ⟨i, x⟩ ⟨l, y⟩
  by_cases hi : i = j
  · subst i
    by_cases hl : l = j
    · subst l
      simp [Matrix.mul_apply, selectedAmbientMatrix, Fintype.sum_sigma,
        orthogonalProjector, orthProj, selectedAmbientDirection,
        Matrix.vecMulVec_apply, Matrix.one_apply]
    · simp [Matrix.mul_apply, selectedAmbientMatrix, Fintype.sum_sigma,
        orthogonalProjector, selectedAmbientDirection,
        Matrix.vecMulVec_apply, Matrix.one_apply, hl]
  · simp [Matrix.mul_apply, selectedAmbientMatrix, Fintype.sum_sigma,
      orthogonalProjector, selectedAmbientDirection,
      Matrix.vecMulVec_apply, Matrix.one_apply, hi]

/-- On a projected Hermitian selected block, reconstruction changes
the full public deformation by precisely the selected-block difference. -/
theorem reconstructedFullDeformation_projected_eq_add_selectedDifference
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j)))
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j) :
    (reconstructedFullDeformation A₀ j Gext
      (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)).1 =
      (publicBlockDeformation A₀
        ((BlockProductDisintegration.split dims j).symm (Gext, Gj))).1 +
      selectedAmbientMatrix j
        (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ -
          (Gj ⟨j, by simp⟩).1) := by
  classical
  ext ⟨i, x⟩ ⟨l, y⟩
  by_cases hil : i = l
  · subst l
    by_cases hij : i = j
    · subst i
      simp [reconstructedFullDeformation, publicBlockDeformation,
        BlockGUE.publicBlockDiagonal, BlockGUE.publicBlockDiagonalRaw,
        selectedAmbientMatrix, split_symm_apply_selected,
        selectedSampleOfMatrix,
        matrixHermitianPart_orthProj_mul_hermitian_mul_orthProj]
    · let q : {i : Fin k // i ≠ j} := ⟨i, hij⟩
      have hnew := split_symm_apply_exterior dims j Gext
        (selectedSampleOfMatrix j
          (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ)) q
      have hold := split_symm_apply_exterior dims j Gext Gj q
      simp [reconstructedFullDeformation, publicBlockDeformation,
        BlockGUE.publicBlockDiagonal, BlockGUE.publicBlockDiagonalRaw,
        selectedAmbientMatrix, hij, hnew, hold, q]
  · by_cases hij : i = j
    · subst i
      have hlj : l ≠ j := by
        intro h
        subst l
        exact hil rfl
      simp [reconstructedFullDeformation, publicBlockDeformation,
        BlockGUE.publicBlockDiagonal, BlockGUE.publicBlockDiagonalRaw,
        selectedAmbientMatrix, hil, hlj]
    · simp [reconstructedFullDeformation, publicBlockDeformation,
        BlockGUE.publicBlockDiagonal, BlockGUE.publicBlockDiagonalRaw,
        selectedAmbientMatrix, hil, hij]

/-- For a unit direction, the selected orthogonal projector is idempotent. -/
theorem orthProj_mul_self_of_norm_eq_one {N : ℕ}
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    orthProj φ * orthProj φ = orthProj φ := by
  have hsum : ∑ i, ‖WithLp.ofLp φ i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hφ]
    norm_num
  have hsumC :
      ∑ i, star (WithLp.ofLp φ i) * WithLp.ofLp φ i = (1 : ℂ) := by
    change (∑ i, (starRingEnd ℂ) (WithLp.ofLp φ i) *
      WithLp.ofLp φ i) = (1 : ℂ)
    simp_rw [Complex.conj_mul']
    exact_mod_cast hsum
  ext i j
  simp only [orthProj, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.vecMulVec_apply]
  simp only [sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  simp
  calc
    WithLp.ofLp φ i * star (WithLp.ofLp φ j) -
        ∑ x, WithLp.ofLp φ i * star (WithLp.ofLp φ x) *
          (WithLp.ofLp φ x * star (WithLp.ofLp φ j)) =
      WithLp.ofLp φ i * star (WithLp.ofLp φ j) -
        WithLp.ofLp φ i *
          (∑ x, star (WithLp.ofLp φ x) * WithLp.ofLp φ x) *
            star (WithLp.ofLp φ j) := by
              congr 1
              rw [Finset.mul_sum, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro x _
              ring
    _ = 0 := by rw [hsumC]; ring

/-- **Algebraic bridge for PSSS (2.13).**  On a unit selected
direction, rebuilding the full ambient compression from the fixed exterior
and the projected selected GUE block gives exactly the compression of the
public block deformation. -/
theorem reconstructedFullCompression_projected_eq_compressHermitian
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (φ : EuclideanSpace ℂ (Fin (dims j))) (hφ : ‖φ‖ = 1)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j) :
    reconstructedFullCompression A₀ j φ Gext
        (orthProj φ * (Gj ⟨j, by simp⟩).1 * orthProj φ) =
      compressHermitian
        (publicBlockDeformation A₀
          ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
        (selectedAmbientDirection j φ) := by
  let V := (Gj ⟨j, by simp⟩).1
  let P := orthProj φ
  let u := selectedAmbientDirection j φ
  let K := publicBlockDeformation A₀
    ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
  have hPP : P * P = P := orthProj_mul_self_of_norm_eq_one φ hφ
  have hselected : P * (P * V * P - V) * P = 0 := by
    calc
      P * (P * V * P - V) * P =
          (P * P) * V * (P * P) - P * V * P := by noncomm_ring
      _ = 0 := by rw [hPP]; abel
  have hambient :
      orthogonalProjector u *
          selectedAmbientMatrix j (P * V * P - V) *
          orthogonalProjector u = 0 := by
    rw [orthogonalProjector_mul_selectedAmbientMatrix_mul]
    rw [hselected]
    ext x y
    simp [selectedAmbientMatrix]
  apply Subtype.ext
  simp only [reconstructedFullCompression, compressHermitian,
    orthogonalCompression_coe]
  change orthogonalProjector u *
      (reconstructedFullDeformation A₀ j Gext (P * V * P)).1 *
        (orthogonalProjector u)ᴴ =
    orthogonalProjector u * K.1 * (orthogonalProjector u)ᴴ
  rw [reconstructedFullDeformation_projected_eq_add_selectedDifference]
  rw [orthogonalProjector_conjTranspose]
  rw [Matrix.mul_add, Matrix.add_mul, hambient, add_zero]

end PSSSNative.BlockBand.PSSS
