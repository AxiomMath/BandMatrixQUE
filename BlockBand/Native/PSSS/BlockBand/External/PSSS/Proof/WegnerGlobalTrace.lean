module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerFrozenSchurAverage

/-!
# Global public-block conditioning for the Wegner estimate

Fixing the exterior sample of one block and reordering indices so that the selected block comes
first, the public block deformation becomes a fixed matrix plus the selected GUE block in the
upper-left corner. The negative imaginary part of the full regulated resolvent trace is the sum
over blocks of the corresponding selected-block traces.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The zero sample of the selected block `j`. -/
def zeroSelectedSample {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :
    BlockProductDisintegration.SelectedSample dims j :=
  fun _ => ⟨0, Matrix.isHermitian_zero⟩

/-- Recombine a fixed exterior sample with the zero selected block. -/
def frozenExteriorPublicSample {k : ℕ} (dims : Fin k → ℕ) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j) :
    BlockGUE.PublicBlockSample dims :=
  (BlockProductDisintegration.split dims j).symm
    (Gext, zeroSelectedSample dims j)

/-- Reindexed public deformation at a fixed exterior sample. -/
def frozenExteriorReindexed {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j) :
    Matrix (Fin (dims j) ⊕ {x : BlockGUE.Index dims // x.1 ≠ j})
      (Fin (dims j) ⊕ {x : BlockGUE.Index dims // x.1 ≠ j}) ℂ :=
  (publicBlockDeformation A₀ (frozenExteriorPublicSample dims j Gext)).1.submatrix
    (selectedBlockSplitEquiv dims j) (selectedBlockSplitEquiv dims j)

/-- After conditioning the exterior, recombining an arbitrary singleton sample
changes only the selected upper-left block. -/
theorem reindexed_publicBlockDeformation_split_eq_add_selected {k : ℕ}
    {dims : Fin k → ℕ} (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (j : Fin k) (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j) :
    (publicBlockDeformation A₀
      ((BlockProductDisintegration.split dims j).symm (Gext, Gj))).1.submatrix
        (selectedBlockSplitEquiv dims j) (selectedBlockSplitEquiv dims j) =
      frozenExteriorReindexed A₀ j Gext +
        Matrix.fromBlocks (Gj ⟨j, by simp⟩) 0 0 0 := by
  classical
  ext (x | x) (y | y)
  · simp [frozenExteriorReindexed, frozenExteriorPublicSample,
      zeroSelectedSample, publicBlockDeformation,
      BlockGUE.publicBlockDiagonal, BlockGUE.publicBlockDiagonalRaw,
      split_symm_apply_selected]
  · simp only [frozenExteriorReindexed, frozenExteriorPublicSample,
      publicBlockDeformation, BlockGUE.publicBlockDiagonal,
      BlockGUE.publicBlockDiagonalRaw, selectedBlockSplitEquiv_inl,
      selectedBlockSplitEquiv_inr, Matrix.submatrix_apply, Matrix.add_apply,
      Matrix.fromBlocks]
    rw [dite_eq_right (fun h => y.2 h.symm),
      dite_eq_right (fun h => y.2 h.symm)]
    simp
  · simp [frozenExteriorReindexed, frozenExteriorPublicSample,
      publicBlockDeformation, BlockGUE.publicBlockDiagonal,
      BlockGUE.publicBlockDiagonalRaw, x.property]
  · by_cases hxy : x.1.1 = y.1.1
    · let qx : {i : Fin k // i ≠ j} := ⟨x.1.1, x.2⟩
      have hxGj := split_symm_apply_exterior dims j Gext Gj qx
      have hx0 := split_symm_apply_exterior dims j Gext
        (zeroSelectedSample dims j) qx
      simp only [frozenExteriorReindexed, frozenExteriorPublicSample,
        publicBlockDeformation, BlockGUE.publicBlockDiagonal,
        BlockGUE.publicBlockDiagonalRaw, selectedBlockSplitEquiv_inr,
        Matrix.submatrix_apply, Matrix.add_apply, Matrix.fromBlocks]
      rw [dite_eq_left hxy, dite_eq_left hxy, hxGj, hx0]
      simp [qx]
    · simp [frozenExteriorReindexed, frozenExteriorPublicSample,
        publicBlockDeformation, BlockGUE.publicBlockDiagonal,
        BlockGUE.publicBlockDiagonalRaw, hxy]

/-- The selected principal block of the inverse can be computed after putting that block first,
which passes from sigma-type block indices to the `Sum` convention of Schur complements. -/
theorem selected_inv_submatrix_eq_reindexed {k : ℕ} {dims : Fin k → ℕ}
    (j : Fin k) (M : Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ) :
    (M⁻¹).submatrix (fun a : Fin (dims j) => ⟨j, a⟩)
        (fun a : Fin (dims j) => ⟨j, a⟩) =
      ((M.submatrix (selectedBlockSplitEquiv dims j)
        (selectedBlockSplitEquiv dims j))⁻¹).submatrix Sum.inl Sum.inl := by
  rw [Matrix.inv_submatrix_equiv]
  rfl

/-- Exact projected-trace decomposition of the full regulated public block
resolvent.
Every term on the right is the selected block to which the fixed-exterior
Schur averaging applies.
-/
theorem neg_im_publicBlockRegulatedTrace_eq_sum {k : ℕ}
    {dims : Fin k → ℕ} (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (G : BlockGUE.PublicBlockSample dims) (e eta : ℝ) :
    -((((((publicBlockDeformation A₀ G).1 -
      (e : ℂ) • (1 : Matrix (BlockGUE.Index dims)
        (BlockGUE.Index dims) ℂ)) +
      Complex.I • (eta • (1 : Matrix (BlockGUE.Index dims)
        (BlockGUE.Index dims) ℂ)))⁻¹).trace).im) =
      ∑ j : Fin k,
        -(((((((publicBlockDeformation A₀ G).1 -
          (e : ℂ) • (1 : Matrix (BlockGUE.Index dims)
            (BlockGUE.Index dims) ℂ)) +
          Complex.I • (eta • (1 : Matrix (BlockGUE.Index dims)
            (BlockGUE.Index dims) ℂ)))⁻¹).submatrix
              (fun a : Fin (dims j) => ⟨j, a⟩)
              (fun a : Fin (dims j) => ⟨j, a⟩)).trace).im) := by
  exact neg_im_trace_eq_sum_selectedBlock _

end PSSSNative.BlockBand.PSSS
