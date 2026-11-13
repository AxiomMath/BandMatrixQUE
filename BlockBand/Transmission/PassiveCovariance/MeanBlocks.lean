module

public import BlockBand.Transmission.PassiveCovariance.DressedBlocks
public import BlockBand.Transmission.PathScalar.MeanStage2

/-!
# The dressed matrix is block diagonal; its inverse is `diag((ζ - X)⁻¹, (z - bm₁)⁻¹)`

With `m₁, m₂` the mean traces and `ζ = zetaOf b E m₁ m₂ = -E - (1-2b)m₁ - bm₂`
(`PathScalar.zetaOf`), the dressed matrix `D = H₀ - S̄` of `MeanFieldOp` has blocks
`blkAt D 0 0 = ζ - X`, `blkAt D 1 1 = (z - bm₁)I` and zero off-diagonal blocks
(`blkAt_dressed`). If `D N = I` then `N`'s blocks are `(ζ - X)⁻¹`, `(z - bm₁)⁻¹ I` and zero
(`blkAt_dressed_inv`). `norm_layerMat_le'` bounds a layer matrix by its four `blkAt` blocks;
`norm_normTrace_le`: `|W⁻¹Tr M| ≤ ‖M‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PathScalar
open scoped Matrix.Norms.L2Operator

variable {W : ℕ}

theorem norm_layerMat_le' (M : LayerMat W) :
    ‖M‖ ≤ ‖blkAt M 0 0‖ + ‖blkAt M 0 1‖ + ‖blkAt M 1 0‖ + ‖blkAt M 1 1‖ :=
  norm_layerMat_le M

theorem blkAt_one (r s : Fin 2) :
    blkAt (1 : LayerMat W) r s = if r = s then 1 else 0 := by
  fin_cases r <;> fin_cases s <;> ext x y <;> simp [blkAt, siteOf, Matrix.one_apply]

theorem blkAt_sub (M N : LayerMat W) (r s : Fin 2) : blkAt (M - N) r s = blkAt M r s - blkAt N r s := by
  ext x y; rfl

theorem norm_normTrace_le (M : Matrix (Fin W) (Fin W) ℂ) : ‖(W : ℂ)⁻¹ * M.trace‖ ≤ ‖M‖ := by
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h; simp
  have hW : (0 : ℝ) < W := by exact_mod_cast h
  rw [norm_mul, norm_inv, Complex.norm_natCast, Matrix.trace]
  have hs : ‖∑ i, M.diag i‖ ≤ W * ‖M‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖M.diag i‖ ≤ ∑ _i : Fin W, ‖M‖ := Finset.sum_le_sum fun i _ => norm_entry_le' M i i
      _ = W * ‖M‖ := by simp
  rw [inv_mul_le_iff₀ hW]; exact hs

set_option linter.unnecessarySeqFocus false in
/-- The blocks of the dressed matrix. -/
theorem blkAt_dressed (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    blkAt (dressed b E X) 0 0 = zetaOf b E (meanTr b E X 0) (meanTr b E X 3) • 1 - X ∧
      blkAt (dressed b E X) 0 1 = 0 ∧ blkAt (dressed b E X) 1 0 = 0 ∧
      blkAt (dressed b E X) 1 1 = (boundaryZ b E - (b : ℂ) * meanTr b E X 0) • 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x y <;>
    simp [blkAt, siteOf, dressed, selfEnergy, layerMatrix, liftX, bondMatrix, zetaOf,
      BlockBand.Internal.Contracts.Layers.blockDiag, Matrix.one_apply, Matrix.diagonal_apply,
      LayerShape.incident] <;> split_ifs <;> simp_all <;> ring

/-- **The inverse of the dressed matrix is block diagonal.** -/
theorem blkAt_dressed_inv (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (hW : 1 ≤ W) (N : LayerMat W)
    (hN : dressed b E X * N = 1) :
    (zetaOf b E (meanTr b E X 0) (meanTr b E X 3) • 1 - X) * blkAt N 0 0 = 1 ∧
      blkAt N 0 0 * (zetaOf b E (meanTr b E X 0) (meanTr b E X 3) • 1 - X) = 1 ∧
      boundaryZ b E - (b : ℂ) * meanTr b E X 0 ≠ 0 ∧
      blkAt N 1 1 = (boundaryZ b E - (b : ℂ) * meanTr b E X 0)⁻¹ • 1 ∧
      blkAt N 0 1 = 0 ∧ blkAt N 1 0 = 0 := by
  obtain ⟨d00, d01, d10, d11⟩ := blkAt_dressed b E X
  set A := zetaOf b E (meanTr b E X 0) (meanTr b E X 3) • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set β := boundaryZ b E - (b : ℂ) * meanTr b E X 0
  have hb : ∀ r s, blkAt (dressed b E X * N) r s = blkAt (1 : LayerMat W) r s := fun r s => by
    rw [hN]
  have e00 := hb 0 0; have e01 := hb 0 1; have e10 := hb 1 0; have e11 := hb 1 1
  rw [blkAt_mul, Fin.sum_univ_two, blkAt_one] at e00 e01 e10 e11
  simp only [d00, d01, d10, d11, Matrix.zero_mul, add_zero, zero_add, Fin.isValue,
    ↓reduceIte, Matrix.smul_mul, Matrix.one_mul] at e00 e01 e10 e11
  simp only [show ((0 : Fin 2) = 1) = False from by decide, show ((1 : Fin 2) = 0) = False from
    by decide, ↓reduceIte] at e01 e10
  have hA' : blkAt N 0 0 * A = 1 := mul_eq_one_comm.mp e00
  have hβ : β ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at e11
    have := congrFun (congrFun e11 ⟨0, hW⟩) ⟨0, hW⟩
    simp at this
  refine ⟨e00, hA', hβ, ?_, ?_, ?_⟩
  · rw [← e11, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  · calc blkAt N 0 1 = (blkAt N 0 0 * A) * blkAt N 0 1 := by rw [hA', Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, e01, Matrix.mul_zero]
  · calc blkAt N 1 0 = β⁻¹ • (β • blkAt N 1 0) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
      _ = 0 := by rw [e10, smul_zero]

end BlockBand.Transmission.PassiveCovariance
