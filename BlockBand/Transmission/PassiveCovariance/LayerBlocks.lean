module

public import BlockBand.Transmission.PassiveCovariance.MeanFieldPort
public import BlockBand.Transmission.PassiveLayer.LayerSchur

/-!
# Operator-norm tools for layer matrices

* `blk11 … blk22`, `layerMat_eq_fromBlocks`, `norm_layerMat_le`: a `2W × 2W` layer matrix is the
  block matrix of its four `W × W` blocks, and its operator norm is at most the sum of theirs.
* `norm_diagonal_le`: `‖diag d‖ ≤ c` when every `|d_i| ≤ c`.
* `norm_matrixExpect_le`: `‖E G‖ ≤ E‖G‖` (entrywise expectation, operator norm).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## Blocks of a layer matrix
-/

/-- The physical–physical block. -/
def blk11 (M : LayerMat W) : Matrix (Fin W) (Fin W) ℂ := Matrix.of fun x y => M (phys x) (phys y)
/-- The physical–port block. -/
def blk12 (M : LayerMat W) : Matrix (Fin W) (Fin W) ℂ := Matrix.of fun x y => M (phys x) (port y)
/-- The port–physical block. -/
def blk21 (M : LayerMat W) : Matrix (Fin W) (Fin W) ℂ := Matrix.of fun x y => M (port x) (phys y)
/-- The port–port block. -/
def blk22 (M : LayerMat W) : Matrix (Fin W) (Fin W) ℂ := Matrix.of fun x y => M (port x) (port y)

theorem layerMat_eq_fromBlocks (M : LayerMat W) :
    M = fromBlocks (liftX (blk11 M)) (liftX (blk12 M)) (liftX (blk21 M)) (liftX (blk22 M)) := by
  have h0 : ∀ a : Fin 1, a = 0 := fun a => Subsingleton.elim _ _
  ext i j
  rcases i with ⟨i0, i⟩ | ⟨i0, i⟩ <;> rcases j with ⟨j0, j⟩ | ⟨j0, j⟩ <;>
    simp [fromBlocks, liftX, blk11, blk12, blk21, blk22, h0 i0, h0 j0]

/-- **Operator norm of a layer matrix by its four `W × W` blocks.** -/
theorem norm_layerMat_le (M : LayerMat W) :
    ‖M‖ ≤ ‖blk11 M‖ + ‖blk12 M‖ + ‖blk21 M‖ + ‖blk22 M‖ := by
  conv_lhs => rw [layerMat_eq_fromBlocks M]
  refine (norm_fromBlocks_le _ _ _ _).trans ?_
  gcongr <;> exact norm_liftX_le _

theorem norm_diagonal_le {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (hd : ∀ i, ‖d i‖ ≤ c) : ‖diagonal d‖ ≤ c := by
  refine opNorm_le_of_vec _ hc fun x => ?_
  rw [vecNorm, vecNorm, ← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c)]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mulVec_diagonal, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd i) 2) (by positivity)

/-- `‖E G‖ ≤ E‖G‖` for an entrywise-integrable random matrix. -/
theorem norm_matrixExpect_le {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    {μ : Measure Ω} (G : Ω → Matrix n n ℂ) (hG : ∀ i j, Integrable (fun ω => G ω i j) μ)
    (hn : Integrable (fun ω => ‖G ω‖) μ) : ‖matrixExpect μ G‖ ≤ ∫ ω, ‖G ω‖ ∂μ := by
  have h0 : 0 ≤ ∫ ω, ‖G ω‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  refine opNorm_le_of_vec _ h0 fun v => ?_
  set y := matrixExpect μ G *ᵥ v
  have hb : bilinear y (matrixExpect μ G) v = ∫ ω, bilinear y (G ω) v ∂μ :=
    bilinear_matrixExpect G y v hG
  have hle : vecNorm y ^ 2 ≤ vecNorm y * ((∫ ω, ‖G ω‖ ∂μ) * vecNorm v) := by
    have e : bilinear y (matrixExpect μ G) v = ((vecNorm y ^ 2 : ℝ) : ℂ) := star_self_eq y
    have h1 : vecNorm y ^ 2 = ‖bilinear y (matrixExpect μ G) v‖ := by
      rw [e, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    rw [h1, hb]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ ω, ‖bilinear y (G ω) v‖ ∂μ ≤ ∫ ω, vecNorm y * ‖G ω‖ * vecNorm v ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            ((hn.const_mul _).mul_const _) (Eventually.of_forall fun ω => norm_bilinear_le _ _ _)
      _ = vecNorm y * ((∫ ω, ‖G ω‖ ∂μ) * vecNorm v) := by
          rw [integral_mul_const, integral_const_mul]; ring
  rcases (vecNorm_nonneg y).eq_or_lt with h | h
  · rw [← h]; exact mul_nonneg h0 (vecNorm_nonneg v)
  · nlinarith

end BlockBand.Transmission.PassiveCovariance
