module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpCoordinateProductFubini

/-!
# Sharp strict-coordinate index reorganization

This module reorganizes the strict upper-pair contractions produced by the
exact circular Gaussian integration by parts.  The reorganization is
pointwise and uses only profile flatness, stochasticity, finite Cauchy–Schwarz,
and the Hermitian resolvent bound; no aggregate Ward certificate is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSharpCoordinateIBP

open Matrix MeasureTheory ProbabilityTheory
open ERGaussianCoordinate ERResolventMomentIBP ERProfile
open ERComplementBackgroundReconstruction
open scoped BigOperators NNReal ComplexOrder Matrix.Norms.L2Operator

local instance (p : Params) : NeZero p.n := p.nNeZero
local instance (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance (p : Params) : Fintype (UpperPair p) := Fintype.ofFinite _
local instance (p : Params) : DecidableEq (UpperPair p) := Classical.decEq _

/-- A row's squared Euclidean mass is bounded by the squared `ℓ²` operator
norm. -/
theorem matrix_row_norm_sq_le_l2_opNorm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (i : ι) :
    ∑ j, ‖G i j‖ ^ 2 ≤ ‖G‖ ^ 2 := by
  let e : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single i 1)
  let v : EuclideanSpace ℂ ι :=
    (EuclideanSpace.equiv ι ℂ).symm ((G.conjTranspose).mulVec e.ofLp)
  have h := Matrix.l2_opNorm_mulVec G.conjTranspose e
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hv : ‖v‖ ≤ ‖G‖ := by
    simpa [v, Matrix.l2_opNorm_conjTranspose, he] using h
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
  have hG0 : 0 ≤ ‖G‖ := norm_nonneg _
  have hsq := mul_self_le_mul_self hv0 hv
  rw [← sq, ← sq] at hsq
  simpa [v, e, EuclideanSpace.norm_sq_eq, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply] using hsq

/-- The analogous squared-mass estimate for a column. -/
theorem matrix_column_norm_sq_le_l2_opNorm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (i : ι) :
    ∑ j, ‖G j i‖ ^ 2 ≤ ‖G‖ ^ 2 := by
  simpa [Matrix.conjTranspose_apply, norm_star,
    Matrix.l2_opNorm_conjTranspose] using
    matrix_row_norm_sq_le_l2_opNorm_sq G.conjTranspose i

/-- The full source inverse has the dimension-free Hermitian resolvent
operator bound. -/
theorem norm_sourceInverse_l2_opNorm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) :
    ‖sourceInverse A z‖ ≤ (z.im)⁻¹ := by
  rw [sourceInverse_eq_neg_matrixResolvent A hA z hz.ne', norm_neg]
  let B : Matrix ι ι ℂ := (z.re : ℂ) • 1 - A
  have hB : B.IsHermitian :=
    Matrix.isHermitian_one.smul (RCLike.conj_ofReal z.re) |>.sub hA
  have hzero : (0 : Matrix ι ι ℂ).PosSemidef := Matrix.PosSemidef.zero
  have hpencil : cauchyResolventPencil B 0 z.im 0 =
      z • (1 : Matrix ι ι ℂ) - A := by
    ext a b
    simp [cauchyResolventPencil, B, Complex.ext_iff]
    constructor <;> ring
  have hnorm : ‖(cauchyResolventPencil B 0 z.im 0)⁻¹‖ ≤ (z.im)⁻¹ :=
    norm_cauchyResolventPencil_nonsing_inv_le
      B 0 hB hzero hz (by simp)
  rwa [hpencil] at hnorm

/-- Every row of the source inverse of a sample has Ward mass at most `η⁻²`. -/
theorem Law.sum_norm_sourceInverse_row_sq_le
    {p : Params} (M : Law p) (ω : M.Ω)
    (z : ℂ) (hz : 0 < z.im) (i : Site p.n p.W) :
    ∑ j, ‖sourceInverse (M.H ω) z i j‖ ^ 2 ≤ (z.im)⁻¹ ^ 2 := by
  calc
    _ ≤ ‖sourceInverse (M.H ω) z‖ ^ 2 :=
      matrix_row_norm_sq_le_l2_opNorm_sq
        (sourceInverse (M.H ω) z) i
    _ ≤ (z.im)⁻¹ ^ 2 := by
      gcongr
      exact norm_sourceInverse_l2_opNorm_le
        (M.H ω) (M.isHermitian ω) z hz

/-- Every column of the source inverse of a sample has Ward mass at most `η⁻²`. -/
theorem Law.sum_norm_sourceInverse_column_sq_le
    {p : Params} (M : Law p) (ω : M.Ω)
    (z : ℂ) (hz : 0 < z.im) (j : Site p.n p.W) :
    ∑ i, ‖sourceInverse (M.H ω) z i j‖ ^ 2 ≤ (z.im)⁻¹ ^ 2 := by
  calc
    _ ≤ ‖sourceInverse (M.H ω) z‖ ^ 2 :=
      matrix_column_norm_sq_le_l2_opNorm_sq
        (sourceInverse (M.H ω) z) j
    _ ≤ (z.im)⁻¹ ^ 2 := by
      gcongr
      exact norm_sourceInverse_l2_opNorm_le
        (M.H ω) (M.isHermitian ω) z hz

end ERSharpCoordinateIBP
end GaussianRing
end ERNative.BlockBand
