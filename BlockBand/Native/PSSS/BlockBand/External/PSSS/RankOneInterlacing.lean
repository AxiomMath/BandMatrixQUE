module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.HermitianCompression

/-!
# Rank-one Hermitian interlacing: sound algebraic core

This module develops the noncommuting rank-one ray.  It deliberately records
only conclusions established from the checked-in spectral API.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Filter
open scoped ComplexConjugate Matrix Topology

universe u

/-- The orthogonal projector onto `u⊥`, in ambient coordinates. -/
def orthogonalProjector {ι : Type u} [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  1 - Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u))

/-- The rank-one outer product is the matrix of the Hilbert-space rank-one map. -/
theorem toEuclideanLin_vecMulVec_self {ι : Type u} [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin
        (Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u))) =
      (InnerProductSpace.rankOne ℂ u u : EuclideanSpace ℂ ι →ₗ[ℂ]
        EuclideanSpace ℂ ι) := by
  have h := congrArg Matrix.toEuclideanLin
    (InnerProductSpace.symm_toEuclideanLin_rankOne u u)
  simpa using h.symm

/-- In operator coordinates the orthogonal projector is `I - |u⟩⟨u|`. -/
theorem toEuclideanLin_orthogonalProjector {ι : Type u}
    [Fintype ι] [DecidableEq ι] (u : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (orthogonalProjector u) =
      LinearMap.id -
        (InnerProductSpace.rankOne ℂ u u : EuclideanSpace ℂ ι →ₗ[ℂ]
          EuclideanSpace ℂ ι) := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [orthogonalProjector, map_sub, Matrix.toLin_one]
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal,
    toEuclideanLin_vecMulVec_self]

/-- Pointwise formula for the ambient orthogonal projector. -/
theorem toEuclideanLin_orthogonalProjector_apply {ι : Type u}
    [Fintype ι] [DecidableEq ι] (u x : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (orthogonalProjector u) x =
      x - inner ℂ u x • u := by
  rw [toEuclideanLin_orthogonalProjector]
  rfl

/-- A unit vector spans the kernel direction of its orthogonal projector. -/
theorem toEuclideanLin_orthogonalProjector_apply_unit {ι : Type u}
    [Fintype ι] [DecidableEq ι] {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1) :
    Matrix.toEuclideanLin (orthogonalProjector u) u = 0 := by
  rw [toEuclideanLin_orthogonalProjector]
  change u - inner ℂ u u • u = 0
  rw [inner_self_eq_one_of_norm_eq_one hu]
  simp

/-- The image of the unit-vector projector is orthogonal to `u`. -/
theorem inner_orthogonalProjector_apply_unit {ι : Type u}
    [Fintype ι] [DecidableEq ι] {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1)
    (x : EuclideanSpace ℂ ι) :
    inner ℂ u (Matrix.toEuclideanLin (orthogonalProjector u) x) = 0 := by
  rw [toEuclideanLin_orthogonalProjector_apply, inner_sub_right,
    inner_smul_right, inner_self_eq_one_of_norm_eq_one hu]
  simp

/-- The projector fixes every vector orthogonal to `u`. -/
theorem orthogonalProjector_apply_of_inner_eq_zero {ι : Type u}
    [Fintype ι] [DecidableEq ι] (u x : EuclideanSpace ℂ ι)
    (hx : inner ℂ u x = 0) :
    Matrix.toEuclideanLin (orthogonalProjector u) x = x := by
  rw [toEuclideanLin_orthogonalProjector_apply, hx]
  simp

/-- The orthogonal projector is Hermitian. -/
theorem orthogonalProjector_conjTranspose {ι : Type u}
    [Fintype ι] [DecidableEq ι] (u : EuclideanSpace ℂ ι) :
    (orthogonalProjector u)ᴴ = orthogonalProjector u := by
  unfold orthogonalProjector
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_vecMulVec]
  simp

/-- The ambient compression has the distinguished zero eigenvector `u`. -/
theorem orthogonalCompression_apply_unit_eq_zero {ι : Type u}
    [Fintype ι] [DecidableEq ι] (K : HermitianMatrix ι)
    {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1) :
    Matrix.toEuclideanLin (orthogonalCompression K u : Matrix ι ι ℂ) u = 0 := by
  change Matrix.toEuclideanLin
    (orthogonalProjector u * K.1 * (orthogonalProjector u)ᴴ) u = 0
  rw [orthogonalProjector_conjTranspose]
  let b := (EuclideanSpace.basisFun ι ℂ).toBasis
  change Matrix.toLin b b
    (orthogonalProjector u * K.1 * orthogonalProjector u) u = 0
  rw [Matrix.toLin_mul_apply b b b, Matrix.toLin_mul_apply b b b]
  change Matrix.toEuclideanLin (orthogonalProjector u)
    (Matrix.toEuclideanLin K.1
      (Matrix.toEuclideanLin (orthogonalProjector u) u)) = 0
  rw [toEuclideanLin_orthogonalProjector_apply_unit hu]
  simp

/-- The ambient compression maps into `u⊥`; hence its restriction to `u⊥`
is a well-defined endomorphism and the ambient direction `ℂ u` contributes
the distinguished zero block. -/
theorem inner_orthogonalCompression_apply_unit {ι : Type u}
    [Fintype ι] [DecidableEq ι] (K : HermitianMatrix ι)
    {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1) (x : EuclideanSpace ℂ ι) :
    inner ℂ u
      (Matrix.toEuclideanLin (orthogonalCompression K u : Matrix ι ι ℂ) x) = 0 := by
  change inner ℂ u
    (Matrix.toEuclideanLin
      (orthogonalProjector u * K.1 * (orthogonalProjector u)ᴴ) x) = 0
  rw [orthogonalProjector_conjTranspose]
  let b := (EuclideanSpace.basisFun ι ℂ).toBasis
  change inner ℂ u
    (Matrix.toLin b b (orthogonalProjector u * K.1 * orthogonalProjector u) x) = 0
  rw [Matrix.toLin_mul_apply b b b, Matrix.toLin_mul_apply b b b]
  change inner ℂ u (Matrix.toEuclideanLin (orthogonalProjector u) _) = 0
  exact inner_orthogonalProjector_apply_unit hu _

/-- The largest decreasingly ordered eigenvalue dominates every unit-vector
Rayleigh quotient.  This is the `k = 0` Courant–Fischer direction used for
the escaping branch. -/
theorem re_inner_le_eigenvalues₀_zero {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : HermitianMatrix ι) {x : EuclideanSpace ℂ ι} (hx : ‖x‖ = 1) :
    RCLike.re (inner ℂ (Matrix.toEuclideanLin A.1 x) x) ≤
      A.2.eigenvalues₀ (0 : Fin (Fintype.card ι)) := by
  let hA := Matrix.isSymmetric_toEuclideanLin_iff.mpr A.2
  rw [Matrix.IsHermitian.eigenvalues₀]
  rw [hA.re_inner_apply_self_eq_sum_eigenvalues_mul_sq
    finrank_euclideanSpace x]
  calc
    ∑ i : Fin (Fintype.card ι),
        hA.eigenvalues finrank_euclideanSpace i *
          ‖(hA.eigenvectorBasis finrank_euclideanSpace).repr x i‖ ^ 2
      ≤ ∑ i : Fin (Fintype.card ι),
          hA.eigenvalues finrank_euclideanSpace 0 *
            ‖(hA.eigenvectorBasis finrank_euclideanSpace).repr x i‖ ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right
            (hA.eigenvalues_antitone finrank_euclideanSpace (Fin.zero_le i))
            (sq_nonneg _)
    _ = hA.eigenvalues finrank_euclideanSpace 0 * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [(hA.eigenvectorBasis
        finrank_euclideanSpace).repr_apply_apply]
      exact (hA.eigenvectorBasis
        finrank_euclideanSpace).sum_sq_norm_inner_right x
    _ = hA.eigenvalues finrank_euclideanSpace 0 := by rw [hx]; ring

/-- Operator form of the rank-one ray. -/
theorem toEuclideanLin_rankOneShift {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (τ : ℝ) :
    Matrix.toEuclideanLin (rankOneShift K u τ : Matrix ι ι ℂ) =
      Matrix.toEuclideanLin K.1 + (τ : ℂ) •
        (InnerProductSpace.rankOne ℂ u u : EuclideanSpace ℂ ι →ₗ[ℂ]
          EuclideanSpace ℂ ι) := by
  change Matrix.toEuclideanLin
      (K.1 + (τ : ℂ) •
        Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u))) = _
  rw [map_add, map_smul, toEuclideanLin_vecMulVec_self]

/-- Along a unit vector, the rank-one perturbation adds exactly `τ` to the
Rayleigh quotient. -/
theorem re_inner_rankOneShift_unit {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1)
    (τ : ℝ) :
    RCLike.re (inner ℂ
      (Matrix.toEuclideanLin (rankOneShift K u τ : Matrix ι ι ℂ) u) u) =
      RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u) + τ := by
  rw [toEuclideanLin_rankOneShift, LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_left, map_add]
  rw [inner_smul_left]
  change _ + RCLike.re ((starRingEnd ℂ) (τ : ℂ) *
    inner ℂ (InnerProductSpace.rankOne ℂ u u u) u) = _
  rw [InnerProductSpace.inner_left_rankOne_apply,
    inner_self_eq_one_of_norm_eq_one hu]
  simp

/-- The largest eigenvalue of the positive rank-one ray diverges to `+∞`. -/
theorem eigenvalues₀_zero_rankOneShift_tendsto_atTop {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : HermitianMatrix ι) {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1) :
    Tendsto (fun τ : ℝ =>
      (rankOneShift K u τ).2.eigenvalues₀
        (0 : Fin (Fintype.card ι))) atTop atTop := by
  refine Filter.tendsto_atTop_mono (f := fun τ : ℝ =>
      RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u) + τ)
    (g := fun τ : ℝ => (rankOneShift K u τ).2.eigenvalues₀
      (0 : Fin (Fintype.card ι))) ?_ ?_
  · intro τ
    rw [← re_inner_rankOneShift_unit K hu τ]
    exact re_inner_le_eigenvalues₀_zero (rankOneShift K u τ) hu
  · simpa [Function.id_def, add_comm] using
    Filter.tendsto_atTop_add_const_right atTop
      (RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u)) tendsto_id

end PSSSNative.BlockBand.PSSS
