module

public import BlockBand.Coarea.Native.BlockBand.Coarea.Crossing
public import BlockBand.Coarea.Native.BlockBand.LinearAlgebra.SylvesterCongruence

/-!
# Deterministic rank sector at a Schur crossing

This file formalizes the index bookkeeping in the rank-sector step of the proof of the
rank-preserving eigenpair coarea formula.  The retained coordinates precede the
exterior coordinates, and the full Hermitian block matrix is reduced around an
invertible exterior block.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix
open scoped ComplexOrder

/-- The one-based ordered position of a simple zero of a Hermitian matrix: the
number of strictly negative eigenvalues plus one. -/
def orderedZeroRank
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℕ :=
  negativeEigenvalueCount hA + 1

/-- Exact determinant factorization around the invertible exterior block.

This is the determinant part of the Schur reduction in the rank-sector step of
the coarea theorem.  The retained block is first and the exterior block is second;
there are no asymptotic parameters. -/
theorem det_fromBlocks_eq_exterior_mul_schur
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (D : Matrix n n ℂ) [Invertible D] :
    (Matrix.fromBlocks A B Bᴴ D).det =
      D.det * (A - B * ⅟D * Bᴴ).det :=
  Matrix.det_fromBlocks₂₂ A B Bᴴ D

/-- Static inertia decomposition in one-based rank notation.

This is the index computation in the rank-sector step of the coarea theorem.
Normalization: `N_-` counts strictly negative eigenvalues and a selected simple
zero has ordered rank `N_- + 1`. Thus the full rank is the exterior negative
count plus the retained crossing rank. -/
theorem orderedZeroRank_fromBlocks
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (D : Matrix n n ℂ) [Invertible D]
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    let hFull : (Matrix.fromBlocks A B Bᴴ D).IsHermitian :=
      Matrix.isHermitian_fromBlocks_iff.mpr
        ⟨hA, rfl, Matrix.conjTranspose_conjTranspose B, hD⟩
    let hInv : (⅟D).IsHermitian := by
      rw [Matrix.invOf_eq_nonsing_inv D]
      exact hD.inv
    let hSchur : (A - B * ⅟D * Bᴴ).IsHermitian :=
      hA.sub (Matrix.isHermitian_mul_mul_conjTranspose B hInv)
    orderedZeroRank hFull =
      negativeEigenvalueCount hD + orderedZeroRank hSchur := by
  dsimp only [orderedZeroRank]
  rw [negativeEigenvalueCount_hermitianSchur A B D hA hD]
  omega

/-- At a simple Schur zero, reconstruction produces a nonzero null vector of
the full block matrix with the sign convention `(v,-Tv)`. -/
theorem simpleSchurZero_reconstruction
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (D : Matrix n n ℂ) [Invertible D]
    {v : m → ℂ}
    (hsimple : SimpleHermitianEigenpair (A - B * ⅟D * Bᴴ) 0 v) :
    Matrix.fromBlocks A B Bᴴ D *ᵥ schurReconstruction Bᴴ D v = 0 ∧
      schurReconstruction Bᴴ D v ≠ 0 := by
  have hvker : (A - B * ⅟D * Bᴴ) *ᵥ v = 0 := by
    simpa using hsimple.eigenvector
  refine ⟨schurReconstruction_mem_ker A B Bᴴ D v hvker, ?_⟩
  intro hzero
  have hvzero : v = 0 := by
    funext i
    exact congrFun hzero (Sum.inl i)
  have hn := hsimple.normalized
  rw [hvzero] at hn
  simp at hn

/-- Complete local rank-sector bridge at a simple Schur crossing.

This is the rank-sector step in the proof of the coarea theorem.  At the crossing time the
Schur complement equals the retained matrix, its normalized simple zero
reconstructs to a full null vector, the eigenvalue branch crosses strictly
downward with speed `vᴴ𝒟v`, and the full ordered rank splits into the
exterior negative count plus the retained rank.  All hypotheses are explicit;
the statement is exact and finite-dimensional. -/
theorem rankSector_of_simpleSchurCrossing
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (D : Matrix n n ℂ) [Invertible D]
    (hA : A.IsHermitian) (hD : D.IsHermitian)
    {S : ℝ → Matrix m m ℂ} {vCurve : ℝ → m → ℂ} {e : ℝ → ℝ}
    {v' : m → ℂ} {e' t : ℝ}
    (hSt : S t = A - B * ⅟D * Bᴴ)
    (hsimple : SimpleHermitianEigenpair (S t) (e t) (vCurve t))
    (hezero : e t = 0)
    (hSderiv : HasDerivAt S
      (-(schurClock (schurTransfer Bᴴ D))) t)
    (hvderiv : HasDerivAt vCurve v' t)
    (hederiv : HasDerivAt e e' t)
    (heigenpair : ∀ s : ℝ, S s *ᵥ vCurve s = (e s : ℂ) • vCurve s) :
    let hFull : (Matrix.fromBlocks A B Bᴴ D).IsHermitian :=
      Matrix.isHermitian_fromBlocks_iff.mpr
        ⟨hA, rfl, Matrix.conjTranspose_conjTranspose B, hD⟩
    let hInv : (⅟D).IsHermitian := by
      rw [Matrix.invOf_eq_nonsing_inv D]
      exact hD.inv
    let hSchur : (A - B * ⅟D * Bᴴ).IsHermitian :=
      hA.sub (Matrix.isHermitian_mul_mul_conjTranspose B hInv)
    e' < 0 ∧
      orderedZeroRank hFull =
        negativeEigenvalueCount hD + orderedZeroRank hSchur ∧
      Matrix.fromBlocks A B Bᴴ D *ᵥ
        schurReconstruction Bᴴ D (vCurve t) = 0 := by
  dsimp only
  have hslope : e' < 0 :=
    hellmannFeynman_schurClockCrossing_neg
      (schurTransfer Bᴴ D) hsimple hSderiv hvderiv hederiv heigenpair
  have hrank := orderedZeroRank_fromBlocks A B D hA hD
  have hsimpleSchur :
      SimpleHermitianEigenpair (A - B * ⅟D * Bᴴ) 0 (vCurve t) := by
    rw [← hSt, ← hezero]
    exact hsimple
  have hrec := (simpleSchurZero_reconstruction A B D hsimpleSchur).1
  exact ⟨hslope, hrank, hrec⟩

end CoareaNative.BlockBand
