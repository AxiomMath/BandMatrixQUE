module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedEuclidean
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Diagonal covariance data for the Euclidean replicated GUE law

This module proves the missing cross-coordinate covariance cancellation from
the independent product law and records the exact diagonal covariance
kernel of the Euclidean transport.  No concentration or variance estimate is
assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped NNReal RealInnerProductSpace

namespace CEHNative.BlockBand.External.CEH
namespace ReplicatedGUEEuclidean

/-- Distinct Euclidean coordinates have zero covariance under the transported
replicated full-GUE law. -/
theorem covariance_coordinate_eq_zero {N d : ℕ}
    {i j : Fin (Fintype.card (HermitianCoordinate (N * d)))} (hij : i ≠ j) :
    cov[(fun x : CoordinateEuclideanSpace N d => x i),
      (fun x : CoordinateEuclideanSpace N d => x j); measure N d] = 0 := by
  have hind := (iIndepFun_replicatedNormalizedGUECoordinates N d).indepFun hij
  have hi : MemLp (fun x : ReplicatedGUECoordinateSpace N d => x i) 2
      (replicatedNormalizedGUEMeasure N d) :=
    ((FiniteGaussianPoincare.replicatedNormalizedGUE_hasGaussianLaw_id N d).eval i).memLp_two
  have hj : MemLp (fun x : ReplicatedGUECoordinateSpace N d => x j) 2
      (replicatedNormalizedGUEMeasure N d) :=
    ((FiniteGaussianPoincare.replicatedNormalizedGUE_hasGaussianLaw_id N d).eval j).memLp_two
  have hzero := hind.covariance_eq_zero hi hj
  have htransport := (hasLaw_coordinatesEquiv N d).covariance_fun_comp
    (f := fun x : CoordinateEuclideanSpace N d => x i)
    (g := fun x : CoordinateEuclideanSpace N d => x j)
    (by fun_prop) (by fun_prop)
  rw [show (fun y : ReplicatedGUECoordinateSpace N d =>
      (coordinatesEquiv N d y) i) = (fun y => y i) by rfl,
    show (fun y : ReplicatedGUECoordinateSpace N d =>
      (coordinatesEquiv N d y) j) = (fun y => y j) by rfl] at htransport
  exact htransport.symm.trans hzero

/-- Unified coordinate covariance kernel: diagonal entries are the exact GUE
coordinate variances and all cross entries vanish. -/
theorem covariance_coordinate {N d : ℕ}
    (i j : Fin (Fintype.card (HermitianCoordinate (N * d)))) :
    cov[(fun x : CoordinateEuclideanSpace N d => x i),
      (fun x : CoordinateEuclideanSpace N d => x j); measure N d] =
      if i = j then
        hermitianGUEFinCoordinateVariance (N * d)
          (1 / ((N * d : ℕ) : ℝ)) (by positivity) i else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    rw [covariance_self (by fun_prop)]
    exact variance_coordinate N d i
  · simp [hij, covariance_coordinate_eq_zero hij]

/-- Every coordinate variance is bounded above by the normalized diagonal
variance `1/(N*d)`. -/
theorem coordinateVariance_le {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d)))) :
    (hermitianGUEFinCoordinateVariance (N * d)
      (1 / ((N * d : ℕ) : ℝ)) (by positivity) k : ℝ) ≤
      1 / (((N * d : ℕ) : ℝ)) := by
  cases h : (hermitianCoordinateEquivFin (N * d)).symm k with
  | inl i =>
      rw [normalizedCoordinateVariance_diagonal (Nat.mul_pos hN hd) k i h]
  | inr c =>
      rw [normalizedCoordinateVariance_offDiagonal (Nat.mul_pos hN hd) k c h]
      have hn : (0 : ℝ) < ((N * d : ℕ) : ℝ) := by positivity
      have : 1 / (2 * (((N * d : ℕ) : ℝ))) ≤ 1 / (((N * d : ℕ) : ℝ)) := by
        exact one_div_le_one_div_of_le hn (by linarith)
      exact this

/-- For positive replicated dimension, a diagonal coordinate attains the upper
variance `1/(N*d)`.  Together with `coordinateVariance_le`, this identifies the
finite maximum of the diagonal covariance data exactly. -/
theorem exists_coordinateVariance_eq {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    ∃ k : Fin (Fintype.card (HermitianCoordinate (N * d))),
      (hermitianGUEFinCoordinateVariance (N * d)
        (1 / ((N * d : ℕ) : ℝ)) (by positivity) k : ℝ) =
        1 / (((N * d : ℕ) : ℝ)) := by
  have hn : 0 < N * d := Nat.mul_pos hN hd
  let i : Fin (N * d) := ⟨0, hn⟩
  let k : Fin (Fintype.card (HermitianCoordinate (N * d))) :=
    hermitianCoordinateEquivFin (N * d) (.inl i)
  refine ⟨k, ?_⟩
  apply normalizedCoordinateVariance_diagonal hn k i
  simp [k]

end ReplicatedGUEEuclidean
end CEHNative.BlockBand.External.CEH
