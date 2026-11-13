module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplication
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPAggregate
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The full normalized GUE law on the replicated dimension

The CEH tensor argument uses a fresh full GUE matrix on dimension `N*d`, not a
copy of one `N`-dimensional sample.  This module puts that distinction into the
types.  The law below is the finite product of the real Hermitian coordinates
with diagonal variance `(N*d)⁻¹` and real/imaginary strict-upper variance
`(2*N*d)⁻¹`.  Its reconstruction is then reindexed from `Fin (N*d)` to the
paper's tensor index `Fin N × Fin d`.

In particular, no statement identifies this sample with `X ⊗ I_d`.  Without a
replicated local law, this module proves the exact product-coordinate law,
its covariance kernel, measurable Hermitian reconstruction, and the pointwise
four-constellation polarization under its expectation.  Identifying the four
resulting expectations with replicated deterministic MDE data would require
the replicated-spectrum/MDE comparison and quantitative remainder bounds, which
are not part of this module.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal

/-- Real coordinates of one full Hermitian matrix of dimension `N*d`. -/
abbrev ReplicatedGUECoordinateSpace (N d : ℕ) :=
  HermitianCoordinateSpace (N * d)

/-- The normalized full-GUE product law at replicated dimension. -/
def replicatedNormalizedGUEMeasure (N d : ℕ) :
    Measure (ReplicatedGUECoordinateSpace N d) :=
  hermitianGUECoordinateMeasure (N * d) (1 / ((N * d : ℕ) : ℝ)) (by positivity)

instance replicatedNormalizedGUEMeasure.instIsProbabilityMeasure
    (N d : ℕ) : IsProbabilityMeasure (replicatedNormalizedGUEMeasure N d) := by
  unfold replicatedNormalizedGUEMeasure
  infer_instance

/-- Every real Hermitian coordinate has its exact Gaussian marginal under the
replicated product law. -/
theorem replicatedNormalizedGUE_coordinate_hasLaw
    (N d : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d)))) :
    HasLaw (fun x : ReplicatedGUECoordinateSpace N d => x k)
      (gaussianReal 0 (hermitianGUEFinCoordinateVariance (N * d)
        (1 / ((N * d : ℕ) : ℝ)) (by positivity) k))
      (replicatedNormalizedGUEMeasure N d) := by
  exact hermitianGUECoordinate_hasLaw (N * d)
    (1 / ((N * d : ℕ) : ℝ)) (by positivity) k

/-- The real coordinates of the replicated full GUE are mutually independent. -/
theorem iIndepFun_replicatedNormalizedGUECoordinates (N d : ℕ) :
    iIndepFun
      (fun k (x : ReplicatedGUECoordinateSpace N d) => x k)
      (replicatedNormalizedGUEMeasure N d) := by
  exact iIndepFun_hermitianGUECoordinates (N * d)
    (1 / ((N * d : ℕ) : ℝ)) (by positivity)

/-- Equivalence between the flattened and tensor index conventions. -/
def replicatedIndexEquiv (N d : ℕ) : Fin (N * d) ≃ Fin N × Fin d :=
  finProdFinEquiv.symm

/-- Reconstruct the full `N*d` GUE and only then reindex it to the tensor
index.  This is generally not a Kronecker product. -/
def replicatedFullGUEBlock (N d : ℕ)
    (x : ReplicatedGUECoordinateSpace N d) :
    Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ :=
  Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
    (hermitianGUEBlock (N * d) x).1

/-- The reindexed full GUE reconstruction is Hermitian pointwise. -/
theorem replicatedFullGUEBlock_isHermitian (N d : ℕ)
    (x : ReplicatedGUECoordinateSpace N d) :
    (replicatedFullGUEBlock N d x).IsHermitian := by
  exact (hermitianGUEBlock_isHermitian (N * d) x).reindex
    (replicatedIndexEquiv N d)

/-- Every entry of the reindexed full-GUE reconstruction is measurable. -/
theorem measurable_replicatedFullGUEBlock_entry (N d : ℕ)
    (p q : Fin N × Fin d) :
    Measurable (fun x : ReplicatedGUECoordinateSpace N d =>
      replicatedFullGUEBlock N d x p q) := by
  change Measurable (fun x : HermitianCoordinateSpace (N * d) =>
    (hermitianGUEBlock (N * d) x).1
      ((replicatedIndexEquiv N d).symm p)
      ((replicatedIndexEquiv N d).symm q))
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
    (measurable_hermitianGUEBlock (N * d)).subtype_val)

/-- The full reindexed matrix reconstruction is measurable for the product
Borel structure on matrix entries. -/
theorem measurable_replicatedFullGUEBlock (N d : ℕ) :
    Measurable (replicatedFullGUEBlock N d) := by
  refine Measurable.of_eval fun p => Measurable.of_eval fun q => ?_
  exact measurable_replicatedFullGUEBlock_entry N d p q

/-- One covariance direction, expressed on the tensor index after reindexing. -/
def replicatedGUECoordinateDirection (N d : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d))))
    (p q : Fin N × Fin d) : ℂ :=
  gueCoordinateDirection (N * d) k
    ((replicatedIndexEquiv N d).symm p)
    ((replicatedIndexEquiv N d).symm q)

/-- Exact covariance kernel of the full replicated GUE.  The factor is
`1/(N*d)`, including for entries in different tensor slots; it is not the
block-diagonal covariance of `X ⊗ I_d`. -/
theorem replicatedNormalizedGUECoordinateKernel
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p a b q : Fin N × Fin d) :
    (∑ k : Fin (Fintype.card (HermitianCoordinate (N * d))),
      (hermitianGUEFinCoordinateVariance (N * d)
        (1 / ((N * d : ℕ) : ℝ)) (by positivity) k : ℂ) *
        replicatedGUECoordinateDirection N d k p a *
        replicatedGUECoordinateDirection N d k b q) =
      if p = q ∧ a = b then ((N * d : ℕ) : ℂ)⁻¹ else 0 := by
  unfold replicatedGUECoordinateDirection
  simpa only [Equiv.apply_eq_iff_eq] using
    normalizedGUECoordinateKernel (Nat.mul_pos hN hd)
      ((replicatedIndexEquiv N d).symm p)
      ((replicatedIndexEquiv N d).symm a)
      ((replicatedIndexEquiv N d).symm b)
      ((replicatedIndexEquiv N d).symm q)

/-- A coordinate direction bundled as a matrix on the tensor index. -/
def replicatedGUECoordinateDirectionMatrix (N d : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d)))) :
    Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ :=
  fun p q => replicatedGUECoordinateDirection N d k p q

/-- Covariance contraction of the full replicated GUE, written directly on
the tensor index. -/
def replicatedNormalizedGUECovarianceContraction (N d : ℕ)
    (X : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) :
    Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ :=
  fun p q => ∑ k : Fin (Fintype.card (HermitianCoordinate (N * d))),
    (hermitianGUEFinCoordinateVariance (N * d)
      (1 / ((N * d : ℕ) : ℝ)) (by positivity) k : ℂ) *
      (replicatedGUECoordinateDirectionMatrix N d k * X *
        replicatedGUECoordinateDirectionMatrix N d k) p q

/-- The full replicated covariance contracts to `(N*d)⁻¹ Tr(X) I`, exactly
the normalization used by `productNTrace`. -/
theorem replicatedNormalizedGUECovarianceContraction_eq
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (X : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) :
    replicatedNormalizedGUECovarianceContraction N d X =
      productNTrace X • (1 : Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ) := by
  ext p q
  unfold replicatedNormalizedGUECovarianceContraction
  simp_rw [Matrix.mul_apply, replicatedGUECoordinateDirectionMatrix]
  have hreorder :
      (∑ k, (hermitianGUEFinCoordinateVariance (N * d)
          (1 / ((N * d : ℕ) : ℝ)) (by positivity) k : ℂ) *
        ∑ b, (∑ a, replicatedGUECoordinateDirection N d k p a * X a b) *
          replicatedGUECoordinateDirection N d k b q) =
      ∑ b, ∑ a, X a b * ∑ k,
        (hermitianGUEFinCoordinateVariance (N * d)
          (1 / ((N * d : ℕ) : ℝ)) (by positivity) k : ℂ) *
          replicatedGUECoordinateDirection N d k p a *
          replicatedGUECoordinateDirection N d k b q := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hreorder]
  simp_rw [replicatedNormalizedGUECoordinateKernel hN hd]
  by_cases hpq : p = q
  · subst q
    simp [productNTrace, Matrix.trace]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp [hpq, productNTrace]

/-- A single-coordinate observable integrates against its normalized full-GUE
marginal.  This is the exact product-law factorization available without any
replicated local-law input. -/
theorem integral_replicatedNormalizedGUE_comp_coordinate
    {N d : ℕ}
    (k : Fin (Fintype.card (HermitianCoordinate (N * d))))
    (F : ℝ → ℂ) (hF : AEStronglyMeasurable F
      (gaussianReal 0 (hermitianGUEFinCoordinateVariance (N * d)
        (1 / ((N * d : ℕ) : ℝ)) (by positivity) k))) :
    (∫ x : ReplicatedGUECoordinateSpace N d, F (x k)
      ∂replicatedNormalizedGUEMeasure N d) =
      ∫ t : ℝ, F t ∂gaussianReal 0
        (hermitianGUEFinCoordinateVariance (N * d)
          (1 / ((N * d : ℕ) : ℝ)) (by positivity) k) := by
  unfold replicatedNormalizedGUEMeasure hermitianGUECoordinateMeasure
  exact integral_comp_eval hF

/-- Under the full replicated GUE law, the positive-chain expectation
is exactly the expectation of its four ordinary adjoint constellations.  This
is the maximal law-to-positive-chain bridge that is purely algebraic: no
replicated MDE comparison or probabilistic estimate is used. -/
theorem replicatedNormalizedGUE_integral_positiveChain_eq_fourfold
    {N d : ℕ}
    (G₁ G₂ : ReplicatedGUECoordinateSpace N d →
      Matrix (Fin (N * d)) (Fin (N * d)) ℂ)
    (A : Matrix (Fin (N * d)) (Fin (N * d)) ℂ) :
    (∫ y, NTrace
      (CEHNative.BlockBand.matrixImaginaryPart (G₁ y) * A *
        CEHNative.BlockBand.matrixImaginaryPart (G₂ y) * Aᴴ)
      ∂replicatedNormalizedGUEMeasure N d) =
    ∫ y, NTrace ((-(1 / 4 : ℂ)) •
      (G₁ y * A * G₂ y * Aᴴ + (G₁ y)ᴴ * A * (G₂ y)ᴴ * Aᴴ -
        G₁ y * A * (G₂ y)ᴴ * Aᴴ - (G₁ y)ᴴ * A * G₂ y * Aᴴ))
      ∂replicatedNormalizedGUEMeasure N d := by
  apply integral_congr_ae
  filter_upwards with y
  exact positiveChainTrace_eq_fourfold (G₁ y) A (G₂ y)

end CEHNative.BlockBand.External.CEH
