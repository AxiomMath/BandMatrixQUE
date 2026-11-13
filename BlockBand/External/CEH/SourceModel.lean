module

public import Mathlib

/-!
# The deformed Wigner model of CEH

This file defines the deformed Wigner model `H_λ = H₀ + λW` of CEH (arXiv:2607.02446v2,
(2.1)–(2.3)), its resolvent, and a measurable ordered eigenpair selection.

The Wigner matrix `W` has independent entries on and above the diagonal; after multiplication by
`√N`, the diagonal entries have a common real law `χ_d` and the off-diagonal entries a common
complex law `χ_od`, centred, with all moments bounded by constants fixed for the whole family.
The condition `|E χ_od²| < 1` is kept as stated in CEH; a real variable of variance one does not
satisfy it, so `χ_od` is complex (the GUE case has `E χ_od² = 0`). Matrix norms are
Euclidean operator norms and vector norms are the unnormalized `ℓ²` norm.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- Complex `N × N` matrices. -/
abbrev SourceMatrix (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

/-- Hermitian `N × N` matrices, with the subspace topology and σ-algebra. -/
abbrev SourceHermitian (N : ℕ) := {A : SourceMatrix N // A.IsHermitian}

/-- All upper-triangular coordinates, including the real diagonal. -/
abbrev SourceUpperPair (N : ℕ) := {q : Fin N × Fin N // q.1 ≤ q.2}

/-- The diagonal and off-diagonal entry laws and the uniform moment constants of CEH
Assumption 2.1: both laws are centred with all moments finite, `E|χ_od|² = 1` and
`|E χ_od²| < 1`; the diagonal variance is unrestricted. -/
structure EntryDistributions where
  diagonal : ProbabilityMeasure ℝ
  offDiagonal : ProbabilityMeasure ℂ
  momentBound : ℕ → ℝ
  momentBound_nonneg : ∀ p, 0 ≤ momentBound p
  diagonal_integrable : Integrable (fun x : ℝ => x) (diagonal : Measure ℝ)
  offDiagonal_integrable : Integrable (fun x : ℂ => x) (offDiagonal : Measure ℂ)
  diagonal_centered : ∫ x, x ∂(diagonal : Measure ℝ) = 0
  offDiagonal_centered : ∫ x, x ∂(offDiagonal : Measure ℂ) = 0
  diagonal_moments_integrable : ∀ p : ℕ,
    Integrable (fun x : ℝ => ‖x‖ ^ p) (diagonal : Measure ℝ)
  offDiagonal_moments_integrable : ∀ p : ℕ,
    Integrable (fun x : ℂ => ‖x‖ ^ p) (offDiagonal : Measure ℂ)
  moments : ∀ p : ℕ,
    (∫ x, ‖x‖ ^ p ∂(diagonal : Measure ℝ)) +
      (∫ x, ‖x‖ ^ p ∂(offDiagonal : Measure ℂ)) ≤ momentBound p
  variance : ∫ x, ‖x‖ ^ 2 ∂(offDiagonal : Measure ℂ) = 1
  square_integrable : Integrable (fun x : ℂ => x ^ 2) (offDiagonal : Measure ℂ)
  sigma_lt_one : ‖∫ x, x ^ 2 ∂(offDiagonal : Measure ℂ)‖ < 1

/-- A Wigner family: for each `N`, a law on Hermitian matrices with `w_aa = N^{-1/2} χ_d` and
`w_ab = N^{-1/2} χ_od` (`a < b`), independent on and above the diagonal. The entry laws and the
moment constants do not depend on `N`. -/
structure WignerFamily where
  entries : EntryDistributions
  law : (N : ℕ) → ProbabilityMeasure (SourceHermitian N)
  upper_independent : ∀ N : ℕ, 0 < N →
    iIndepFun (fun q : SourceUpperPair N => fun W : SourceHermitian N =>
      ((Real.sqrt (N : ℝ) : ℂ) * W.1 q.1.1 q.1.2))
      (law N : Measure (SourceHermitian N))
  diagonal_law : ∀ (N : ℕ) (a : Fin N),
    HasLaw (fun W : SourceHermitian N => Real.sqrt (N : ℝ) * (W.1 a a).re)
      (entries.diagonal : Measure ℝ) (law N : Measure (SourceHermitian N))
  offDiagonal_law : ∀ (N : ℕ) (a b : Fin N), a < b →
    HasLaw (fun W : SourceHermitian N => (Real.sqrt (N : ℝ) : ℂ) * W.1 a b)
      (entries.offDiagonal : Measure ℂ) (law N : Measure (SourceHermitian N))

/-- The deformed matrix `H_λ = H₀ + λW`, `λ` real. -/
def deformedMatrix {N : ℕ} (lambda : ℝ) (H0 W : SourceHermitian N) : SourceMatrix N :=
  H0.1 + (lambda : ℂ) • W.1

/-- `H_λ` is Hermitian. -/
theorem deformedMatrix_isHermitian {N : ℕ} (lambda : ℝ)
    (H0 W : SourceHermitian N) : (deformedMatrix lambda H0 W).IsHermitian := by
  exact H0.2.add (W.2.smul (by simp [IsSelfAdjoint]))

/-- `H_λ` as a Hermitian matrix. -/
def deformedHermitian {N : ℕ} (lambda : ℝ) (H0 W : SourceHermitian N) :
    SourceHermitian N := ⟨deformedMatrix lambda H0 W, deformedMatrix_isHermitian lambda H0 W⟩

/-- The polynomial deformation bound `‖H₀‖ ≤ C N^κ λ` of CEH (2.2), in the operator norm. -/
def DeformationBound {N : ℕ} (kappa C lambda : ℝ) (H0 : SourceHermitian N) : Prop :=
  ‖H0.1‖ ≤ C * (N : ℝ) ^ kappa * lambda

/-- The resolvent `(H_λ - z)⁻¹`, using Lean's total matrix inverse; for `Im z ≠ 0` it is the
ordinary inverse. -/
def sourceResolvent {N : ℕ} (lambda : ℝ) (H0 W : SourceHermitian N)
    (z : ℂ) : SourceMatrix N :=
  (deformedMatrix lambda H0 W - z • (1 : SourceMatrix N))⁻¹

/-- The unnormalized Euclidean norm `(Σ_a |x_a|²)^{1/2}`. -/
def sourceVectorNorm {N : ℕ} (x : Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ a, ‖x a‖ ^ 2)

/-- The sesquilinear form `x* A y`. -/
def sourceMatrixElement {N : ℕ} (A : SourceMatrix N) (x y : Fin N → ℂ) : ℂ :=
  star x ⬝ᵥ (A *ᵥ y)

/-- A measurable selection of increasingly ordered eigenvalues and orthonormal eigenvectors of
every Hermitian matrix. Repeated eigenvalues are allowed, with any choice of eigenvectors. -/
structure EigenpairSelection (N : ℕ) where
  eigenvalue : SourceHermitian N → Fin N → ℝ
  eigenvector : SourceHermitian N → Fin N → Fin N → ℂ
  measurable_eigenvalue : ∀ i, Measurable (fun H => eigenvalue H i)
  measurable_eigenvector : ∀ i a, Measurable (fun H => eigenvector H i a)
  increasing : ∀ H, Monotone (eigenvalue H)
  orthonormal : ∀ H i j,
    star (eigenvector H i) ⬝ᵥ eigenvector H j = if i = j then 1 else 0
  eigen_equation : ∀ H i,
    H.1 *ᵥ eigenvector H i = (eigenvalue H i : ℂ) • eigenvector H i

end BlockBand.External.CEH
