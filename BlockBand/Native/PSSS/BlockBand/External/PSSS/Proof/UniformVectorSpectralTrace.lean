module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorComplexRealification
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.InnerProductSpace.Trace
public import BlockBand.Model.Construction.OrderedCourantFischer

/-!
# Spectral trace normalization for the spherical Gaussian small-ball estimate

This module closes the trace link between Mathlib's Euclidean matrix operator and the
underlying matrix.  Applied to the realified complex Gram matrix, it identifies the
sum of the spectral weights with twice the complex Frobenius squared mass.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- The trace of the Euclidean linear operator represented by a matrix is exactly its
matrix trace.  This specializes `Matrix.trace_toLin_eq` to the standard orthonormal
`PiLp` basis used by `Matrix.toEuclideanLin`. -/
theorem trace_toEuclideanLin_eq_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    (LinearMap.trace ℝ (EuclideanSpace ℝ ι)) (Matrix.toEuclideanLin A) =
      A.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq A (EuclideanSpace.basisFun ι ℝ).toBasis

/-- The total eigenvalue weight of the positive real Gram operator is exactly twice
its source complex Frobenius squared mass.  This is the normalization required by the
Laplace-product lower-tail estimate. -/
theorem sum_eigenvalues_complexGramRealification {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) :
    let T := Matrix.toEuclideanLin (complexGramRealification Q)
    let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (Matrix.isHermitian_iff_isSymm.mpr (complexGramRealification_isSymm Q))
    let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) =
        Fintype.card (Fin N × Fin 2) := by simp
    ∑ k, hT.eigenvalues hdim k =
      2 * ∑ i : Fin N, ∑ j : Fin N, ‖Q i j‖ ^ 2 := by
  dsimp only
  let T := Matrix.toEuclideanLin (complexGramRealification Q)
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr (complexGramRealification_isSymm Q))
  let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) =
      Fintype.card (Fin N × Fin 2) := by simp
  calc
    (∑ k, hT.eigenvalues hdim k) =
        RCLike.re ((LinearMap.trace ℝ
          (EuclideanSpace ℝ (Fin N × Fin 2))) T) :=
      (hT.re_trace_eq_sum_eigenvalues hdim).symm
    _ = (complexGramRealification Q).trace := by
      exact trace_toEuclideanLin_eq_trace (complexGramRealification Q)
    _ = _ := trace_complexGramRealification Q

/-- Every spectral weight of the realified Gram operator is nonnegative. -/
theorem eigenvalues_complexGramRealification_nonneg {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) :
    let T := Matrix.toEuclideanLin (complexGramRealification Q)
    let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (Matrix.isHermitian_iff_isSymm.mpr (complexGramRealification_isSymm Q))
    let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) =
        Fintype.card (Fin N × Fin 2) := by simp
    ∀ k, 0 ≤ hT.eigenvalues hdim k := by
  dsimp only
  let R := complexMatrixRealification Q
  have hpsd : (complexGramRealification Q).PosSemidef := by
    simpa [complexGramRealification, R] using
      (Matrix.posSemidef_conjTranspose_mul_self R)
  have hpos : (Matrix.toEuclideanLin
      (complexGramRealification Q)).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hpsd
  intro k
  simpa using hpos.nonneg_eigenvalues (by simp) k

/-- Coordinate Frobenius mass is the squared norm of the flattened complex matrix in
exactly the `EuclideanSpace` appearing in the statement. -/
theorem norm_sq_matrix_vec_eq_sum {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) :
    ‖(WithLp.toLp 2 (Matrix.vec Q) :
      EuclideanSpace ℂ (Fin N × Fin N))‖ ^ 2 =
      ∑ i : Fin N, ∑ j : Fin N, ‖Q i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [Matrix.vec]
  rw [Finset.sum_comm]

/-- Realification is the coordinatewise canonical real isometry `ℂ ≃ ℝ²`,
followed by uncurrying the two finite coordinate indices. -/
def complexEuclideanRealification (N : ℕ) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : Fin N × Fin 2 => ℝ) :=
  let e : ℂ ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ) :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
  ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : Fin N => e).trans
      (LinearIsometryEquiv.piLpCurry (ι := Fin N) (κ := fun _ => Fin 2) ℝ 2
        (fun _ : Fin N => fun _ : Fin 2 => ℝ)).symm).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.sigmaEquivProd (Fin N) (Fin 2)))

/-- The abstract coordinatewise isometry has the expected real/imaginary
coordinate formula. -/
theorem complexEuclideanRealification_apply {N : ℕ}
    (z : EuclideanSpace ℂ (Fin N)) :
    complexEuclideanRealification N z =
      WithLp.toLp 2 (complexVectorRealification (WithLp.ofLp z)) := by
  ext p
  rcases p with ⟨i, k⟩
  fin_cases k <;>
    simp [complexEuclideanRealification, Complex.isometryOfOrthonormal_apply,
      Sigma.uncurry,
      complexVectorRealification]

/-- In the orthonormal eigenbasis of the real Gram operator, a complex
standard Gaussian has independent variance-one real coordinates. -/
theorem map_complexGramSpectralCoordinates_stdGaussian {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) :
    let T := Matrix.toEuclideanLin (complexGramRealification Q)
    let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (Matrix.isHermitian_iff_isSymm.mpr (complexGramRealification_isSymm Q))
    let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) =
        Fintype.card (Fin N × Fin 2) := by simp
    Measure.map
        (fun z : EuclideanSpace ℂ (Fin N) =>
          WithLp.ofLp ((hT.eigenvectorBasis hdim).repr
            (complexEuclideanRealification N z)))
        (stdGaussian (EuclideanSpace ℂ (Fin N))) =
      Measure.pi (fun _ : Fin (Fintype.card (Fin N × Fin 2)) =>
        gaussianReal 0 1) := by
  dsimp only
  let T := Matrix.toEuclideanLin (complexGramRealification Q)
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr (complexGramRealification_isSymm Q))
  let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) =
      Fintype.card (Fin N × Fin 2) := by simp
  let U : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (Fin N × Fin 2))) :=
    (complexEuclideanRealification N).trans
      (hT.eigenvectorBasis hdim).repr
  let μ := Measure.pi
    (fun _ : Fin (Fintype.card (Fin N × Fin 2)) => gaussianReal 0 1)
  have hU : Measure.map U (stdGaussian (EuclideanSpace ℂ (Fin N))) =
      stdGaussian
        (EuclideanSpace ℝ (Fin (Fintype.card (Fin N × Fin 2)))) :=
    stdGaussian_map U
  have hcoord : Measure.map WithLp.ofLp
      (stdGaussian
        (EuclideanSpace ℝ (Fin (Fintype.card (Fin N × Fin 2))))) = μ := by
    have hto : Measure.map (WithLp.toLp 2) μ =
        stdGaussian
          (EuclideanSpace ℝ (Fin (Fintype.card (Fin N × Fin 2)))) :=
      map_pi_eq_stdGaussian
    rw [← hto, Measure.map_map]
    · rw [show WithLp.ofLp ∘ (WithLp.toLp 2) = id by
        funext g
        rfl]
      exact Measure.map_id
    · fun_prop
    · fun_prop
  change Measure.map (fun z => WithLp.ofLp (U z))
      (stdGaussian (EuclideanSpace ℂ (Fin N))) = μ
  calc
    _ = Measure.map WithLp.ofLp
        (Measure.map U (stdGaussian (EuclideanSpace ℂ (Fin N)))) := by
      rw [Measure.map_map]
      · rfl
      · fun_prop
      · fun_prop
    _ = μ := by rw [hU, hcoord]

/-- Elementary finite-product lower bound used to collapse the full spectral
Laplace product to the total eigenvalue mass. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    1 + ∑ i, u i ≤ ∏ i, (1 + u i) := by
  classical
  suffices ∀ s : Finset ι, 1 + ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 + u i) by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hs : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg fun i _ => hu i
      calc
        1 + (u a + ∑ i ∈ s, u i)
            ≤ (1 + u a) * (1 + ∑ i ∈ s, u i) := by
              nlinarith [hu a]
        _ ≤ (1 + u a) * ∏ i ∈ s, (1 + u i) :=
          mul_le_mul_of_nonneg_left ih (add_nonneg zero_le_one (hu a))

end PSSSNative.BlockBand.PSSS
