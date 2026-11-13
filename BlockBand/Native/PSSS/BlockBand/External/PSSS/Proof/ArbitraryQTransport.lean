module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.OrderedProbabilityExtraction

/-!
# Transport of the ordered diagonal ratio bound to arbitrary symmetric matrices

This module closes the finite-dimensional spectral transport in the APSSS
quadratic-ratio estimate.  A real symmetric matrix is converted to its
self-adjoint Euclidean linear map, diagonalized in an orthonormal eigenbasis,
and its coefficients are permuted by decreasing shifted coefficient energy.
The existing product-Gaussian orthogonal and permutation invariance theorems
then identify the original matrix event with the ordered diagonal event.

The constant is absolute and is chosen before the dimension and all matrix,
shift, center, and tail parameters.  The zero-dimensional case is discharged
from `Q ≠ 0`, rather than padded by a fictitious coordinate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix

/-- The explicit real constant used in the matrix-facing theorem.  The
maximum with one supplies the required normalization without changing any
parameter dependence. -/
def quadraticRatioTailConstant : ℝ :=
  max 1 orderedQuadraticRatioProbabilityConstant.toReal

/-- The ordered diagonal probability constant is finite.  Ultimately this is
the finiteness of the scalar `3/4` kernel integral. -/
theorem orderedQuadraticRatioProbabilityConstant_ne_top :
    orderedQuadraticRatioProbabilityConstant ≠ ⊤ := by
  unfold orderedQuadraticRatioProbabilityConstant orderedTailProbabilityConstant
    shiftedIntegralAbsoluteConstant
  apply ENNReal.Finiteness.add_ne_top ENNReal.ofReal_ne_top
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ENNReal.mul_ne_top
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.pow_ne_top threeQuarterKernelConstant_ne_top

/-- The real constant dominates the exact ENNReal constant produced by
the ordered Fourier and low-rank analysis. -/
theorem orderedQuadraticRatioProbabilityConstant_le_ofReal :
    orderedQuadraticRatioProbabilityConstant ≤
      ENNReal.ofReal quadraticRatioTailConstant := by
  rw [← ENNReal.ofReal_toReal orderedQuadraticRatioProbabilityConstant_ne_top]
  exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- The real constant is at least one. -/
theorem one_le_quadraticRatioTailConstant :
    1 ≤ quadraticRatioTailConstant :=
  le_max_left _ _

/-- A nonzero real symmetric matrix has a nonzero eigenvalue in the exact
ordered-eigenvalue family used by the Euclidean spectral adapter. -/
theorem exists_symmetric_eigenvalue_ne_zero {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm) (hQ0 : Q ≠ 0) :
    let T := Matrix.toEuclideanLin Q
    let hT : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (Matrix.isHermitian_iff_isSymm.mpr hQ)
    ∃ j : Fin n, hT.eigenvalues (finrank_euclideanFin n) j ≠ 0 := by
  dsimp only
  let T := Matrix.toEuclideanLin Q
  let hT : T.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (Matrix.isHermitian_iff_isSymm.mpr hQ)
  by_contra h
  push Not at h
  have hTzero : T = 0 := (hT.inner_map_self_eq_zero).mp (by
    intro x
    have hdiag := hT.re_inner_apply_self_eq_sum_eigenvalues_mul_sq
      (finrank_euclideanFin n) x
    change RCLike.re (inner ℝ (T x) x) = 0
    rw [hdiag]
    simp [h])
  have hQzero : Q = 0 := Matrix.toEuclideanLin.map_eq_zero_iff.mp hTzero
  exact hQ0 hQzero

/-- After the canonical energy permutation, a nonzero symmetric matrix still
has at least one active diagonal coefficient. -/
theorem ordered_spectral_active_card_pos {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm) (hQ0 : Q ≠ 0)
    (b : Fin n → ℝ) :
    let T := Matrix.toEuclideanLin Q
    let hT : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (Matrix.isHermitian_iff_isSymm.mpr hQ)
    let E := hT.eigenvalues (finrank_euclideanFin n)
    let bs := symmetricSpectralShift hT (WithLp.toLp 2 b)
    let σ := dominantEnergyPermutation E bs
    0 < (Finset.univ.filter fun j : Fin n =>
      permuteFinCoordinates σ E j ≠ 0).card := by
  dsimp only
  obtain ⟨j, hj⟩ := exists_symmetric_eigenvalue_ne_zero Q hQ hQ0
  apply Finset.card_pos.mpr
  refine ⟨(dominantEnergyPermutation
    ((Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (Matrix.isHermitian_iff_isSymm.mpr hQ)).eigenvalues
        (finrank_euclideanFin n))
    (symmetricSpectralShift
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (Matrix.isHermitian_iff_isSymm.mpr hQ))
      (WithLp.toLp 2 b))).symm j, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_univ _
  · unfold permuteFinCoordinates
    rw [Equiv.apply_symm_apply]
    exact hj

/-- The canonical simultaneous permutation makes the coefficient energy of
the diagonalized matrix antitone, in precisely the form consumed by the
ordered diagonal probability theorem. -/
theorem ordered_spectral_coefficientEnergy_antitone {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (b : Fin n → ℝ) :
    let T := Matrix.toEuclideanLin Q
    let hT : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (Matrix.isHermitian_iff_isSymm.mpr hQ)
    let E := hT.eigenvalues (finrank_euclideanFin n)
    let bs := symmetricSpectralShift hT (WithLp.toLp 2 b)
    let σ := dominantEnergyPermutation E bs
    Antitone (fun j : Fin n =>
      coefficientEnergy (permuteFinCoordinates σ E)
        (permuteFinCoordinates σ bs) j) := by
  dsimp only
  simpa [coefficientEnergy, permuteFinCoordinates] using
    antitone_coefficientEnergy_dominantEnergyPermutation
      ((Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (Matrix.isHermitian_iff_isSymm.mpr hQ)).eigenvalues
          (finrank_euclideanFin n))
      (symmetricSpectralShift
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr
          (Matrix.isHermitian_iff_isSymm.mpr hQ))
        (WithLp.toLp 2 b))

/-- APSSS quadratic-ratio tail bound for an arbitrary nonzero real symmetric
matrix.  This is the multiplicative-event statement: one absolute
constant precedes all data; the product Gaussian has variance one in every
coordinate; and the estimate is uniform for every `t ≥ 1`. -/
theorem quadraticRatio_tail :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ), Q.IsSymm → Q ≠ 0 →
      ∀ (b : Fin n → ℝ) (a t : ℝ), 1 ≤ t →
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)
        {g | t * |dotProduct (g + b) (Q *ᵥ (g + b)) - a| ≤
          ‖(WithLp.toLp 2 (Q *ᵥ (g + b)) : EuclideanSpace ℝ (Fin n))‖} ≤
        ENNReal.ofReal (C / t) := by
  refine ⟨quadraticRatioTailConstant, one_le_quadraticRatioTailConstant, ?_⟩
  intro n Q hQ hQ0 b a t ht
  cases n with
  | zero =>
      exfalso
      exact hQ0 (Subsingleton.elim Q 0)
  | succ m =>
      let T := Matrix.toEuclideanLin Q
      let hT : T.IsSymmetric :=
        Matrix.isSymmetric_toEuclideanLin_iff.mpr
          (Matrix.isHermitian_iff_isSymm.mpr hQ)
      let E := hT.eigenvalues (finrank_euclideanFin (m + 1))
      let bs := symmetricSpectralShift hT (WithLp.toLp 2 b)
      let σ := dominantEnergyPermutation E bs
      let Eo := permuteFinCoordinates σ E
      let bo := permuteFinCoordinates σ bs
      have hord : Antitone (fun j : Fin (m + 1) =>
          coefficientEnergy Eo bo j) := by
        simpa [T, hT, E, bs, σ, Eo, bo] using
          ordered_spectral_coefficientEnergy_antitone Q hQ b
      have hactive : 0 <
          (Finset.univ.filter fun j : Fin (m + 1) => Eo j ≠ 0).card := by
        simpa [T, hT, E, bs, σ, Eo] using
          ordered_spectral_active_card_pos Q hQ hQ0 b
      have hdiag := measure_ordered_weightedSquares_multiplicativeEvent_le
        Eo bo hord hactive a t ht
      rw [show {g : Fin (m + 1) → ℝ |
          t * |dotProduct (g + b) (Q *ᵥ (g + b)) - a| ≤
            ‖(WithLp.toLp 2 (Q *ᵥ (g + b)) :
              EuclideanSpace ℝ (Fin (m + 1)))‖} =
          matrixQuadraticRatioEvent Q b a t by rfl]
      rw [measure_matrixQuadraticRatioEvent_eq_orderedWeightedSquares Q hQ b a t]
      calc
        (Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1)
            ((weightedSquaresRandomVector Eo bo 0 a) ⁻¹'
              multiplicativeRatioPairEvent t) ≤
          orderedQuadraticRatioProbabilityConstant / ENNReal.ofReal t := hdiag
        _ ≤ ENNReal.ofReal quadraticRatioTailConstant / ENNReal.ofReal t := by
          gcongr
          exact orderedQuadraticRatioProbabilityConstant_le_ofReal
        _ = ENNReal.ofReal (quadraticRatioTailConstant / t) := by
          rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < t)]

end PSSSNative.BlockBand.PSSS
