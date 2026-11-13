module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WeightedSquaresLaw
public import BlockBand.Model.Construction.OrderedCourantFischer

/-!
# Orthogonal invariance of the finite standard Gaussian law

This module supplies the law-level change of coordinates used before the APSSS
weighted-square argument.  The measure is the finite product of the
one-dimensional `gaussianReal 0 1` laws.  Invariance is deduced from Mathlib's
proved invariance of `stdGaussian`; no distributional certificate is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

/-- The ordinary-coordinate action of a real orthogonal equivalence. -/
def orthogonalCoordinateChange {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (g : Fin n → ℝ) : Fin n → ℝ :=
  WithLp.ofLp (U (WithLp.toLp 2 g))

/-- Orthogonal coordinate changes are Borel measurable. -/
theorem measurable_orthogonalCoordinateChange {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Measurable (orthogonalCoordinateChange U) := by
  unfold orthogonalCoordinateChange
  fun_prop

/-- Exact pushforward invariance of the finite product standard-Gaussian law
under every real orthogonal coordinate change. -/
theorem map_pi_gaussianReal_orthogonalCoordinateChange {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Measure.map (orthogonalCoordinateChange U)
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let μ : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  have hto : Measure.map (WithLp.toLp 2) μ =
      stdGaussian (EuclideanSpace ℝ (Fin n)) :=
    map_pi_eq_stdGaussian
  have hU : Measure.map U (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) :=
    stdGaussian_map U
  have hof : Measure.map WithLp.ofLp
      (stdGaussian (EuclideanSpace ℝ (Fin n))) = μ := by
    rw [← hto, Measure.map_map]
    · rw [show WithLp.ofLp ∘ (WithLp.toLp 2) = id by
        funext g
        rfl]
      exact Measure.map_id
    · fun_prop
    · fun_prop
  change Measure.map (fun g => WithLp.ofLp (U (WithLp.toLp 2 g))) μ = μ
  calc
    Measure.map (fun g => WithLp.ofLp (U (WithLp.toLp 2 g))) μ =
        Measure.map WithLp.ofLp
          (Measure.map U (Measure.map (WithLp.toLp 2) μ)) := by
      rw [Measure.map_map, Measure.map_map]
      · rfl
      all_goals fun_prop
    _ = μ := by rw [hto, hU, hof]

/-- The dimension equality used to index the spectral basis by the original
`Fin n` coordinate type. -/
theorem finrank_euclideanFin (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
  simp

/-- Spectral coordinates of a real self-adjoint operator. -/
def symmetricSpectralCoordinateChange {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  orthogonalCoordinateChange
    (hT.eigenvectorBasis (finrank_euclideanFin n)).repr

/-- The spectral coordinate change of a real self-adjoint operator preserves
the finite product standard-Gaussian law. -/
theorem map_pi_gaussianReal_symmetricSpectralCoordinateChange {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) :
    Measure.map (symmetricSpectralCoordinateChange hT)
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) :=
  map_pi_gaussianReal_orthogonalCoordinateChange _

/-- The shift expressed in the orthonormal eigenbasis of a real self-adjoint
operator. -/
def symmetricSpectralShift {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ :=
  fun j => (hT.eigenvectorBasis (finrank_euclideanFin n)).repr b j

/-- The APSSS pair before changing to spectral coordinates.  The first
component is the spectral tail of `‖T(x+b)‖²`; the second is the
translated quadratic form. -/
def symmetricSpectralWeightedSquaresRandomVector {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b : EuclideanSpace ℝ (Fin n))
    (r : ℕ) (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ × ℝ :=
  (∑ j : Fin n, if r ≤ (j : ℕ) then
      (hT.eigenvalues (finrank_euclideanFin n) j) ^ 2 *
        ((hT.eigenvectorBasis (finrank_euclideanFin n)).repr (x + b) j) ^ 2
    else 0,
   inner ℝ (T (x + b)) (x + b) - a)

/-- Spectral diagonalization identifies the quadratic-form pair
pointwise with the diagonal weighted-square pair. -/
theorem symmetricSpectralWeightedSquaresRandomVector_eq {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b : EuclideanSpace ℝ (Fin n))
    (r : ℕ) (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    symmetricSpectralWeightedSquaresRandomVector hT b r a x =
      weightedSquaresRandomVector
        (hT.eigenvalues (finrank_euclideanFin n))
        (symmetricSpectralShift hT b) r a
        (WithLp.ofLp
          ((hT.eigenvectorBasis (finrank_euclideanFin n)).repr x)) := by
  apply Prod.ext
  · unfold symmetricSpectralWeightedSquaresRandomVector
      weightedSquaresRandomVector tailQuadraticRatioEnergy
      symmetricSpectralShift
    change (∑ j : Fin n, if r ≤ (j : ℕ) then
      (hT.eigenvalues (finrank_euclideanFin n) j) ^ 2 *
        ((hT.eigenvectorBasis (finrank_euclideanFin n)).repr (x + b) j) ^ 2
      else 0) = _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : r ≤ (j : ℕ)
    · simp only [hj, ↓reduceIte]
      rw [map_add]
      rfl
    · simp [hj]
  · unfold symmetricSpectralWeightedSquaresRandomVector
      weightedSquaresRandomVector quadraticRatioValue symmetricSpectralShift
    change inner ℝ (T (x + b)) (x + b) - a = _
    have hdiag :
        inner ℝ (T (x + b)) (x + b) =
          ∑ j : Fin n, hT.eigenvalues (finrank_euclideanFin n) j *
            ‖(hT.eigenvectorBasis (finrank_euclideanFin n)).repr (x + b) j‖ ^ 2 := by
      simpa using hT.re_inner_apply_self_eq_sum_eigenvalues_mul_sq
        (finrank_euclideanFin n) (x + b)
    rw [hdiag]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [map_add]
    simp only [PiLp.add_apply, Real.norm_eq_abs, sq_abs]

/-- The spectral quadratic-form pair is measurable in the original
Euclidean coordinate vector. -/
theorem measurable_symmetricSpectralWeightedSquaresRandomVector {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b : EuclideanSpace ℝ (Fin n))
    (r : ℕ) (a : ℝ) :
    Measurable (symmetricSpectralWeightedSquaresRandomVector hT b r a) := by
  unfold symmetricSpectralWeightedSquaresRandomVector
  fun_prop

/-- Law-level spectral adapter: under the original product Gaussian
coordinates, the self-adjoint quadratic-form pair has exactly the same
pushforward law as the diagonal APSSS weighted-square pair with eigenvalue
weights and the spectrally transformed shift. -/
theorem map_symmetricSpectralWeightedSquares_eq_map_weightedSquares {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b : EuclideanSpace ℝ (Fin n))
    (r : ℕ) (a : ℝ) :
    Measure.map
        (fun g : Fin n → ℝ =>
          symmetricSpectralWeightedSquaresRandomVector hT b r a
            (WithLp.toLp 2 g))
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      Measure.map
        (weightedSquaresRandomVector
          (hT.eigenvalues (finrank_euclideanFin n))
          (symmetricSpectralShift hT b) r a)
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  let μ : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let W := weightedSquaresRandomVector
    (hT.eigenvalues (finrank_euclideanFin n))
    (symmetricSpectralShift hT b) r a
  let U := symmetricSpectralCoordinateChange hT
  have hU : Measurable U := measurable_orthogonalCoordinateChange _
  have hW : Measurable W :=
    measurable_weightedSquaresRandomVector _ _ _ _
  calc
    Measure.map
        (fun g : Fin n → ℝ =>
          symmetricSpectralWeightedSquaresRandomVector hT b r a
            (WithLp.toLp 2 g)) μ =
        Measure.map (W ∘ U) μ := by
      congr 1
      funext g
      exact symmetricSpectralWeightedSquaresRandomVector_eq
        hT b r a (WithLp.toLp 2 g)
    _ = Measure.map W (Measure.map U μ) := by
      rw [Measure.map_map hW hU]
    _ = Measure.map W μ := by
      rw [show Measure.map U μ = μ from
        map_pi_gaussianReal_symmetricSpectralCoordinateChange hT]

/-- Event-probability form of the spectral adapter, ready for the APSSS ratio
event in `ℝ × ℝ`. -/
theorem measure_symmetricSpectralWeightedSquares_preimage_eq {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b : EuclideanSpace ℝ (Fin n))
    (r : ℕ) (a : ℝ) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        ((fun g : Fin n → ℝ =>
          symmetricSpectralWeightedSquaresRandomVector hT b r a
            (WithLp.toLp 2 g)) ⁻¹' s) =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        ((weightedSquaresRandomVector
          (hT.eigenvalues (finrank_euclideanFin n))
          (symmetricSpectralShift hT b) r a) ⁻¹' s) := by
  let μ : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let X := fun g : Fin n → ℝ =>
    symmetricSpectralWeightedSquaresRandomVector hT b r a
      (WithLp.toLp 2 g)
  let W := weightedSquaresRandomVector
    (hT.eigenvalues (finrank_euclideanFin n))
    (symmetricSpectralShift hT b) r a
  have hX : Measurable X := by
    dsimp only [X]
    exact (measurable_symmetricSpectralWeightedSquaresRandomVector
      hT b r a).comp (by fun_prop)
  have hW : Measurable W :=
    measurable_weightedSquaresRandomVector _ _ _ _
  rw [← Measure.map_apply_of_aemeasurable hX.aemeasurable hs,
    ← Measure.map_apply_of_aemeasurable hW.aemeasurable hs]
  exact congrArg (fun ν : Measure (ℝ × ℝ) => ν s)
    (map_symmetricSpectralWeightedSquares_eq_map_weightedSquares hT b r a)

end PSSSNative.BlockBand.PSSS
