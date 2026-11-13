module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GaussianOrthogonalInvariance
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Spectral coordinates for the APSSS quadratic ratio

APSSS refers to Aizenman–Peled–Schenker–Shamis–Sodin.

For a self-adjoint operator `T` and a shift `b`, the event `t |⟪T(x+b), x+b⟫ - a| ≤ ‖T(x+b)‖` has,
under the standard Gaussian, the same probability as the corresponding diagonal weighted-squares
event in spectral coordinates, ordered so that the dominant coefficient energies come first. The
norm `‖T(x+b)‖` is split into at most two dominant rank-one terms plus a tail energy.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal InnerProductSpace Matrix

/-- The squared norm of a self-adjoint image is the full eigenvalue-square
energy in its orthonormal eigenbasis. -/
theorem sq_norm_eq_quadraticRatioEnergy_spectral {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b x : EuclideanSpace ℝ (Fin n)) :
    ‖T (x + b)‖ ^ 2 =
      quadraticRatioEnergy
        (hT.eigenvalues (finrank_euclideanFin n))
        (symmetricSpectralShift hT b)
        (WithLp.ofLp
          ((hT.eigenvectorBasis (finrank_euclideanFin n)).repr x)) := by
  rw [LinearMap.sq_norm_apply_eq_sum_of_eigenbasis T
    (hT.eigenvectorBasis (finrank_euclideanFin n))
    (hT.apply_eigenvectorBasis (finrank_euclideanFin n)) (x + b)]
  unfold quadraticRatioEnergy symmetricSpectralShift
  apply Finset.sum_congr rfl
  intro j _
  rw [map_add]
  simp only [PiLp.add_apply, Real.norm_eq_abs, sq_abs]
  rfl

/-- Consequently the norm itself is the square root of the full spectral
energy, with no sign or normalization loss. -/
theorem norm_eq_sqrt_quadraticRatioEnergy_spectral {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b x : EuclideanSpace ℝ (Fin n)) :
    ‖T (x + b)‖ =
      Real.sqrt (quadraticRatioEnergy
        (hT.eigenvalues (finrank_euclideanFin n))
        (symmetricSpectralShift hT b)
        (WithLp.ofLp
          ((hT.eigenvectorBasis (finrank_euclideanFin n)).repr x))) := by
  rw [← sq_norm_eq_quadraticRatioEnergy_spectral hT b x]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- The canonical APSSS ordering permutation: sort the negative coefficient
energies, hence put the largest `E_j²(1+b_j²)` first. -/
def dominantEnergyPermutation {n : ℕ} (E b : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun j => -coefficientEnergy E b j)

/-- Under the canonical permutation the coefficient energies are antitone, so
the first `r` coordinates are precisely the dominant rank-one terms. -/
theorem antitone_coefficientEnergy_dominantEnergyPermutation {n : ℕ}
    (E b : Fin n → ℝ) :
    Antitone (fun j => coefficientEnergy E b (dominantEnergyPermutation E b j)) := by
  have hmono := Tuple.monotone_sort (fun j : Fin n => -coefficientEnergy E b j)
  intro i j hij
  have h := hmono hij
  dsimp [dominantEnergyPermutation] at h ⊢
  linarith

/-- Simultaneously reindex weights, shifts, and Gaussian coordinates by a
permutation. -/
def permuteFinCoordinates {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x (σ j)

/-- The full squared numerator is unchanged by simultaneous coordinate
permutation. -/
theorem quadraticRatioEnergy_permuteFinCoordinates {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (E b g : Fin n → ℝ) :
    quadraticRatioEnergy (permuteFinCoordinates σ E)
        (permuteFinCoordinates σ b) (permuteFinCoordinates σ g) =
      quadraticRatioEnergy E b g := by
  unfold quadraticRatioEnergy permuteFinCoordinates
  simpa using σ.sum_comp Finset.univ
    (fun j => E j ^ 2 * (g j + b j) ^ 2) (by simp)

/-- The quadratic denominator is likewise unchanged by simultaneous
coordinate permutation. -/
theorem quadraticRatioValue_permuteFinCoordinates {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (E b g : Fin n → ℝ) :
    quadraticRatioValue (permuteFinCoordinates σ E)
        (permuteFinCoordinates σ b) (permuteFinCoordinates σ g) =
      quadraticRatioValue E b g := by
  unfold quadraticRatioValue permuteFinCoordinates
  simpa using σ.sum_comp Finset.univ
    (fun j => E j * (g j + b j) ^ 2) (by simp)

/-- At split rank zero the APSSS tail energy is the entire squared
numerator. -/
theorem tailQuadraticRatioEnergy_zero {n : ℕ} (E b g : Fin n → ℝ) :
    tailQuadraticRatioEnergy E b 0 g = quadraticRatioEnergy E b g := by
  unfold tailQuadraticRatioEnergy quadraticRatioEnergy
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- The measurable multiplicative event `t |q| ≤ √p` on the joint square
variables `(p, q)`.  Unlike a quotient formulation, it contains every point
with vanishing denominator `q = 0`.
-/
def multiplicativeRatioPairEvent (t : ℝ) : Set (ℝ × ℝ) :=
  {p | t * |p.2| ≤ Real.sqrt p.1}

/-- The multiplicative pair event is Borel measurable. -/
theorem measurableSet_multiplicativeRatioPairEvent (t : ℝ) :
    MeasurableSet (multiplicativeRatioPairEvent t) := by
  unfold multiplicativeRatioPairEvent
  measurability

/-- At rank zero the entire weighted-square pair is invariant under
simultaneous permutation of coefficients, shifts, and coordinates. -/
theorem weightedSquaresRandomVector_zero_permuteFinCoordinates {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (E b g : Fin n → ℝ) (a : ℝ) :
    weightedSquaresRandomVector
        (permuteFinCoordinates σ E) (permuteFinCoordinates σ b) 0 a
        (permuteFinCoordinates σ g) =
      weightedSquaresRandomVector E b 0 a g := by
  apply Prod.ext
  · simp only [weightedSquaresRandomVector, tailQuadraticRatioEnergy_zero]
    exact quadraticRatioEnergy_permuteFinCoordinates σ E b g
  · simp only [weightedSquaresRandomVector]
    rw [quadraticRatioValue_permuteFinCoordinates]

/-- A coordinate permutation preserves the finite product Gaussian
law.  This is the permutation specialization of orthogonal invariance. -/
theorem map_pi_gaussianReal_permuteFinCoordinates {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    Measure.map (permuteFinCoordinates σ)
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ.symm
  have hU := map_pi_gaussianReal_orthogonalCoordinateChange U
  have hfun : permuteFinCoordinates σ = orthogonalCoordinateChange U := by
    funext g
    ext j
    rfl
  rw [hfun]
  exact hU

/-- Hence every measurable event has the same probability after a coordinate
permutation. -/
theorem measure_preimage_permuteFinCoordinates {n : ℕ}
    (σ : Equiv.Perm (Fin n)) {s : Set (Fin n → ℝ)}
    (hs : NullMeasurableSet s
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        (permuteFinCoordinates σ ⁻¹' s) =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) s := by
  exact (⟨by
    unfold permuteFinCoordinates
    fun_prop,
    map_pi_gaussianReal_permuteFinCoordinates σ⟩ :
      MeasurePreserving (permuteFinCoordinates σ)
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1))).measure_preimage hs

/-- In particular, the measurable rank-zero multiplicative event may be
reordered by the canonical dominant-energy permutation without changing its
probability. -/
theorem measure_weightedSquares_zero_preimage_permute_eq {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (E b : Fin n → ℝ) (a t : ℝ) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        ((weightedSquaresRandomVector
          (permuteFinCoordinates σ E) (permuteFinCoordinates σ b) 0 a) ⁻¹'
            multiplicativeRatioPairEvent t) =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        ((weightedSquaresRandomVector E b 0 a) ⁻¹'
          multiplicativeRatioPairEvent t) := by
  let s :=
    (weightedSquaresRandomVector
      (permuteFinCoordinates σ E) (permuteFinCoordinates σ b) 0 a) ⁻¹'
        multiplicativeRatioPairEvent t
  have hs : MeasurableSet s :=
    (measurable_weightedSquaresRandomVector _ _ 0 a)
      (measurableSet_multiplicativeRatioPairEvent t)
  rw [← measure_preimage_permuteFinCoordinates σ hs.nullMeasurableSet]
  congr 1
  ext g
  change weightedSquaresRandomVector
      (permuteFinCoordinates σ E) (permuteFinCoordinates σ b) 0 a
        (permuteFinCoordinates σ g) ∈ multiplicativeRatioPairEvent t ↔
    weightedSquaresRandomVector E b 0 a g ∈ multiplicativeRatioPairEvent t
  rw [weightedSquaresRandomVector_zero_permuteFinCoordinates]

/-- After the canonical energy permutation, the physical numerator splits
into the first `r` dominant rank-one terms and the corresponding
reindexed tail. -/
theorem norm_le_orderedSpectralDominant_add_tail {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b x : EuclideanSpace ℝ (Fin n)) (r : ℕ) :
    let E := hT.eigenvalues (finrank_euclideanFin n)
    let bs := symmetricSpectralShift hT b
    let gs := WithLp.ofLp
      ((hT.eigenvectorBasis (finrank_euclideanFin n)).repr x)
    let σ := dominantEnergyPermutation E bs
    ‖T (x + b)‖ ≤
      (∑ j : Fin n, if (j : ℕ) < r then
        |permuteFinCoordinates σ E j| *
          |permuteFinCoordinates σ gs j + permuteFinCoordinates σ bs j|
        else 0) +
      Real.sqrt (tailQuadraticRatioEnergy
        (permuteFinCoordinates σ E) (permuteFinCoordinates σ bs) r
        (permuteFinCoordinates σ gs)) := by
  dsimp only
  rw [norm_eq_sqrt_quadraticRatioEnergy_spectral hT b x]
  rw [← quadraticRatioEnergy_permuteFinCoordinates
    (dominantEnergyPermutation
      (hT.eigenvalues (finrank_euclideanFin n))
      (symmetricSpectralShift hT b))]
  exact sqrt_quadraticRatioEnergy_le_dominant_add_tail _ _ _ r

/-- The specialization used in APSSS: at most two canonically ordered
rank-one terms are removed, and every remaining term belongs to the tail
energy. -/
theorem norm_le_two_orderedSpectralDominant_add_tail {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b x : EuclideanSpace ℝ (Fin n)) :
    let E := hT.eigenvalues (finrank_euclideanFin n)
    let bs := symmetricSpectralShift hT b
    let gs := WithLp.ofLp
      ((hT.eigenvectorBasis (finrank_euclideanFin n)).repr x)
    let σ := dominantEnergyPermutation E bs
    ‖T (x + b)‖ ≤
      (∑ j : Fin n, if (j : ℕ) < 2 then
        |permuteFinCoordinates σ E j| *
          |permuteFinCoordinates σ gs j + permuteFinCoordinates σ bs j|
        else 0) +
      Real.sqrt (tailQuadraticRatioEnergy
        (permuteFinCoordinates σ E) (permuteFinCoordinates σ bs) 2
        (permuteFinCoordinates σ gs)) :=
  norm_le_orderedSpectralDominant_add_tail hT b x 2

/-- The matrix event in the `quadraticRatio_tail` signature. -/
def matrixQuadraticRatioEvent {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (a t : ℝ) : Set (Fin n → ℝ) :=
  {g | t * |dotProduct (g + b) (Q *ᵥ (g + b)) - a| ≤
    ‖(WithLp.toLp 2 (Q *ᵥ (g + b)) : EuclideanSpace ℝ (Fin n))‖}

/-- The multiplicative quadratic-ratio event for a self-adjoint operator,
before changing to spectral coordinates. -/
def symmetricQuadraticRatioEvent {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (b : EuclideanSpace ℝ (Fin n)) (a t : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | t * |inner ℝ (T (x + b)) (x + b) - a| ≤ ‖T (x + b)‖}

/-- The self-adjoint event is exactly the inverse image of the
measurable multiplicative pair event under the rank-zero spectral pair. -/
theorem symmetricQuadraticRatioEvent_eq_preimage {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b : EuclideanSpace ℝ (Fin n)) (a t : ℝ) :
    symmetricQuadraticRatioEvent (T := T) b a t =
      symmetricSpectralWeightedSquaresRandomVector hT b 0 a ⁻¹'
        multiplicativeRatioPairEvent t := by
  ext x
  unfold symmetricQuadraticRatioEvent multiplicativeRatioPairEvent
    symmetricSpectralWeightedSquaresRandomVector
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [show (∑ j : Fin n, if 0 ≤ (j : ℕ) then
      (hT.eigenvalues (finrank_euclideanFin n) j) ^ 2 *
        ((hT.eigenvectorBasis (finrank_euclideanFin n)).repr (x + b) j) ^ 2
      else 0) =
      quadraticRatioEnergy
        (hT.eigenvalues (finrank_euclideanFin n))
        (symmetricSpectralShift hT b)
        (WithLp.ofLp
          ((hT.eigenvectorBasis (finrank_euclideanFin n)).repr x)) by
    rw [← tailQuadraticRatioEnergy_zero]
    exact congrArg Prod.fst
      (symmetricSpectralWeightedSquaresRandomVector_eq hT b 0 a x)]
  rw [← norm_eq_sqrt_quadraticRatioEnergy_spectral hT b x]

/-- The self-adjoint multiplicative event has the same Gaussian probability as the diagonal
weighted-squares event. -/
theorem measure_symmetricQuadraticRatioEvent_eq_weightedSquares {n : ℕ}
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsSymmetric) (b : EuclideanSpace ℝ (Fin n)) (a t : ℝ) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        ((fun g : Fin n → ℝ => WithLp.toLp 2 g) ⁻¹'
          symmetricQuadraticRatioEvent (T := T) b a t) =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        ((weightedSquaresRandomVector
          (hT.eigenvalues (finrank_euclideanFin n))
          (symmetricSpectralShift hT b) 0 a) ⁻¹'
            multiplicativeRatioPairEvent t) := by
  rw [symmetricQuadraticRatioEvent_eq_preimage hT b a t]
  exact measure_symmetricSpectralWeightedSquares_preimage_eq hT b 0 a
    (measurableSet_multiplicativeRatioPairEvent t)

/-- A real symmetric matrix event is the corresponding
self-adjoint Euclidean-operator event.
This theorem records all `WithLp`
normalizations used in `matrixQuadraticRatioEvent`.
-/
theorem matrixQuadraticRatioEvent_eq_symmetric_preimage {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (a t : ℝ) :
    let T := Matrix.toEuclideanLin Q
    matrixQuadraticRatioEvent Q b a t =
      (fun g : Fin n → ℝ => WithLp.toLp 2 g) ⁻¹'
        symmetricQuadraticRatioEvent (T := T) (WithLp.toLp 2 b) a t := by
  dsimp only
  ext g
  unfold matrixQuadraticRatioEvent symmetricQuadraticRatioEvent
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have happly :
      Matrix.toEuclideanLin Q (WithLp.toLp 2 (g + b)) =
        WithLp.toLp 2 (Q *ᵥ (g + b)) := by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.toEuclideanCLM_toLp Q (g + b)
  have hinner :
      inner ℝ
          (Matrix.toEuclideanLin Q (WithLp.toLp 2 (g + b)))
          (WithLp.toLp 2 (g + b)) =
        dotProduct (g + b) (Q *ᵥ (g + b)) := by
    rw [real_inner_comm]
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.inner_toEuclideanCLM Q
      (WithLp.toLp 2 (g + b)) (WithLp.toLp 2 (g + b))
  have hinner' :
      inner ℝ
          (WithLp.toLp 2 (Q *ᵥ (g + b)))
          (WithLp.toLp 2 (g + b)) =
        dotProduct (g + b) (Q *ᵥ (g + b)) := by
    rw [← happly]
    exact hinner
  rw [show WithLp.toLp 2 g + WithLp.toLp 2 b =
      WithLp.toLp 2 (g + b) by rfl]
  rw [happly, hinner']

/-- Probability adapter: a symmetric matrix
quadratic-ratio event has exactly the law of the rank-zero diagonal
weighted-square event in its orthonormal eigenbasis.
-/
theorem measure_matrixQuadraticRatioEvent_eq_weightedSquares {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (b : Fin n → ℝ) (a t : ℝ) :
    let T := Matrix.toEuclideanLin Q
    let hT : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (Matrix.isHermitian_iff_isSymm.mpr hQ)
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        (matrixQuadraticRatioEvent Q b a t) =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        ((weightedSquaresRandomVector
          (hT.eigenvalues (finrank_euclideanFin n))
          (symmetricSpectralShift hT (WithLp.toLp 2 b)) 0 a) ⁻¹'
            multiplicativeRatioPairEvent t) := by
  dsimp only
  rw [matrixQuadraticRatioEvent_eq_symmetric_preimage Q b a t]
  exact measure_symmetricQuadraticRatioEvent_eq_weightedSquares
    _ (WithLp.toLp 2 b) a t

/-- Ordered adapter for `matrixQuadraticRatioEvent`: after diagonalization its
probability is the rank-zero weighted-square probability with coefficients
placed in decreasing coefficient-energy order.
The same ordering is used by
`norm_le_two_orderedSpectralDominant_add_tail`.
-/
theorem measure_matrixQuadraticRatioEvent_eq_orderedWeightedSquares {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (b : Fin n → ℝ) (a t : ℝ) :
    let T := Matrix.toEuclideanLin Q
    let hT : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (Matrix.isHermitian_iff_isSymm.mpr hQ)
    let E := hT.eigenvalues (finrank_euclideanFin n)
    let bs := symmetricSpectralShift hT (WithLp.toLp 2 b)
    let σ := dominantEnergyPermutation E bs
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        (matrixQuadraticRatioEvent Q b a t) =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        ((weightedSquaresRandomVector
          (permuteFinCoordinates σ E) (permuteFinCoordinates σ bs) 0 a) ⁻¹'
            multiplicativeRatioPairEvent t) := by
  dsimp only
  rw [measure_matrixQuadraticRatioEvent_eq_weightedSquares Q hQ b a t]
  exact (measure_weightedSquares_zero_preimage_permute_eq
    (dominantEnergyPermutation
      ((Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (Matrix.isHermitian_iff_isSymm.mpr hQ)).eigenvalues
          (finrank_euclideanFin n))
      (symmetricSpectralShift
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr
          (Matrix.isHermitian_iff_isSymm.mpr hQ))
        (WithLp.toLp 2 b)))
    _ _ a t).symm

end PSSSNative.BlockBand.PSSS
