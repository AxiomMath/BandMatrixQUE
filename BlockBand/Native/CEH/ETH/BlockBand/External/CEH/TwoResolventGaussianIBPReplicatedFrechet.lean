module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedGlobalDerivative
public import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Smoothness and Fréchet derivative of the replicated resolvent trace

The normalized trace of the resolvent of the replicated GUE pencil is a real-smooth function of
the Euclidean GUE coordinates at every nonreal spectral parameter, and its Fréchet derivative is
given by the two-resolvent trace in each coordinate direction.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
@[expose] public section
noncomputable section

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal

namespace CEHNative.BlockBand.External.CEH
namespace ReplicatedGUEEuclidean

open PencilAdapter

/-- Every entry of the reconstructed GUE block is a real-smooth function of
its Euclidean coordinate vector. -/
theorem contDiff_hermitianGUEBlock_entry {N d : ℕ} (i j : Fin (N * d)) :
    ContDiff ℝ ⊤ (fun x : CoordinateEuclideanSpace N d =>
      (hermitianGUEBlock (N * d) ((coordinatesEquiv N d).symm x)).1 i j) := by
  rw [show (fun x : CoordinateEuclideanSpace N d =>
      (hermitianGUEBlock (N * d) ((coordinatesEquiv N d).symm x)).1 i j) =
      (fun x => (∑ k : Fin (Fintype.card (HermitianCoordinate (N * d))),
        ((x k : ℝ) : ℂ) • gueCoordinateDirection (N * d) k) i j) by
    funext x
    rw [← hermitianGUEBlock_eq_sum_coordinateDirections]
    rfl]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiff.sum
  intro k hk
  exact ((Complex.ofRealCLM.comp (EuclideanSpace.proj k)).contDiff).mul contDiff_const

/-- Every entry of the global replicated resolvent pencil is real-smooth. -/
theorem contDiff_resolventPencil_entry {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) (z : ℂ) (i j : Fin (N * d)) :
    ContDiff ℝ ⊤ (fun x : CoordinateEuclideanSpace N d =>
      (resolventPencil (replicatedSpectrum d f) lambda
        (hermitianGUEBlock (N * d) ((coordinatesEquiv N d).symm x)).1 z) i j) := by
  simp only [resolventPencil, deformedMatrix, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (contDiff_const.add
    (contDiff_const.mul (contDiff_hermitianGUEBlock_entry i j))).sub contDiff_const

private theorem contDiff_matrix_det
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ i j, ContDiff ℝ ⊤ (fun x => A x i j)) :
    ContDiff ℝ ⊤ (fun x => (A x).det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ hσ
  apply contDiff_const.mul
  apply contDiff_prod
  intro k hk
  exact hA (σ k) k

/-- The determinant of the global replicated resolvent pencil is real-smooth. -/
theorem contDiff_resolventPencil_det {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) (z : ℂ) :
    ContDiff ℝ ⊤ (fun x : CoordinateEuclideanSpace N d =>
      (resolventPencil (replicatedSpectrum d f) lambda
        (hermitianGUEBlock (N * d) ((coordinatesEquiv N d).symm x)).1 z).det) :=
  contDiff_matrix_det _ (contDiff_resolventPencil_entry f lambda z)

/-- The determinant of the global replicated pencil never vanishes away from
the real spectral axis. -/
theorem resolventPencil_det_ne_zero {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (x : CoordinateEuclideanSpace N d) :
    (resolventPencil (replicatedSpectrum d f) lambda
      (hermitianGUEBlock (N * d) ((coordinatesEquiv N d).symm x)).1 z).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  let W := (hermitianGUEBlock (N * d) ((coordinatesEquiv N d).symm x)).1
  let H := deformedMatrix (replicatedSpectrum d f) lambda W
  have hH : H.IsHermitian := deformedMatrix_isHermitian _ _ W
    (hermitianGUEBlock_isHermitian (N * d) _)
  have hu : IsUnit (z • (1 : Matrix (Fin (N * d)) (Fin (N * d)) ℂ) - H) :=
    CEHNative.BlockBand.isUnit_resolventPencil H hH hz
  simpa only [resolventPencil, H, W, neg_sub] using hu.neg

/-- Every entry of the inverse global pencil is real-smooth off the real axis. -/
theorem contDiff_resolvent_entry {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) (i j : Fin (N * d)) :
    ContDiff ℝ ⊤ (fun x : CoordinateEuclideanSpace N d =>
      PencilAdapter.resolvent (replicatedSpectrum d f) lambda
        (hermitianGUEBlock (N * d) ((coordinatesEquiv N d).symm x)).1 z i j) := by
  let A : CoordinateEuclideanSpace N d → Matrix (Fin (N * d)) (Fin (N * d)) ℂ :=
    fun x => resolventPencil (replicatedSpectrum d f) lambda
      (hermitianGUEBlock (N * d) ((coordinatesEquiv N d).symm x)).1 z
  have hA : ∀ p q, ContDiff ℝ ⊤ (fun x => A x p q) :=
    contDiff_resolventPencil_entry f lambda z
  have hdet : ContDiff ℝ ⊤ (fun x => (A x).det) := contDiff_matrix_det A hA
  have hdet0 : ∀ x, (A x).det ≠ 0 := resolventPencil_det_ne_zero f lambda hz
  unfold PencilAdapter.resolvent
  change ContDiff ℝ ⊤ (fun x => (A x)⁻¹ i j)
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  apply (hdet.inv hdet0).mul
  apply contDiff_matrix_det
  intro p q
  simp only [Matrix.updateRow_apply]
  split_ifs
  · fun_prop
  · exact hA _ _

/-- The complex normalized trace of the global replicated resolvent is globally
real-smooth at every nonreal spectral parameter. -/
theorem contDiff_oneResolventTrace {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ContDiff ℝ ⊤ (oneResolventTrace d f lambda z) := by
  unfold oneResolventTrace replicatedOneResolventTrace NTrace
    CEHNative.BlockBand.Conventions.normalizedTrace Matrix.trace
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i hi
  exact contDiff_resolvent_entry f lambda hz i i

/-- The real part of the normalized replicated resolvent trace is globally
`C¹` in all Euclidean GUE coordinates. -/
theorem contDiff_oneResolventTrace_re {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ContDiff ℝ 1 (fun x => (oneResolventTrace d f lambda z x).re) := by
  change ContDiff ℝ 1 (Complex.reCLM ∘ oneResolventTrace d f lambda z)
  exact Complex.reCLM.contDiff.comp
    ((contDiff_oneResolventTrace f lambda hz).of_le (by norm_num))

/-- The imaginary part of the normalized replicated resolvent trace is globally
`C¹` in all Euclidean GUE coordinates. -/
theorem contDiff_oneResolventTrace_im {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ContDiff ℝ 1 (fun x => (oneResolventTrace d f lambda z x).im) := by
  change ContDiff ℝ 1 (Complex.imCLM ∘ oneResolventTrace d f lambda z)
  exact Complex.imCLM.contDiff.comp
    ((contDiff_oneResolventTrace f lambda hz).of_le (by norm_num))

/-- The real-part Fréchet derivative is the real projection of the full complex
derivative. -/
theorem fderiv_oneResolventTrace_re
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (x : CoordinateEuclideanSpace N d) :
    fderiv ℝ (fun y => (oneResolventTrace d f lambda z y).re) x =
      Complex.reCLM.comp (fderiv ℝ (oneResolventTrace d f lambda z) x) := by
  change fderiv ℝ (Complex.reCLM ∘ oneResolventTrace d f lambda z) x = _
  exact (Complex.reCLM.hasFDerivAt.comp x
    ((contDiff_oneResolventTrace f lambda hz).differentiable (by simp) x).hasFDerivAt).fderiv

/-- The imaginary-part Fréchet derivative is the imaginary projection of the
full complex derivative. -/
theorem fderiv_oneResolventTrace_im
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (x : CoordinateEuclideanSpace N d) :
    fderiv ℝ (fun y => (oneResolventTrace d f lambda z y).im) x =
      Complex.imCLM.comp (fderiv ℝ (oneResolventTrace d f lambda z) x) := by
  change fderiv ℝ (Complex.imCLM ∘ oneResolventTrace d f lambda z) x = _
  exact (Complex.imCLM.hasFDerivAt.comp x
    ((contDiff_oneResolventTrace f lambda hz).differentiable (by simp) x).hasFDerivAt).fderiv

/-- The global Fréchet derivative evaluated on a Euclidean coordinate basis
vector is exactly the two-resolvent trace derivative. -/
theorem fderiv_oneResolventTrace_apply_single
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) {z : ℂ}
    (hz : z.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d))))
    (x : CoordinateEuclideanSpace N d) :
    let y := (coordinatesEquiv N d).symm x
    let B := deformationMatrix (replicatedSpectrum d f) +
      (lambda : ℂ) • complementaryGUEBackground (N * d) k y -
      z • (1 : Matrix (Fin (N * d)) (Fin (N * d)) ℂ)
    let D := (lambda : ℂ) • gueCoordinateDirection (N * d) k
    let G := coordinateResolvent B D (x k)
    fderiv ℝ (oneResolventTrace d f lambda z) x (EuclideanSpace.single k 1) =
      (((N * d : ℕ) : ℂ)⁻¹ * ∑ i : Fin (N * d), -(G * D * G) i i) := by
  dsimp only
  let y := (coordinatesEquiv N d).symm x
  have hinner : HasDerivAt
      (fun u => coordinatesEquiv N d (Function.update y k u))
      (EuclideanSpace.single k 1) (x k) := by
    have hu := (hasDerivAt_update y k (x k))
    have he := (coordinatesEquiv N d).hasFDerivAt (x := Function.update y k (x k))
    convert he.comp (x k) hu.hasFDerivAt |>.hasDerivAt using 1
    · rfl
    · rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      ext j
      simp [EuclideanSpace.single, PiLp.single_apply, Pi.single_apply]
  have hupdate : coordinatesEquiv N d (Function.update y k (x k)) = x := by
    ext j
    by_cases hj : j = k
    · subst j
      simp [y]
    · simp [y, Function.update_apply, hj]
  have houter : HasFDerivAt (oneResolventTrace d f lambda z)
      (fderiv ℝ (oneResolventTrace d f lambda z) x)
      (coordinatesEquiv N d (Function.update y k (x k))) := by
    simpa only [hupdate] using
      ((contDiff_oneResolventTrace f lambda hz).differentiable (by simp) x).hasFDerivAt
  have hchain : HasDerivAt
      (fun u => oneResolventTrace d f lambda z
        (coordinatesEquiv N d (Function.update y k u)))
      (fderiv ℝ (oneResolventTrace d f lambda z) x
        (EuclideanSpace.single k 1)) (x k) := by
    convert houter.comp (x k) hinner.hasFDerivAt |>.hasDerivAt using 1
    · rfl
    · simp [y]
  exact hchain.unique (hasDerivAt_oneResolventTrace_coordinateCurve
    f lambda hz k y (x k))

/-- Full Euclidean Fréchet derivative, reconstructed from all coordinate-curve
derivatives.  The formula is an equality on an arbitrary tangent vector, not
merely a list of partial derivatives. -/
theorem fderiv_oneResolventTrace_apply
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (x v : CoordinateEuclideanSpace N d) :
    fderiv ℝ (oneResolventTrace d f lambda z) x v =
      ∑ k : Fin (Fintype.card (HermitianCoordinate (N * d))),
        (v k) •
          let y := (coordinatesEquiv N d).symm x
          let B := deformationMatrix (replicatedSpectrum d f) +
            (lambda : ℂ) • complementaryGUEBackground (N * d) k y -
            z • (1 : Matrix (Fin (N * d)) (Fin (N * d)) ℂ)
          let D := (lambda : ℂ) • gueCoordinateDirection (N * d) k
          let G := coordinateResolvent B D (x k)
          (((N * d : ℕ) : ℂ)⁻¹ *
            ∑ i : Fin (N * d), -(G * D * G) i i) := by
  have hv : v = ∑ k : Fin (Fintype.card (HermitianCoordinate (N * d))),
      (v k) • EuclideanSpace.single k (1 : ℝ) := by
    ext j
    simp [EuclideanSpace.single, PiLp.single_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]
  congr 1
  exact fderiv_oneResolventTrace_apply_single f lambda hz k x

end ReplicatedGUEEuclidean
end CEHNative.BlockBand.External.CEH
