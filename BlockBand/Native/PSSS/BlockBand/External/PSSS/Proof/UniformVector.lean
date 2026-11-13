module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEArbitraryFixedVectorTail
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian normalization and the complex spherical inverse tail

This module defines the uniform complex-sphere law as the direction of the
standard Gaussian on the underlying real Euclidean space.  It proves its probability
normalization, its unit-norm support in positive dimension, and transports the canonical
GUE inverse-vector estimate simultaneously for almost every spherical direction.

Source: Lemma 3.1 and the complex normalization (3.6) of APSSS
(Aizenman–Peled–Schenker–Shamis–Sodin), and the fixed-vector estimate of PSSS
(Peled–Schenker–Shamis–Sodin).  The Gaussian here has real covariance identity on `ℂ^N`; radial scaling is
irrelevant after normalization.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- Radial normalization used to obtain a complex unit vector from a
standard Gaussian on the underlying `2N`-dimensional real Euclidean space. -/
def complexGaussianDirection {N : ℕ} (g : EuclideanSpace ℂ (Fin N)) :
    EuclideanSpace ℂ (Fin N) := ((‖g‖⁻¹ : ℝ) : ℂ) • g

/-- The spherical law is, by definition, the law of the direction of a standard
Gaussian in the underlying real inner-product space. -/
noncomputable def uniformSphere (N : ℕ) : Measure (EuclideanSpace ℂ (Fin N)) :=
  Measure.map complexGaussianDirection
    (stdGaussian (EuclideanSpace ℂ (Fin N)))

/-- Radial normalization is Borel measurable, including its totalized value at zero. -/
theorem measurable_complexGaussianDirection {N : ℕ} :
    Measurable (complexGaussianDirection (N := N)) := by
  unfold complexGaussianDirection
  fun_prop

/-- The normalized Gaussian pushforward remains a probability measure. -/
instance isProbabilityMeasure_uniformSphere (N : ℕ) :
    IsProbabilityMeasure (uniformSphere N) := by
  unfold uniformSphere
  infer_instance

/-- In positive complex dimension, the real standard Gaussian is not a Dirac mass. -/
theorem stdGaussian_complex_ne_dirac {N : ℕ} (hN : 0 < N)
    (x : EuclideanSpace ℂ (Fin N)) :
    stdGaussian (EuclideanSpace ℂ (Fin N)) ≠ Measure.dirac x := by
  intro h
  let i : Fin N := ⟨0, hN⟩
  let e : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (Pi.single i (1 : ℂ))
  let L : StrongDual ℝ (EuclideanSpace ℂ (Fin N)) := innerSL ℝ e
  have hv := variance_dual_stdGaussian L
  rw [h, variance_dirac] at hv
  have hL : ‖L‖ ≠ 0 := by
    intro h0
    have hz : L = 0 := norm_eq_zero.mp h0
    have he : ‖e‖ = 1 := by simp [e, i]
    have hone : L e = 1 := by simp [L, he]
    rw [hz] at hone
    norm_num at hone
  exact hL (sq_eq_zero_iff.mp hv.symm)

set_option maxHeartbeats 800000 in
/-- A positive-dimensional complex standard Gaussian assigns zero mass to the origin. -/
theorem stdGaussian_complex_singleton_zero {N : ℕ} (hN : 0 < N) :
    stdGaussian (EuclideanSpace ℂ (Fin N))
      ({0} : Set (EuclideanSpace ℂ (Fin N))) = 0 := by
  let _ : NullSingletonClass (stdGaussian (EuclideanSpace ℂ (Fin N))) :=
    IsGaussian.nullSingletonClass (fun x => stdGaussian_complex_ne_dirac hN x)
  exact measure_singleton 0

set_option maxHeartbeats 800000 in
/-- A normalized nonzero vector has norm one. -/
theorem norm_complexGaussianDirection {N : ℕ}
    (g : EuclideanSpace ℂ (Fin N)) (hg : g ≠ 0) :
    ‖complexGaussianDirection g‖ = 1 := by
  unfold complexGaussianDirection
  rw [norm_smul, Complex.norm_real, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg)]

set_option maxHeartbeats 800000 in
/-- The complex spherical law is supported on the unit sphere in every positive
complex dimension. -/
theorem uniformSphere_norm_eq_one {N : ℕ} (hN : 0 < N) :
    ∀ᵐ v ∂uniformSphere N, ‖v‖ = 1 := by
  rw [ae_iff]
  unfold uniformSphere
  rw [Measure.map_apply_of_aemeasurable measurable_complexGaussianDirection.aemeasurable]
  · rw [show complexGaussianDirection ⁻¹' {a | ¬ ‖a‖ = 1} = {0} by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hg
        by_contra hgne
        exact hg (norm_complexGaussianDirection g hgne)
      · rintro rfl
        simp [complexGaussianDirection]]
    exact stdGaussian_complex_singleton_zero hN
  · exact (measurableSet_eq_fun measurable_norm measurable_const).compl

/-- The integrated arbitrary-unit-vector GUE estimate holds for almost every direction
of the normalized complex Gaussian, with the same absolute constant as the
fixed-vector theorem.  The constant is chosen before the dimension, deterministic
Hermitian deformation, direction and threshold. -/
theorem uniformSphere_ae_canonicalGUE_inverse_tail :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (N : ℕ) (_hN : 0 < N) (A : HermitianMatrix (Fin N))
        (t : ℝ), 1 ≤ t →
        ∀ᵐ φ ∂uniformSphere N,
          canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
            (canonicalGUEVariance_nonneg N)
            {V | t * Real.sqrt N ≤
              ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ WithLp.ofLp φ) :
                EuclideanSpace ℂ (Fin N))‖} ≤ ENNReal.ofReal (C / t) := by
  obtain ⟨C, hC, htail⟩ := canonicalGUE_arbitraryUnitVector_inverse_tail
  refine ⟨C, hC, ?_⟩
  intro N hN A t ht
  filter_upwards [uniformSphere_norm_eq_one hN] with φ hφ
  exact htail N hN A (WithLp.ofLp φ) (by simpa [complexEuclideanVector]) t ht

end PSSSNative.BlockBand.PSSS
