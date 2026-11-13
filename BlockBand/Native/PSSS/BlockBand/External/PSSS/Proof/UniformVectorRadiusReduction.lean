module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVector

/-!
# Radius truncation for the complex spherical small-ball problem

This module isolates the exact deterministic and measure-theoretic reduction from a
small-image event for the normalized complex Gaussian direction to a small-image event
for the underlying standard Gaussian, plus a large-radius error.  This is the
radius-truncation step in Lemma 3.1 of APSSS (Aizenman–Peled–Schenker–Shamis–Sodin).
The Gaussian quadratic Laplace-product estimate is not used here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- The small-image event for a complex matrix at threshold `a`. -/
def mulVecNormLeEvent {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) :
    Set (EuclideanSpace ℂ (Fin N)) :=
  {v | ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) : EuclideanSpace ℂ (Fin N))‖ ≤ a}

/-- The matrix small-image event is Borel measurable. -/
theorem measurableSet_mulVecNormLeEvent {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) :
    MeasurableSet (mulVecNormLeEvent Q a) := by
  unfold mulVecNormLeEvent
  exact measurableSet_le (by fun_prop) measurable_const

/-- Exact pushforward formula for every measurable spherical event. -/
theorem uniformSphere_apply_measurableSet {N : ℕ}
    {s : Set (EuclideanSpace ℂ (Fin N))} (hs : MeasurableSet s) :
    uniformSphere N s =
      stdGaussian (EuclideanSpace ℂ (Fin N))
        (complexGaussianDirection ⁻¹' s) := by
  unfold uniformSphere
  exact Measure.map_apply_of_aemeasurable
    measurable_complexGaussianDirection.aemeasurable hs

/-- Multiplying the normalized direction back by its radius recovers a nonzero vector. -/
theorem norm_mulVec_le_radius_of_direction {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) (g : EuclideanSpace ℂ (Fin N))
    {a R : ℝ} (ha : 0 ≤ a)
    (hdir : g ∈ complexGaussianDirection ⁻¹' mulVecNormLeEvent Q a)
    (hrad : ‖g‖ ≤ R) :
    ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp g) : EuclideanSpace ℂ (Fin N))‖ ≤ a * R := by
  by_cases hg : g = 0
  · subst g
    have hR : 0 ≤ R := by simpa using hrad
    simpa [mulVecNormLeEvent] using mul_nonneg ha hR
  have hrecover : (((‖g‖ : ℝ) : ℂ) • complexGaussianDirection g) = g := by
    unfold complexGaussianDirection
    rw [← mul_smul]
    norm_cast
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hg), one_smul]
  have hQ := congrArg
    (fun x : EuclideanSpace ℂ (Fin N) =>
      (WithLp.toLp 2 (Q *ᵥ WithLp.ofLp x) : EuclideanSpace ℂ (Fin N))) hrecover
  have hQ' :
      (WithLp.toLp 2 (Q *ᵥ WithLp.ofLp g) : EuclideanSpace ℂ (Fin N)) =
        ((‖g‖ : ℝ) : ℂ) •
          (WithLp.toLp 2 (Q *ᵥ WithLp.ofLp (complexGaussianDirection g)) :
            EuclideanSpace ℂ (Fin N)) := by
    ext i
    have hi := congrArg (fun x : EuclideanSpace ℂ (Fin N) => WithLp.ofLp x i) hQ
    simpa [Matrix.mulVec] using hi.symm
  rw [hQ', norm_smul, Complex.norm_real]
  have hdir' :
      ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp (complexGaussianDirection g)) :
        EuclideanSpace ℂ (Fin N))‖ ≤ a := hdir
  calc
    ‖‖g‖‖ * ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp (complexGaussianDirection g)) :
      EuclideanSpace ℂ (Fin N))‖
        = ‖g‖ * ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp (complexGaussianDirection g)) :
          EuclideanSpace ℂ (Fin N))‖ := by rw [Real.norm_of_nonneg (norm_nonneg g)]
    _ ≤ ‖g‖ * a := mul_le_mul_of_nonneg_left hdir' (norm_nonneg g)
    _ ≤ R * a := mul_le_mul_of_nonneg_right hrad ha
    _ = a * R := mul_comm _ _

/-- On a radius-truncated Gaussian sample, a spherical small-image event is contained
in the corresponding unnormalized Gaussian small-image event. -/
theorem direction_smallBall_inter_radius_subset {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) {a R : ℝ} (ha : 0 ≤ a) :
    (complexGaussianDirection ⁻¹' mulVecNormLeEvent Q a) ∩ {g | ‖g‖ ≤ R} ⊆
      mulVecNormLeEvent Q (a * R) := by
  intro g hg
  exact norm_mulVec_le_radius_of_direction Q g ha hg.1 hg.2

end PSSSNative.BlockBand.PSSS
