module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedPoincare
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Euclidean transport of the replicated GUE coordinate law

The concrete GUE coordinates are stored as a finite function type, whose library
norm is the sup norm.  This module transports them through the canonical
continuous linear equivalence to the `L²`-normed `EuclideanSpace`.  It proves
measurability, Gaussianity, centering, and preserves every coordinate marginal
with its exact diagonal/off-diagonal variance.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped NNReal RealInnerProductSpace

namespace CEHNative.BlockBand.External.CEH
namespace ReplicatedGUEEuclidean

open PencilAdapter

/-- The Euclidean realization of all independent real Hermitian coordinates. -/
abbrev CoordinateEuclideanSpace (N d : ℕ) :=
  EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate (N * d))))

/-- Canonical coordinate-preserving continuous linear equivalence from the
sup-normed finite function space used by reconstruction to its Euclidean `L²`
realization. -/
def coordinatesEquiv (N d : ℕ) :
    ReplicatedGUECoordinateSpace N d ≃L[ℝ] CoordinateEuclideanSpace N d :=
  (EuclideanSpace.equiv
    (Fin (Fintype.card (HermitianCoordinate (N * d)))) ℝ).symm

@[simp] theorem coordinatesEquiv_apply (N d : ℕ)
    (x : ReplicatedGUECoordinateSpace N d)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d)))) :
    coordinatesEquiv N d x k = x k := by
  rfl

@[simp] theorem coordinatesEquiv_symm_apply (N d : ℕ)
    (x : CoordinateEuclideanSpace N d)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d)))) :
    (coordinatesEquiv N d).symm x k = x k := by
  rfl

/-- The pushed-forward concrete replicated GUE law on a Hilbert space. -/
def measure (N d : ℕ) : Measure (CoordinateEuclideanSpace N d) :=
  Measure.map (coordinatesEquiv N d) (replicatedNormalizedGUEMeasure N d)

instance measure.instIsProbabilityMeasure (N d : ℕ) :
    IsProbabilityMeasure (measure N d) := by
  unfold measure
  infer_instance

/-- The transport and its inverse are Borel measurable. -/
theorem measurable_coordinatesEquiv (N d : ℕ) :
    Measurable (coordinatesEquiv N d) :=
  (coordinatesEquiv N d).continuous.measurable

/-- The inverse Euclidean transport is Borel measurable. -/
theorem measurable_coordinatesEquiv_symm (N d : ℕ) :
    Measurable (coordinatesEquiv N d).symm :=
  (coordinatesEquiv N d).symm.continuous.measurable

/-- The transported identity has the original concrete product law. -/
theorem hasLaw_coordinatesEquiv (N d : ℕ) :
    HasLaw (coordinatesEquiv N d) (measure N d)
      (replicatedNormalizedGUEMeasure N d) := by
  exact ⟨(measurable_coordinatesEquiv N d).aemeasurable, rfl⟩

/-- The Euclidean pushforward remains Gaussian, proved from the already-derived
joint Gaussian law and the explicit continuous linear map. -/
instance measure.instIsGaussian (N d : ℕ) : IsGaussian (measure N d) := by
  exact (FiniteGaussianPoincare.replicatedNormalizedGUE_hasGaussianLaw_id N d).map
    (coordinatesEquiv N d).toContinuousLinearMap |>.isGaussian_map

/-- The Euclidean pushforward is centered. -/
theorem integral_id_eq_zero (N d : ℕ) :
    (∫ x : CoordinateEuclideanSpace N d, x ∂measure N d) = 0 := by
  rw [measure]
  change (∫ x : CoordinateEuclideanSpace N d, id x
    ∂Measure.map (coordinatesEquiv N d) (replicatedNormalizedGUEMeasure N d)) = 0
  rw [integral_map_of_stronglyMeasurable (measurable_coordinatesEquiv N d)
    stronglyMeasurable_id]
  change (∫ x : ReplicatedGUECoordinateSpace N d, coordinatesEquiv N d x
    ∂replicatedNormalizedGUEMeasure N d) = 0
  change (∫ x : ReplicatedGUECoordinateSpace N d,
    (coordinatesEquiv N d).toContinuousLinearMap x
    ∂replicatedNormalizedGUEMeasure N d) = 0
  rw [ContinuousLinearMap.integral_comp_id_comm (IsGaussian.integrable_id)
    (coordinatesEquiv N d).toContinuousLinearMap]
  rw [FiniteGaussianPoincare.integral_id_replicatedNormalizedGUEMeasure_eq_zero]
  exact map_zero _

/-- Each Euclidean coordinate retains its exact scalar Gaussian law. -/
theorem coordinate_hasLaw (N d : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d)))) :
    HasLaw (fun x : CoordinateEuclideanSpace N d => x k)
      (gaussianReal 0 (hermitianGUEFinCoordinateVariance (N * d)
        (1 / ((N * d : ℕ) : ℝ)) (by positivity) k)) (measure N d) := by
  have hsource := replicatedNormalizedGUE_coordinate_hasLaw N d k
  refine { aemeasurable := (by fun_prop), map_eq := ?_ }
  rw [measure, Measure.map_map
    (by fun_prop : Measurable (fun x : CoordinateEuclideanSpace N d => x k))
    (measurable_coordinatesEquiv N d)]
  rw [← hsource.map_eq]
  congr 1

/-- The coordinate variance of the Euclidean law is exactly the GUE coordinate
variance; this is the diagonal data for its covariance operator. -/
theorem variance_coordinate (N d : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d)))) :
    Var[(fun x : CoordinateEuclideanSpace N d => x k); measure N d] =
      hermitianGUEFinCoordinateVariance (N * d)
        (1 / ((N * d : ℕ) : ℝ)) (by positivity) k := by
  rw [(coordinate_hasLaw N d k).variance_eq]
  exact variance_id_gaussianReal

/-!
### Resolvent-trace transport and coordinate derivatives
-/

/-- The replicated normalized resolvent trace, now viewed on the Euclidean
coordinate realization. -/
def oneResolventTrace {N : ℕ} (d : ℕ) (f : Spectrum N)
    (lambda : ℝ) (z : ℂ) (x : CoordinateEuclideanSpace N d) : ℂ :=
  replicatedOneResolventTrace d f lambda z ((coordinatesEquiv N d).symm x)

@[simp] theorem oneResolventTrace_coordinatesEquiv {N d : ℕ}
    (f : Spectrum N) (lambda : ℝ) (z : ℂ)
    (y : ReplicatedGUECoordinateSpace N d) :
    oneResolventTrace d f lambda z (coordinatesEquiv N d y) =
      replicatedOneResolventTrace d f lambda z y := by
  simp [oneResolventTrace]

/-- Exact derivative of the Euclidean trace along the image of one raw
coordinate line.  This is the coordinatewise input for the later global
Fréchet-gradient bound; no bound is asserted here. -/
theorem hasDerivAt_oneResolventTrace_coordinateCurve
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) {z : ℂ}
    (hz : z.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d))))
    (y : ReplicatedGUECoordinateSpace N d) (x : ℝ) :
    let B := deformationMatrix (replicatedSpectrum d f) +
      (lambda : ℂ) • complementaryGUEBackground (N * d) k y -
      z • (1 : Matrix (Fin (N * d)) (Fin (N * d)) ℂ)
    let D := (lambda : ℂ) • gueCoordinateDirection (N * d) k
    let G := coordinateResolvent B D x
    HasDerivAt
      (fun u => oneResolventTrace d f lambda z
        (coordinatesEquiv N d (Function.update y k u)))
      ((((N * d : ℕ) : ℂ)⁻¹ *
        ∑ i : Fin (N * d), -(G * D * G) i i)) x := by
  simpa only [oneResolventTrace_coordinatesEquiv] using
    hasDerivAt_replicatedOneResolventTrace_update f lambda hz k y x

end ReplicatedGUEEuclidean
end CEHNative.BlockBand.External.CEH
