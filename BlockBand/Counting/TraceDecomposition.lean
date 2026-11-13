module

public import BlockBand.Counting.ScalarTrace
public import BlockBand.Model.Construction.GaussianCompatibility
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Gaussian trace removal

Under the Gaussian ring law, the scalar trace `t = N⁻¹ Tr H` is independent of the
trace-removed matrix `H_0 = H - t I`.  The proof removes the coordinate mean from the
diagonal Gaussian coordinates, computes all covariances with the scalar trace, and applies
the Gaussian criterion for independence via zero covariance.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Every extracted coordinate is Gaussian under the model law. -/
theorem GaussianRingModel.gaussianExtraction_hasGaussianLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasGaussianLaw p.gaussianExtraction (model.law : Measure p.SiteMatrix) := by
  exact iIndepFun.hasGaussianLaw
    (fun i => (model.gaussianExtraction_coordinate_hasLaw i).hasGaussianLaw)
    model.iIndepFun_gaussianExtraction

/-- All extracted coordinates have finite second moments. -/
theorem GaussianRingModel.memLp_gaussianExtraction_coordinate {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (i : p.GaussianCoordinate) :
    MemLp (fun H => p.gaussianExtraction H i) 2 (model.law : Measure p.SiteMatrix) :=
  (model.gaussianExtraction_coordinate_hasLaw i).hasGaussianLaw.memLp_two

/-- Diagonal covariance of the independent coordinate family. -/
theorem GaussianRingModel.covariance_gaussianExtraction {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (i j : p.GaussianCoordinate) :
    cov[fun H => p.gaussianExtraction H i, fun H => p.gaussianExtraction H j;
      (model.law : Measure p.SiteMatrix)] =
      if i = j then (p.gaussianCoordinateVariance i : ℝ) else 0 := by
  classical
  by_cases h : i = j
  · subst j
    rw [covariance_self (model.gaussianExtraction_coordinate_hasLaw i).aemeasurable,
      (model.gaussianExtraction_coordinate_hasLaw i).variance_eq, variance_id_gaussianReal]
    simp
  · rw [(model.iIndepFun_gaussianExtraction.indepFun h).covariance_eq_zero
      (model.memLp_gaussianExtraction_coordinate i) (model.memLp_gaussianExtraction_coordinate j)]
    simp [h]

/-- Trace covariance with an extracted coordinate is `c / (N W)` for diagonal labels,
and zero for off-diagonal labels. -/
theorem GaussianRingModel.covariance_scalarTrace_coordinate {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (i : p.GaussianCoordinate) :
    cov[p.scalarTrace, fun H => p.gaussianExtraction H i; (model.law : Measure p.SiteMatrix)] =
      match i with
      | .inl _ => p.c / ((p.N : ℝ) * (p.W : ℝ))
      | .inr _ => 0 := by
  classical
  have he : p.scalarTrace = (fun H => (∑ x : p.Site, p.gaussianExtraction H (.inl x)) / (p.N : ℝ)) := by
    funext H
    rfl
  rw [he, covariance_fun_div_left, covariance_fun_sum_left
    (fun x => model.memLp_gaussianExtraction_coordinate (.inl x))
    (model.memLp_gaussianExtraction_coordinate i)]
  simp_rw [model.covariance_gaussianExtraction]
  cases i with
  | inl x =>
      simp [gaussianCoordinateVariance, entryVariance, mul_comm]
      change (p.c / (p.W : ℝ)) / (p.N : ℝ) = p.c / ((p.W : ℝ) * (p.N : ℝ))
      rw [div_div]
  | inr xy => simp

/-- Remove the scalar trace from diagonal real labels, retaining upper components. -/
def tracelessGaussianCoordinates (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    p.GaussianCoordinate → ℝ
  | .inl x => p.gaussianExtraction H (.inl x) - p.scalarTrace H
  | .inr xy => p.gaussianExtraction H (.inr xy)

/-- Every trace-removed coordinate is uncorrelated with the scalar trace. -/
theorem GaussianRingModel.covariance_scalarTrace_tracelessCoordinate {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (i : p.GaussianCoordinate) :
    cov[p.scalarTrace, fun H => p.tracelessGaussianCoordinates H i;
      (model.law : Measure p.SiteMatrix)] = 0 := by
  cases i with
  | inl x =>
      change cov[p.scalarTrace, fun H => p.gaussianExtraction H (.inl x) - p.scalarTrace H;
        (model.law : Measure p.SiteMatrix)] = 0
      rw [covariance_fun_sub_right model.scalarTrace_hasLaw.hasGaussianLaw.memLp_two
        (model.memLp_gaussianExtraction_coordinate (.inl x))
        model.scalarTrace_hasLaw.hasGaussianLaw.memLp_two,
        model.covariance_scalarTrace_coordinate,
        covariance_self p.measurable_scalarTrace.aemeasurable,
        model.variance_scalarTrace, sub_self]
  | inr xy => exact model.covariance_scalarTrace_coordinate (.inr xy)

/-- Continuous linear averaging map on the real coordinate space. -/
def traceMeanLinear (p : BlockBand.Parameters) :
    (p.GaussianCoordinate → ℝ) →L[ℝ] ℝ :=
  (p.N : ℝ)⁻¹ • ∑ x : p.Site, ContinuousLinearMap.proj (.inl x)

/-- Continuous linear removal of the diagonal-coordinate mean. -/
def traceRemovalLinear (p : BlockBand.Parameters) :
    (p.GaussianCoordinate → ℝ) →L[ℝ] (p.GaussianCoordinate → ℝ) :=
  ContinuousLinearMap.pi fun i => match i with
    | .inl _ => ContinuousLinearMap.proj i - p.traceMeanLinear
    | .inr _ => ContinuousLinearMap.proj i

/-- Joint map, representing the scalar by a singleton indexed family so that
Mathlib's coordinate-covariance Gaussian independence theorem applies exactly. -/
def traceDecompositionLinear (p : BlockBand.Parameters) :
    (p.GaussianCoordinate → ℝ) →L[ℝ] ((Unit → ℝ) × (p.GaussianCoordinate → ℝ)) :=
  (ContinuousLinearMap.pi (fun _ : Unit => p.traceMeanLinear)).prod p.traceRemovalLinear

theorem traceMeanLinear_extraction (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    p.traceMeanLinear (p.gaussianExtraction H) = p.scalarTrace H := by
  simp [traceMeanLinear, scalarTrace, gaussianExtraction, inv_mul_eq_div]

theorem traceRemovalLinear_extraction (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    p.traceRemovalLinear (p.gaussianExtraction H) = p.tracelessGaussianCoordinates H := by
  funext i
  cases i <;> simp [traceRemovalLinear, tracelessGaussianCoordinates, p.traceMeanLinear_extraction]

/-- The pair (scalar trace, traceless coordinates) is jointly Gaussian. -/
theorem GaussianRingModel.traceDecomposition_hasGaussianLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasGaussianLaw (fun H => ((fun _ : Unit => p.scalarTrace H), p.tracelessGaussianCoordinates H))
      (model.law : Measure p.SiteMatrix) := by
  have h := model.gaussianExtraction_hasGaussianLaw.map_fun p.traceDecompositionLinear
  simpa [traceDecompositionLinear, p.traceMeanLinear_extraction,
    p.traceRemovalLinear_extraction] using h

/-- Independence of the scalar trace and all trace-removed coordinates,
from the joint Gaussian law and zero covariances. -/
theorem GaussianRingModel.scalarTrace_independent_tracelessCoordinates {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    IndepFun p.scalarTrace p.tracelessGaussianCoordinates (model.law : Measure p.SiteMatrix) := by
  have h := model.traceDecomposition_hasGaussianLaw.indepFun_of_covariance_eval
    (fun (_ : Unit) i => model.covariance_scalarTrace_tracelessCoordinate i)
  have hc := h.comp (measurable_pi_apply ()) measurable_id
  exact hc

/-- Raw trace-removed matrix `H_0 = H - t I`. -/
def tracelessGaussianMatrix (p : BlockBand.Parameters) (H : p.SiteMatrix) : p.SiteMatrix :=
  H - (p.scalarTrace H : ℂ) • (1 : p.SiteMatrix)

/-- Reconstruction intertwines coordinate trace removal with matrix trace removal. -/
theorem gaussianReconstruction_tracelessCoordinates (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    p.gaussianReconstruction (p.tracelessGaussianCoordinates H) =
      p.gaussianReconstruction (p.gaussianExtraction H) -
        (p.scalarTrace H : ℂ) • (1 : p.SiteMatrix) := by
  classical
  ext x y
  by_cases h : x = y
  · subst y
    simp [gaussianReconstruction, tracelessGaussianCoordinates]
  · simp [gaussianReconstruction, tracelessGaussianCoordinates, h]

/-- Almost surely, the reconstructed trace-removed coordinates give `H_0`. -/
theorem GaussianRingModel.ae_reconstruction_tracelessCoordinates {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    (fun H => p.gaussianReconstruction (p.tracelessGaussianCoordinates H)) =ᵐ[
      (model.law : Measure p.SiteMatrix)] p.tracelessGaussianMatrix := by
  filter_upwards [model.isPhysical.1] with H hH
  rw [p.gaussianReconstruction_tracelessCoordinates,
    p.gaussianReconstruction_gaussianExtraction H hH]
  rfl

/-- Scalar Gaussian trace decomposition of the stationarity proposition:
`t = N⁻¹ Tr H` is independent of `H_0 = H - t I` under the model law.
By `scalarTrace_hasLaw`, `t` has variance `c / (N W)`. -/
theorem GaussianRingModel.scalarTrace_independent_tracelessMatrix {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    IndepFun p.scalarTrace p.tracelessGaussianMatrix (model.law : Measure p.SiteMatrix) := by
  have h := model.scalarTrace_independent_tracelessCoordinates.comp
    measurable_id p.measurable_gaussianReconstruction
  exact h.congr (Filter.Eventually.of_forall fun _ => rfl)
    model.ae_reconstruction_tracelessCoordinates

/-- The real scalar trace is exactly `N⁻¹ Tr H` for Hermitian `H`. -/
theorem scalarTrace_eq_complexTrace (p : BlockBand.Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) :
    (p.scalarTrace H : ℂ) = Matrix.trace H / (p.N : ℂ) := by
  have hd (x : p.Site) : ((H x x).re : ℂ) = H x x := by
    have hc : starRingEnd ℂ (H x x) = H x x := hH.apply x x
    have him : (H x x).im = 0 := by
      have hi := congrArg Complex.im hc
      simp only [Complex.conj_im] at hi
      linarith
    apply Complex.ext <;> simp [him]
  simp only [scalarTrace, Complex.ofReal_div, Complex.ofReal_sum]
  simp_rw [hd]
  simp [Matrix.trace]

end BlockBand.Parameters
