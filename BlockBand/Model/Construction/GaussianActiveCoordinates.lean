module

public import BlockBand.Model.Construction.GaussianPolynomialNull

/-!
# Nondegenerate active Gaussian coordinates

The real coordinates of the physical Gaussian model with positive variance (the active
coordinates): their joint law, the almost-sure vanishing of the inactive coordinates, the
almost-sure reconstruction of the matrix from the active coordinates, and absolute continuity of
the active law with respect to Lebesgue measure.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open scoped NNReal

abbrev GaussianActiveCoordinate (p : BlockBand.Parameters) :=
  {i : p.GaussianCoordinate // p.gaussianCoordinateVariance i ≠ 0}

def gaussianActiveExtraction (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    p.GaussianActiveCoordinate → ℝ := fun i => p.gaussianExtraction H i.1

def gaussianActiveValue (p : BlockBand.Parameters) {R : Type*} [Zero R]
    (z : p.GaussianActiveCoordinate → R) (i : p.GaussianCoordinate) : R :=
  if h : p.gaussianCoordinateVariance i ≠ 0 then z ⟨i, h⟩ else 0

def gaussianActiveReconstruction (p : BlockBand.Parameters)
    (z : p.GaussianActiveCoordinate → ℝ) : p.SiteMatrix :=
  p.gaussianReconstruction (p.gaussianActiveValue z)

theorem measurable_gaussianActiveExtraction (p : BlockBand.Parameters) :
    Measurable p.gaussianActiveExtraction :=
  measurable_pi_iff.mpr fun i => (measurable_pi_apply i.1).comp p.measurable_gaussianExtraction

theorem GaussianRingModel.gaussianActiveExtraction_hasLaw
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    HasLaw p.gaussianActiveExtraction
      (Measure.pi fun i : p.GaussianActiveCoordinate =>
        gaussianReal 0 (p.gaussianCoordinateVariance i.1)) (model.law : Measure p.SiteMatrix) := by
  have hind := model.iIndepFun_gaussianExtraction.precomp
    (Subtype.val_injective : Function.Injective (Subtype.val : p.GaussianActiveCoordinate → p.GaussianCoordinate))
  exact hind.hasLaw_pi (fun i => model.gaussianExtraction_coordinate_hasLaw i.1)

theorem GaussianRingModel.ae_gaussianInactiveCoordinate_zero
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (i : p.GaussianCoordinate)
    (hi : p.gaussianCoordinateVariance i = 0) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), p.gaussianExtraction H i = 0 := by
  have h := model.gaussianExtraction_coordinate_hasLaw i
  rw [hi, gaussianReal_zero_var] at h
  have hmap : ∀ᵐ y ∂Measure.map (fun H => p.gaussianExtraction H i)
      (model.law : Measure p.SiteMatrix), y = 0 := by
    rw [h.map_eq, ae_dirac_eq]
    exact Filter.eventually_pure.mpr rfl
  exact ae_of_ae_map h.aemeasurable hmap

/-- Almost-sure exact reconstruction on the nondegenerate sparse coordinate
support; all labels and all raw matrix entries simultaneously. -/
theorem GaussianRingModel.ae_gaussianActiveReconstruction_eq
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      p.gaussianActiveReconstruction (p.gaussianActiveExtraction H) = H := by
  have hall : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∀ i : p.GaussianCoordinate, p.gaussianCoordinateVariance i = 0 → p.gaussianExtraction H i = 0 := by
    rw [ae_all_iff]
    intro i
    by_cases hi : p.gaussianCoordinateVariance i = 0
    · filter_upwards [model.ae_gaussianInactiveCoordinate_zero i hi] with H hH _ using hH
    · exact Filter.Eventually.of_forall fun _ h => False.elim (hi h)
  filter_upwards [hall, model.isPhysical.1] with H hz hH
  have hcoords : p.gaussianActiveValue (p.gaussianActiveExtraction H) = p.gaussianExtraction H := by
    funext i
    unfold gaussianActiveValue gaussianActiveExtraction
    split_ifs with h
    · rfl
    · exact (hz i (not_ne_iff.mp h)).symm
  rw [gaussianActiveReconstruction, hcoords]
  exact p.gaussianReconstruction_gaussianExtraction H hH

/-- The active product law is absolutely continuous w.r.t. finite
Euclidean volume. The absent matrix entries remain deterministic zeros. -/
theorem gaussianActiveLaw_absolutelyContinuous (p : BlockBand.Parameters) :
    (Measure.pi fun i : p.GaussianActiveCoordinate =>
      gaussianReal 0 (p.gaussianCoordinateVariance i.1)) ≪
      (volume : Measure (p.GaussianActiveCoordinate → ℝ)) :=
  pi_absolutelyContinuous_volume _ fun i => gaussianReal_absolutelyContinuous 0 i.2

/-- Nonzero complex polynomial witnesses exclude null algebraic exceptional
sets for any physical model on its active coordinate support. -/
theorem GaussianRingModel.ae_activePolynomial_ne_zero
    {p : BlockBand.Parameters} (model : p.GaussianRingModel)
    (F : MvPolynomial p.GaussianActiveCoordinate ℂ)
    (z₀ : p.GaussianActiveCoordinate → ℝ)
    (h₀ : MvPolynomial.eval (fun i => (z₀ i : ℂ)) F ≠ 0) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      MvPolynomial.eval (fun i => (p.gaussianActiveExtraction H i : ℂ)) F ≠ 0 := by
  set Q := mvPolynomialNormSq F
  have hQ : Q ≠ 0 := by
    intro hQ
    apply h₀
    have h := eval_mvPolynomialNormSq F z₀
    rw [show mvPolynomialNormSq F = 0 from hQ, map_zero] at h
    exact Complex.normSq_eq_zero.mp h.symm
  set Z := {z : p.GaussianActiveCoordinate → ℝ | MvPolynomial.eval z Q = 0}
  have hZmeas : MeasurableSet Z :=
    (MvPolynomial.continuous_eval Q).measurable (measurableSet_singleton 0)
  have hZ : (Measure.pi fun i : p.GaussianActiveCoordinate =>
      gaussianReal 0 (p.gaussianCoordinateVariance i.1)) Z = 0 :=
    p.gaussianActiveLaw_absolutelyContinuous (volume_mvPolynomial_zeroSet_fintype Q hQ)
  have hP : (model.law : Measure p.SiteMatrix) (p.gaussianActiveExtraction ⁻¹' Z) = 0 := by
    rw [← Measure.map_apply p.measurable_gaussianActiveExtraction hZmeas,
      model.gaussianActiveExtraction_hasLaw.map_eq]
    exact hZ
  rw [ae_iff]
  refine measure_mono_null ?_ hP
  intro H hH
  simp only [Set.mem_ofPred_eq, not_not] at hH
  change MvPolynomial.eval (p.gaussianActiveExtraction H) Q = 0
  rw [eval_mvPolynomialNormSq, hH, map_zero]

end BlockBand.Parameters
