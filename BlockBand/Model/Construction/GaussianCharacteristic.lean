module

public import BlockBand.Model.Construction.GaussianCoordinates

/-!
# The joint characteristic identity of the Gaussian construction

The pushforward of a product of independent centred real Gaussians under Hermitian
reconstruction has the joint characteristic function of the physical Gaussian block-band law;
this gives a construction of the physical model for every admissible parameter.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Characteristic identity for a finite product of centered real Gaussians,
including zero variances. The real linear pairing and covariance are exact. -/
theorem gaussianProduct_characteristic {ι : Type*} [Fintype ι]
    (variance : ι → ℝ≥0) (coefficient : ι → ℝ) :
    (∫ z : ι → ℝ,
      Complex.exp (Complex.I * ((∑ i, coefficient i * z i : ℝ) : ℂ))
      ∂Measure.pi (fun i => gaussianReal 0 (variance i))) =
    Complex.exp (-((∑ i, (variance i : ℝ) * (coefficient i) ^ 2 : ℝ) : ℂ) / 2) := by
  classical
  have hpoint (z : ι → ℝ) :
      Complex.exp (Complex.I * ((∑ i, coefficient i * z i : ℝ) : ℂ)) =
        ∏ i, Complex.exp (Complex.I * ((coefficient i * z i : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  simp_rw [hpoint]
  rw [integral_fintype_prod_eq_prod
    (fun i (x : ℝ) => Complex.exp (Complex.I * ((coefficient i * x : ℝ) : ℂ)))
    (μ := fun i => gaussianReal 0 (variance i))]
  have hsingle (i : ι) :
      (∫ x : ℝ, Complex.exp (Complex.I * ((coefficient i * x : ℝ) : ℂ))
        ∂gaussianReal 0 (variance i)) =
        Complex.exp (-((variance i : ℂ) * (coefficient i : ℂ) ^ 2) / 2) := by
    have h := charFun_gaussianReal (μ := 0) (v := variance i) (coefficient i)
    rw [charFun_apply_real] at h
    simpa [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc, neg_div] using h
  simp_rw [hsingle]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← Finset.sum_div]
  congr 1
  simp

/-- Exact finite sum over the independent diagonal/component label type. -/
theorem gaussianCoordinate_sum (p : BlockBand.Parameters)
    (f : p.GaussianCoordinate → ℝ) :
    (∑ i, f i) = (∑ x, f (.inl x)) +
      ∑ x : p.Site, ∑ y : p.Site,
        (f (.inr (x, y, true)) + f (.inr (x, y, false))) := by
  classical
  rw [Fintype.sum_sum_type]
  congr 1
  calc
    (∑ xy : p.Site × (p.Site × Bool), f (.inr xy)) =
      ∑ x : p.Site, ∑ yb : p.Site × Bool, f (.inr (x, yb)) :=
        Fintype.sum_prod_type _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Fintype.sum_prod_type (fun yb : p.Site × Bool => f (.inr (x, yb)))]
      apply Finset.sum_congr rfl
      intro y _
      exact Fintype.sum_bool _

/-- Coefficients of the real coordinate pairing on independent labels. -/
def gaussianCoordinateCoefficient (p : BlockBand.Parameters)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) : p.GaussianCoordinate → ℝ
  | .inl x => d x
  | .inr (x, y, b) =>
      if p.siteIndex x < p.siteIndex y then (if b then v x y else u x y) else 0

theorem gaussianReconstruction_diagonal_re (p : BlockBand.Parameters)
    (z : p.GaussianCoordinate → ℝ) (x : p.Site) :
    (p.gaussianReconstruction z x x).re = z (.inl x) := by
  simp [gaussianReconstruction]

theorem gaussianReconstruction_upper_re (p : BlockBand.Parameters)
    (z : p.GaussianCoordinate → ℝ) (x y : p.Site)
    (h : p.siteIndex x < p.siteIndex y) :
    (p.gaussianReconstruction z x y).re = z (.inr (x, y, false)) := by
  have hxy : x ≠ y := fun he => by simp [he] at h
  simp [gaussianReconstruction, hxy, h]

theorem gaussianReconstruction_upper_im (p : BlockBand.Parameters)
    (z : p.GaussianCoordinate → ℝ) (x y : p.Site)
    (h : p.siteIndex x < p.siteIndex y) :
    (p.gaussianReconstruction z x y).im = z (.inr (x, y, true)) := by
  have hxy : x ≠ y := fun he => by simp [he] at h
  simp [gaussianReconstruction, hxy, h]

/-- Reconstruction identifies the full joint pairing, not merely marginal laws. -/
theorem gaussianReconstruction_coordinatePairing (p : BlockBand.Parameters)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
    (z : p.GaussianCoordinate → ℝ) :
    p.coordinatePairing d u v (p.gaussianReconstruction z) =
      ∑ i, p.gaussianCoordinateCoefficient d u v i * z i := by
  classical
  simp only [coordinatePairing, gaussianReconstruction_diagonal_re,
    gaussianCoordinate_sum, gaussianCoordinateCoefficient]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : p.siteIndex x < p.siteIndex y
  · simp [h, p.gaussianReconstruction_upper_re z x y h,
      p.gaussianReconstruction_upper_im z x y h, add_comm]
  · simp [h]

/-- The product covariance equals the physical quadratic form. -/
theorem gaussianCoordinateVariance_sum (p : BlockBand.Parameters)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    (∑ i, (p.gaussianCoordinateVariance i : ℝ) *
      (p.gaussianCoordinateCoefficient d u v i) ^ 2) = p.coordinateVariance d u v := by
  classical
  simp only [coordinateVariance, gaussianCoordinate_sum, gaussianCoordinateCoefficient,
    gaussianCoordinateVariance]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : p.siteIndex x < p.siteIndex y
  · simp only [h, ite_true, Bool.false_eq_true, ite_false]
    change (p.entryVariance x y / 2) * (v x y) ^ 2 +
      (p.entryVariance x y / 2) * (u x y) ^ 2 =
      (p.entryVariance x y / 2) * ((u x y) ^ 2 + (v x y) ^ 2)
    ring
  · simp [h]

/-- The Gaussian pushforward satisfies every coefficient-array identity
of the physical law, with no supplied-law or independence hypotheses. -/
theorem gaussianMatrixLaw_characteristic (p : BlockBand.Parameters)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    (∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))
      ∂(p.gaussianMatrixLaw : Measure p.SiteMatrix)) =
      Complex.exp (-(p.coordinateVariance d u v : ℂ) / 2) := by
  change (∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))
    ∂Measure.map p.gaussianReconstruction
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))) = _
  rw [integral_map p.measurable_gaussianReconstruction.aemeasurable (show AEStronglyMeasurable
    (fun H : p.SiteMatrix => Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ)))
    (Measure.map p.gaussianReconstruction
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))) from
    (show Continuous (fun H : p.SiteMatrix =>
      Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))) by
      unfold coordinatePairing
      fun_prop).aestronglyMeasurable)]
  simp_rw [p.gaussianReconstruction_coordinatePairing d u v]
  exact (gaussianProduct_characteristic p.gaussianCoordinateVariance
    (p.gaussianCoordinateCoefficient d u v)).trans
    (congrArg (fun t : ℝ => Complex.exp (-(t : ℂ) / 2))
      (p.gaussianCoordinateVariance_sum d u v))

/-- A constructor of the physical Gaussian law, for every admissible finite parameter. This is
existence of the physical model only. -/
def constructGaussianRingModel (p : BlockBand.Parameters) : p.GaussianRingModel where
  law := p.gaussianMatrixLaw
  isPhysical := ⟨p.gaussianMatrixLaw_ae_isHermitian, p.gaussianMatrixLaw_characteristic⟩

theorem nonempty_gaussianRingModel (p : BlockBand.Parameters) :
    Nonempty p.GaussianRingModel := ⟨p.constructGaussianRingModel⟩

end BlockBand.Parameters
