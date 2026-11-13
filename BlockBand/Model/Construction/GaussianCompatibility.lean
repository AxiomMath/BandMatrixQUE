module

public import BlockBand.Model.Construction.GaussianCharacteristic

/-!
# Characteristic law and entry-product compatibility

Under any physical Gaussian model, the extracted real coordinates (diagonal entries and real and
imaginary parts of the strict upper triangle) are independent centred Gaussians with the
prescribed variances, and the law of the matrix is the canonical product pushforward; in
particular the physical law is unique.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Extract the exact diagonal/strict-upper real coordinates. Redundant labels
are fixed at zero; extraction is defined even for non-Hermitian matrices. -/
def gaussianExtraction (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    p.GaussianCoordinate → ℝ
  | .inl x => (H x x).re
  | .inr (x, y, b) => if p.siteIndex x < p.siteIndex y then
      (if b then (H x y).im else (H x y).re) else 0

theorem measurable_gaussianExtraction (p : BlockBand.Parameters) :
    Measurable p.gaussianExtraction := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  cases i with
  | inl x => unfold gaussianExtraction; fun_prop
  | inr xy =>
      rcases xy with ⟨x, y, b⟩
      change Measurable (fun H : p.SiteMatrix =>
        if p.siteIndex x < p.siteIndex y then
          (if b then (H x y).im else (H x y).re) else 0)
      split_ifs <;> fun_prop

/-- Finite real measures are determined by all real linear characteristic
pairings. This is the finite-coordinate specialization of Mathlib uniqueness. -/
theorem finiteReal_measure_eq_of_characteristic {ι : Type*} [Fintype ι]
    {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ q : ι → ℝ,
      (∫ z, Complex.exp (Complex.I * ((∑ i, q i * z i : ℝ) : ℂ)) ∂μ) =
      ∫ z, Complex.exp (Complex.I * ((∑ i, q i * z i : ℝ) : ℂ)) ∂ν) : μ = ν := by
  classical
  apply Measure.ext_of_charFunDual
  funext L
  let q : ι → ℝ := fun i => L (Pi.single i (1 : ℝ))
  have hlinear (z : ι → ℝ) : L z = ∑ i, q i * z i := by
    have hz : z = ∑ i, z i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    calc
      L z = L (∑ i, z i • Pi.single i (1 : ℝ)) := congrArg L hz
      _ = ∑ i, q i * z i := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [map_smul, smul_eq_mul]
        exact mul_comm (z i) (L (Pi.single i (1 : ℝ)))
  simp only [charFunDual_apply]
  simp_rw [hlinear]
  simpa only [mul_comm] using h q

/-- Every linear test of extracted coordinates equals the upper-triangle
pairing, including the zero labels. No Hermitian premise is needed. -/
theorem gaussianExtraction_pairing (p : BlockBand.Parameters)
    (q : p.GaussianCoordinate → ℝ) (H : p.SiteMatrix) :
    (∑ i, q i * p.gaussianExtraction H i) =
      p.coordinatePairing (fun x => q (.inl x))
        (fun x y => q (.inr (x, y, false)))
        (fun x y => q (.inr (x, y, true))) H := by
  classical
  rw [p.gaussianCoordinate_sum]
  simp only [gaussianExtraction, coordinatePairing]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : p.siteIndex x < p.siteIndex y
  · simp [h, add_comm]
  · simp [h]

/-- Zero-variance redundant labels contribute zero to the covariance. -/
theorem gaussianExtraction_variance (p : BlockBand.Parameters)
    (q : p.GaussianCoordinate → ℝ) :
    p.coordinateVariance (fun x => q (.inl x))
      (fun x y => q (.inr (x, y, false)))
      (fun x y => q (.inr (x, y, true))) =
        ∑ i, (p.gaussianCoordinateVariance i : ℝ) * (q i) ^ 2 := by
  rw [← p.gaussianCoordinateVariance_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases i with
  | inl x => rfl
  | inr xy =>
      rcases xy with ⟨x, y, b⟩
      cases b <;> by_cases h : p.siteIndex x < p.siteIndex y <;>
        simp [gaussianCoordinateCoefficient, gaussianCoordinateVariance, h]

/-- A physical model determines the full independent real coordinate product law. -/
theorem GaussianRingModel.gaussianExtraction_law
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    Measure.map p.gaussianExtraction (model.law : Measure p.SiteMatrix) =
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) := by
  apply finiteReal_measure_eq_of_characteristic
  intro q
  rw [integral_map p.measurable_gaussianExtraction.aemeasurable
    (show AEStronglyMeasurable
      (fun z : p.GaussianCoordinate → ℝ =>
        Complex.exp (Complex.I * ((∑ i, q i * z i : ℝ) : ℂ)))
      (Measure.map p.gaussianExtraction (model.law : Measure p.SiteMatrix)) from
      (show Continuous (fun z : p.GaussianCoordinate → ℝ =>
        Complex.exp (Complex.I * ((∑ i, q i * z i : ℝ) : ℂ))) by fun_prop).aestronglyMeasurable)]
  simp_rw [p.gaussianExtraction_pairing q]
  rw [model.isPhysical.2, p.gaussianExtraction_variance q]
  exact (gaussianProduct_characteristic p.gaussianCoordinateVariance q).symm

/-- Each real coordinate has its exact Gaussian marginal under any physical model,
including Dirac-zero inactive labels. -/
theorem GaussianRingModel.gaussianExtraction_coordinate_hasLaw
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (i : p.GaussianCoordinate) :
    HasLaw (fun H => p.gaussianExtraction H i)
      (gaussianReal 0 (p.gaussianCoordinateVariance i)) (model.law : Measure p.SiteMatrix) := by
  have h : HasLaw p.gaussianExtraction
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))
      (model.law : Measure p.SiteMatrix) :=
    ⟨p.measurable_gaussianExtraction.aemeasurable, model.gaussianExtraction_law⟩
  exact HasLaw.comp
    ⟨(measurable_pi_apply i).aemeasurable,
      (measurePreserving_eval (fun j => gaussianReal 0 (p.gaussianCoordinateVariance j)) i).map_eq⟩ h

/-- The full physical real coordinate family is independent, as a consequence of the joint
characteristic law. -/
theorem GaussianRingModel.iIndepFun_gaussianExtraction
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    iIndepFun (fun i H => p.gaussianExtraction H i) (model.law : Measure p.SiteMatrix) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (μ := (model.law : Measure p.SiteMatrix))
    (f := fun i H => p.gaussianExtraction H i)
    (fun i => ((measurable_pi_apply i).comp p.measurable_gaussianExtraction).aemeasurable)).mpr
  change Measure.map p.gaussianExtraction (model.law : Measure p.SiteMatrix) = _
  rw [model.gaussianExtraction_law]
  change Measure.pi (fun i => gaussianReal 0 (p.gaussianCoordinateVariance i)) =
    Measure.pi (fun i => Measure.map (fun H => p.gaussianExtraction H i)
      (model.law : Measure p.SiteMatrix))
  congr 1
  funext i
  exact (model.gaussianExtraction_coordinate_hasLaw i).map_eq.symm

/-- Hermitian support suffices to reconstruct every raw matrix from its extracted
coordinates; no sparsity or simple-spectrum premise is required. -/
theorem gaussianReconstruction_gaussianExtraction (p : BlockBand.Parameters)
    (H : p.SiteMatrix) (hH : H.IsHermitian) :
    p.gaussianReconstruction (p.gaussianExtraction H) = H := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    have hd : starRingEnd ℂ (H x x) = H x x := hH.apply x x
    have him : (H x x).im = 0 := by
      have hi := congrArg Complex.im hd
      simp only [Complex.conj_im] at hi
      linarith
    apply Complex.ext <;> simp [gaussianReconstruction, gaussianExtraction, him]
  · by_cases hlt : p.siteIndex x < p.siteIndex y
    · apply Complex.ext <;> simp [gaussianReconstruction, gaussianExtraction, hxy, hlt]
    · have hylt : p.siteIndex y < p.siteIndex x := by
        have hne : p.siteIndex x ≠ p.siteIndex y := fun h => hxy (p.siteIndex_injective h)
        omega
      have hconj : starRingEnd ℂ (H y x) = H x y := hH.apply x y
      apply Complex.ext
      · have hre := congrArg Complex.re hconj
        simp only [Complex.conj_re] at hre
        simpa [gaussianReconstruction, gaussianExtraction, hxy, hlt, hylt] using hre
      · have him := congrArg Complex.im hconj
        simp only [Complex.conj_im] at him
        simpa [gaussianReconstruction, gaussianExtraction, hxy, hlt, hylt] using him

/-- Any realization of the physical law has exactly the canonical product pushforward law. -/
theorem GaussianRingModel.law_eq_gaussianMatrixLaw
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    model.law = p.gaussianMatrixLaw := by
  apply Subtype.ext
  have hm := congrArg (Measure.map p.gaussianReconstruction) model.gaussianExtraction_law
  rw [Measure.map_map p.measurable_gaussianReconstruction p.measurable_gaussianExtraction] at hm
  have hae : (fun H => p.gaussianReconstruction (p.gaussianExtraction H)) =ᵐ[
      (model.law : Measure p.SiteMatrix)] id := by
    filter_upwards [model.isPhysical.1] with H hH
    exact p.gaussianReconstruction_gaussianExtraction H hH
  simp only [Function.comp_def] at hm
  rw [Measure.map_congr hae, Measure.map_id] at hm
  exact hm

/-- Uniqueness of the physical probability law on raw matrices. -/
theorem physicalGaussianRingLaw_unique {p : BlockBand.Parameters}
    (M M' : p.GaussianRingModel) : M.law = M'.law :=
  M.law_eq_gaussianMatrixLaw.trans M'.law_eq_gaussianMatrixLaw.symm

end BlockBand.Parameters
