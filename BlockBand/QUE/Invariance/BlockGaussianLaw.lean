module

public import BlockBand.QUE.Invariance.BlockCovariance

/-!
# Block-unitary invariance of the physical Gaussian law

Conjugation by independently chosen deterministic block unitaries preserves the characteristic
function of every physical Gaussian model, hence its law
(`GaussianRingModel.map_blockUnitaryConjugation`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open Matrix MeasureTheory ProbabilityTheory

/-- The Hermitian representative of a real-coordinate test. -/
def coordinateHermitianTest (p : BlockBand.Parameters) (d : p.Site → ℝ)
    (u v : p.Site → p.Site → ℝ) : p.SiteMatrix :=
  p.gaussianReconstruction (fun i => match i with
    | .inl x => d x
    | .inr (x,y,b) => if b then v x y / 2 else u x y / 2)

theorem coordinateHermitianTest_isHermitian (p : BlockBand.Parameters)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    (p.coordinateHermitianTest d u v).IsHermitian := p.gaussianReconstruction_isHermitian _

theorem coordinateHermitianTest_pairing (p : BlockBand.Parameters)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) (H : p.SiteMatrix)
    (hH : H.IsHermitian) :
    (Matrix.trace (p.coordinateHermitianTest d u v * H)).re = p.coordinatePairing d u v H := by
  rw [p.hermitianTrace_eq_coordinatePairing _ H (p.coordinateHermitianTest_isHermitian d u v) hH]
  unfold coordinatePairing
  simp only [coordinateHermitianTest, gaussianReconstruction]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y hy
  have hlt := (Finset.mem_filter.mp hy).2
  have hne : x ≠ y := fun h => by subst y; omega
  have htwo (r : ℝ) : 2 * (r / 2) = r := by ring
  simp [hne, hlt, htwo]

theorem coordinateHermitianTest_variance (p : BlockBand.Parameters)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    p.hermitianTestVariance (p.coordinateHermitianTest d u v) = p.coordinateVariance d u v := by
  rw [p.hermitianTestVariance_eq_coordinateVariance _ (p.coordinateHermitianTest_isHermitian d u v)]
  unfold coordinateVariance
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    simp [coordinateHermitianTest, gaussianReconstruction]
  · apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y hy
    have hlt := (Finset.mem_filter.mp hy).2
    have hne : x ≠ y := fun h => by subst y; omega
    have htwo (r : ℝ) : 2 * (r / 2) = r := by ring
    simp [coordinateHermitianTest, gaussianReconstruction, hne, hlt, htwo]

/-- The embedding commutes with adjoints. -/
theorem blockUnitaryMatrix_star (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) :
    p.blockUnitaryMatrix (fun k => star (U k)) = (p.blockUnitaryMatrix U)ᴴ := by
  ext x y
  by_cases h : x.1 = y.1
  · simp [Matrix.conjTranspose_apply, h]
  · simp [Matrix.conjTranspose_apply, h, Ne.symm h]

theorem measurable_blockUnitaryConjugation (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) :
    Measurable (p.blockUnitaryConjugation U) := by
  unfold blockUnitaryConjugation
  fun_prop

/-- Trace test transport uses the inverse conjugation of the Hermitian test. -/
theorem trace_blockUnitaryConjugation (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) (A H : p.SiteMatrix) :
    Matrix.trace (A * p.blockUnitaryConjugation U H) =
      Matrix.trace (p.blockUnitaryConjugation (fun k => star (U k)) A * H) := by
  simp only [blockUnitaryConjugation, blockUnitaryMatrix_star, Matrix.conjTranspose_conjTranspose]
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A * p.blockUnitaryMatrix U * H) (p.blockUnitaryMatrix U)ᴴ)

/-- Conjugation preserves Hermitian matrices. -/
theorem blockUnitaryConjugation_isHermitian (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) (H : p.SiteMatrix)
    (hH : H.IsHermitian) : (p.blockUnitaryConjugation U H).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _ hH

/-- The characteristic law is preserved by block-unitary conjugation, so the pushforward is again
a physical model. -/
theorem GaussianRingModel.isPhysical_map_blockUnitaryConjugation
    {p : BlockBand.Parameters} (model : p.GaussianRingModel)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) :
    p.IsPhysicalGaussianRingLaw (model.law.map (p.blockUnitaryConjugation U)) := by
  constructor
  · change ∀ᵐ H ∂Measure.map (p.blockUnitaryConjugation U) (model.law : Measure p.SiteMatrix), H.IsHermitian
    rw [ae_map_iff (p.measurable_blockUnitaryConjugation U).aemeasurable]
    · filter_upwards [model.isPhysical.1] with H hH
      exact p.blockUnitaryConjugation_isHermitian U H hH
    · exact (isClosed_eq (by fun_prop : Continuous (fun H : p.SiteMatrix => H.conjTranspose))
        continuous_id).measurableSet
  · intro d u v
    change (∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))
        ∂Measure.map (p.blockUnitaryConjugation U) (model.law : Measure p.SiteMatrix)) = _
    rw [integral_map (p.measurable_blockUnitaryConjugation U).aemeasurable
      (show AEStronglyMeasurable (fun H : p.SiteMatrix => Complex.exp
        (Complex.I * (p.coordinatePairing d u v H : ℂ)))
        (Measure.map (p.blockUnitaryConjugation U) (model.law : Measure p.SiteMatrix)) from
          (show Continuous (fun H : p.SiteMatrix => Complex.exp
            (Complex.I * (p.coordinatePairing d u v H : ℂ))) by
              unfold coordinatePairing; fun_prop).aestronglyMeasurable)]
    let A := p.coordinateHermitianTest d u v
    have hA : A.IsHermitian := p.coordinateHermitianTest_isHermitian d u v
    have hae : (fun H : p.SiteMatrix => Complex.exp
        (Complex.I * (p.coordinatePairing d u v (p.blockUnitaryConjugation U H) : ℂ))) =ᵐ[
          (model.law : Measure p.SiteMatrix)]
        (fun H => Complex.exp (Complex.I *
          ((Matrix.trace (p.blockUnitaryConjugation (fun k => star (U k)) A * H)).re : ℂ))) := by
      filter_upwards [model.isPhysical.1] with H hH
      rw [← p.coordinateHermitianTest_pairing d u v _ (p.blockUnitaryConjugation_isHermitian U H hH),
        p.trace_blockUnitaryConjugation]
    rw [integral_congr_ae hae,
      model.hermitianTrace_characteristic _ (p.blockUnitaryConjugation_isHermitian _ A hA),
      p.hermitianTestVariance_blockUnitaryConjugation,
      p.coordinateHermitianTest_variance]

/-- Law invariance under independently chosen deterministic block unitaries, from the
characteristic law and uniqueness of the law. -/
theorem GaussianRingModel.map_blockUnitaryConjugation
    {p : BlockBand.Parameters} (model : p.GaussianRingModel)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) :
    Measure.map (p.blockUnitaryConjugation U) (model.law : Measure p.SiteMatrix) =
      (model.law : Measure p.SiteMatrix) := by
  let rotated : p.GaussianRingModel :=
    ⟨model.law.map (p.blockUnitaryConjugation U), model.isPhysical_map_blockUnitaryConjugation U⟩
  exact congrArg (fun law : ProbabilityMeasure p.SiteMatrix => (law : Measure p.SiteMatrix))
    (physicalGaussianRingLaw_unique rotated model)

end BlockBand.Parameters
