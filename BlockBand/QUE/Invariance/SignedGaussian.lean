module

public import BlockBand.Model.Construction.GaussianCompatibility

/-!
# Signed permutations of the physical Gaussian coordinates

Variance-preserving signed permutations of the real Gaussian coordinates preserve the centred
product law of the coordinates of every physical model
(`GaussianRingModel.signedGaussianExtraction_hasLaw`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Coordinate signs, including inactive Dirac-zero coordinates. -/
def signedGaussianPermutation (p : BlockBand.Parameters)
    (e : p.GaussianCoordinate ≃ p.GaussianCoordinate)
    (negate : p.GaussianCoordinate → Bool)
    (z : p.GaussianCoordinate → ℝ) : p.GaussianCoordinate → ℝ :=
  fun i => if negate i then -z (e i) else z (e i)

/-- The centred coordinate product law is preserved by every variance-preserving signed
permutation. -/
theorem hasLaw_signedGaussianPermutation (p : BlockBand.Parameters)
    (e : p.GaussianCoordinate ≃ p.GaussianCoordinate)
    (negate : p.GaussianCoordinate → Bool)
    (hvar : ∀ i, p.gaussianCoordinateVariance (e i) = p.gaussianCoordinateVariance i) :
    HasLaw (p.signedGaussianPermutation e negate)
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) := by
  let μ : p.GaussianCoordinate → Measure ℝ := fun i =>
    gaussianReal 0 (p.gaussianCoordinateVariance i)
  let Y : p.GaussianCoordinate → (p.GaussianCoordinate → ℝ) → ℝ :=
    fun i z => if negate i then -z (e i) else z (e i)
  have hind0 : iIndepFun
      (fun i : p.GaussianCoordinate => fun z : p.GaussianCoordinate → ℝ => z i)
      (Measure.pi μ) := iIndepFun_pi (μ := μ)
        (X := fun _ : p.GaussianCoordinate => fun x : ℝ => x)
        (fun _ => measurable_id.aemeasurable)
  have hind : iIndepFun Y (Measure.pi μ) := by
    apply (hind0.precomp e.injective).comp (fun i x => if negate i then -x else x)
    intro i
    split_ifs <;> fun_prop
  have hlaw (i : p.GaussianCoordinate) : HasLaw (Y i) (μ i) (Measure.pi μ) := by
    have hbase : HasLaw (fun z : p.GaussianCoordinate → ℝ => z (e i))
        (μ (e i)) (Measure.pi μ) := (measurePreserving_eval μ (e i)).hasLaw
    cases hn : negate i
    · simpa [Y, μ, hn, hvar i] using hbase
    · have hneg := gaussianReal_neg hbase
      have heq : (fun z : p.GaussianCoordinate → ℝ => -z (e i)) =
          -(fun z : p.GaussianCoordinate → ℝ => z (e i)) := by funext z; rfl
      simp only [Y, hn, ite_true]
      rw [heq]
      simpa [μ, hvar i] using hneg
  change HasLaw (fun z i => if negate i then -z (e i) else z (e i))
    (Measure.pi fun i => gaussianReal 0 (p.gaussianCoordinateVariance i))
    (Measure.pi fun i => gaussianReal 0 (p.gaussianCoordinateVariance i))
  simpa [Y, μ] using hind.hasLaw_pi hlaw

/-- Measurability of the concrete signed-coordinate operation. -/
theorem measurable_signedGaussianPermutation (p : BlockBand.Parameters)
    (e : p.GaussianCoordinate ≃ p.GaussianCoordinate)
    (negate : p.GaussianCoordinate → Bool) :
    Measurable (p.signedGaussianPermutation e negate) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold signedGaussianPermutation
  split_ifs <;> fun_prop

/-- Every physical model has the signed-permutation coordinate law. -/
theorem GaussianRingModel.signedGaussianExtraction_hasLaw
    {p : BlockBand.Parameters} (model : p.GaussianRingModel)
    (e : p.GaussianCoordinate ≃ p.GaussianCoordinate)
    (negate : p.GaussianCoordinate → Bool)
    (hvar : ∀ i, p.gaussianCoordinateVariance (e i) = p.gaussianCoordinateVariance i) :
    HasLaw (p.signedGaussianPermutation e negate ∘ p.gaussianExtraction)
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))
      (model.law : Measure p.SiteMatrix) :=
  (p.hasLaw_signedGaussianPermutation e negate hvar).comp
    ⟨p.measurable_gaussianExtraction.aemeasurable, model.gaussianExtraction_law⟩

end BlockBand.Parameters
