module
public import BlockBand.Model.Construction.GaussianCompatibility
public import Mathlib.Probability.ProductMeasure

/-!
# Normalized diagonal-block GUE coordinates

The real Gaussian coordinates of the diagonal blocks of the physical Gaussian ring,
divided by `sqrt c`, have exactly the `GUE_W(1/W)` variances and are jointly independent,
also across blocks; their joint law is the product of the normalized GUE coordinate laws.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open scoped NNReal ComplexConjugate

abbrev BlockGUECoordinate (p : BlockBand.Parameters) :=
  Fin p.W ⊕ (Fin p.W × Fin p.W × Bool)

def blockGUECoordinateVariance (p : BlockBand.Parameters) : p.BlockGUECoordinate → ℝ≥0
  | .inl _ => ⟨1 / (p.W : ℝ), by positivity⟩
  | .inr (a, b, _) => if a.val < b.val then ⟨1 / (2 * (p.W : ℝ)), by positivity⟩ else 0

def blockGUECoordinatesLaw (p : BlockBand.Parameters) : Measure (p.BlockGUECoordinate → ℝ) :=
  Measure.pi (fun i => gaussianReal 0 (p.blockGUECoordinateVariance i))

instance (p : BlockBand.Parameters) : IsProbabilityMeasure p.blockGUECoordinatesLaw := by
  unfold blockGUECoordinatesLaw
  infer_instance

def blockGUECoordinateInclusion (p : BlockBand.Parameters) (k : ZMod p.n) :
    p.BlockGUECoordinate → p.GaussianCoordinate
  | .inl a => .inl (k, a)
  | .inr (a, b, r) => .inr ((k, a), (k, b), r)

/-- Distinct blocks and labels use disjoint independent coordinates. -/
theorem blockGUECoordinateInclusion_injective (p : BlockBand.Parameters) :
    Function.Injective (fun ki : ZMod p.n × p.BlockGUECoordinate =>
      p.blockGUECoordinateInclusion ki.1 ki.2) := by
  rintro ⟨k, i⟩ ⟨l, j⟩ h
  cases i with
  | inl a =>
      cases j with
      | inl b => simpa [blockGUECoordinateInclusion] using h
      | inr q => simp [blockGUECoordinateInclusion] at h
  | inr q =>
      rcases q with ⟨a, b, r⟩
      cases j with
      | inl c => simp [blockGUECoordinateInclusion] at h
      | inr q =>
          rcases q with ⟨c, d, s⟩
          simp only [blockGUECoordinateInclusion, Sum.inr.injEq, Prod.mk.injEq] at h
          rcases h with ⟨⟨hkl, hac⟩, ⟨⟨_, hbd⟩, hrs⟩⟩
          subst l; subst c; subst d; subst s
          rfl

/-- Physical ordering within a block is exactly internal Fin ordering. -/
theorem siteIndex_sameBlock_lt (p : BlockBand.Parameters) (k : ZMod p.n) (a b : Fin p.W) :
    p.siteIndex (k, a) < p.siteIndex (k, b) ↔ a.val < b.val := by
  simp [siteIndex]

/-- Division by `sqrt c` gives exactly the `GUE_W(1/W)` variances. -/
theorem blockGUECoordinateVariance_scaling (p : BlockBand.Parameters)
    (k : ZMod p.n) (i : p.BlockGUECoordinate) :
    NNReal.mk ((Real.sqrt p.c)⁻¹ ^ 2) (sq_nonneg _) *
      p.gaussianCoordinateVariance (p.blockGUECoordinateInclusion k i) =
        p.blockGUECoordinateVariance i := by
  have hc : p.c ≠ 0 := p.c_pos.ne'
  have hW : (p.W : ℝ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  apply NNReal.coe_injective
  cases i with
  | inl a =>
      simp only [blockGUECoordinateInclusion, gaussianCoordinateVariance,
        entryVariance, ite_true, blockGUECoordinateVariance]
      change (Real.sqrt p.c)⁻¹ ^ 2 * (p.c / (p.W : ℝ)) = 1 / (p.W : ℝ)
      rw [inv_pow, Real.sq_sqrt p.c_pos.le]
      field_simp
  | inr q =>
      rcases q with ⟨a, b, r⟩
      by_cases hab : a.val < b.val
      · simp only [blockGUECoordinateInclusion, gaussianCoordinateVariance,
          p.siteIndex_sameBlock_lt, hab, ite_true, entryVariance, blockGUECoordinateVariance]
        change (Real.sqrt p.c)⁻¹ ^ 2 * ((p.c / (p.W : ℝ)) / 2) = 1 / (2 * (p.W : ℝ))
        rw [inv_pow, Real.sq_sqrt p.c_pos.le]
        field_simp
      · simp [blockGUECoordinateInclusion, gaussianCoordinateVariance,
          p.siteIndex_sameBlock_lt, hab, blockGUECoordinateVariance]

def normalizedBlockCoordinates (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    ZMod p.n → p.BlockGUECoordinate → ℝ :=
  fun k i => (Real.sqrt p.c)⁻¹ * p.gaussianExtraction H (p.blockGUECoordinateInclusion k i)

theorem measurable_normalizedBlockCoordinates (p : BlockBand.Parameters) :
    Measurable p.normalizedBlockCoordinates := by
  apply measurable_pi_iff.mpr
  intro k
  apply measurable_pi_iff.mpr
  intro i
  unfold normalizedBlockCoordinates
  exact (((measurable_pi_apply _).comp p.measurable_gaussianExtraction).const_mul _)

/-- Each normalized coordinate is a centered real Gaussian with the GUE variance. -/
theorem GaussianRingModel.normalizedBlock_coordinate_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (k : ZMod p.n) (i : p.BlockGUECoordinate) :
    HasLaw (fun H => p.normalizedBlockCoordinates H k i)
      (gaussianReal 0 (p.blockGUECoordinateVariance i)) (model.law : Measure p.SiteMatrix) := by
  simpa only [normalizedBlockCoordinates, mul_zero, p.blockGUECoordinateVariance_scaling] using
    gaussianReal_const_mul (model.gaussianExtraction_coordinate_hasLaw
      (p.blockGUECoordinateInclusion k i)) (Real.sqrt p.c)⁻¹

/-- Full simultaneous coordinate independence, including across diagonal blocks. -/
theorem GaussianRingModel.iIndepFun_normalizedBlockCoordinates {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    iIndepFun (fun ki : ZMod p.n × p.BlockGUECoordinate =>
      fun H => p.normalizedBlockCoordinates H ki.1 ki.2) (model.law : Measure p.SiteMatrix) := by
  have hi := model.iIndepFun_gaussianExtraction.precomp p.blockGUECoordinateInclusion_injective
  exact hi.comp (fun _ (x : ℝ) => (Real.sqrt p.c)⁻¹ * x) (fun _ => by fun_prop)

/-- The flattened normalized coordinates have the product Gaussian law. -/
theorem GaussianRingModel.normalizedBlockCoordinates_flat_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasLaw (fun H (ki : ZMod p.n × p.BlockGUECoordinate) =>
      p.normalizedBlockCoordinates H ki.1 ki.2)
      (Measure.pi (fun ki : ZMod p.n × p.BlockGUECoordinate =>
        gaussianReal 0 (p.blockGUECoordinateVariance ki.2))) (model.law : Measure p.SiteMatrix) :=
  model.iIndepFun_normalizedBlockCoordinates.hasLaw_pi
    (fun ki => model.normalizedBlock_coordinate_hasLaw ki.1 ki.2)

/-- Regrouping into independent normalized GUE coordinate blocks. -/
theorem GaussianRingModel.normalizedBlockCoordinates_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasLaw p.normalizedBlockCoordinates
      (Measure.pi (fun _ : ZMod p.n => p.blockGUECoordinatesLaw)) (model.law : Measure p.SiteMatrix) := by
  have hc : HasLaw (MeasurableEquiv.curry (ZMod p.n) p.BlockGUECoordinate ℝ)
      (Measure.pi (fun _ : ZMod p.n => p.blockGUECoordinatesLaw))
      (Measure.pi (fun ki : ZMod p.n × p.BlockGUECoordinate =>
        gaussianReal 0 (p.blockGUECoordinateVariance ki.2))) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).measurable.aemeasurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi, blockGUECoordinatesLaw] using
      Measure.infinitePi_map_curry (fun (_ : ZMod p.n) i => gaussianReal 0 (p.blockGUECoordinateVariance i))
  exact hc.comp model.normalizedBlockCoordinates_flat_hasLaw
end BlockBand.Parameters
