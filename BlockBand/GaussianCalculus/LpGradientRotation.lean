module

public import Mathlib
public import BlockBand.Internal.Contracts.Inputs

/-!
# Rotation invariance of two independent Gaussian product vectors

Law: `κ = μ ⊗ μ` on `(ι → ℝ) × (ι → ℝ)` with `μ = gaussianProduct v`, finite `ι`, every variance
`v i ≥ 0` (zero allowed). For every angle `θ`, the map
`(x, y) ↦ (sin θ x + cos θ y, cos θ x - sin θ y)` preserves `κ`, reducing to the
rotation invariance of the planar Gaussian `N(0, v) ⊗ N(0, v)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianCalculus

open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open scoped NNReal ENNReal

/-- The planar map `(a, b) ↦ (sin θ a + cos θ b, cos θ a - sin θ b)` as a linear map. -/
def planarRot (θ : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (Real.sin θ • LinearMap.fst ℝ ℝ ℝ + Real.cos θ • LinearMap.snd ℝ ℝ ℝ).prod
    (Real.cos θ • LinearMap.fst ℝ ℝ ℝ - Real.sin θ • LinearMap.snd ℝ ℝ ℝ)

/-- Coordinate formula for `planarRot`. -/
theorem planarRot_apply (θ : ℝ) (z : ℝ × ℝ) :
    planarRot θ z = (Real.sin θ * z.1 + Real.cos θ * z.2, Real.cos θ * z.1 - Real.sin θ * z.2) := by
  simp [planarRot]

/-- The planar map is an involution. -/
theorem planarRot_comp_self (θ : ℝ) : planarRot θ ∘ₗ planarRot θ = LinearMap.id := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, planarRot_apply, LinearMap.id_apply]
  ext
  · simp only
    linear_combination z.1 * Real.sin_sq_add_cos_sq θ
  · simp only
    linear_combination z.2 * Real.sin_sq_add_cos_sq θ

/-- The planar map preserves Lebesgue measure on `ℝ × ℝ`. -/
theorem measurePreserving_planarRot_volume (θ : ℝ) :
    MeasurePreserving (planarRot θ) (volume : Measure (ℝ × ℝ)) volume := by
  have hdet : LinearMap.det (planarRot θ) * LinearMap.det (planarRot θ) = 1 := by
    rw [← LinearMap.det_comp, planarRot_comp_self, LinearMap.det_id]
  have hne : LinearMap.det (planarRot θ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  have habs : |(LinearMap.det (planarRot θ))⁻¹| = 1 := by
    have h1 : |LinearMap.det (planarRot θ)| * |LinearMap.det (planarRot θ)| = 1 := by
      rw [← abs_mul, hdet, abs_one]
    have h2 : |LinearMap.det (planarRot θ)| = 1 := by
      have h0 : 0 ≤ |LinearMap.det (planarRot θ)| := abs_nonneg _
      nlinarith
    rw [abs_inv, h2, inv_one]
  refine ⟨(planarRot θ).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne, habs, ENNReal.ofReal_one, one_smul]

/-- The two-dimensional Gaussian density product is invariant under the planar map. -/
theorem gaussianPDFReal_mul_planarRot (v : ℝ≥0) (θ : ℝ) (z : ℝ × ℝ) :
    gaussianPDFReal 0 v (planarRot θ z).1 * gaussianPDFReal 0 v (planarRot θ z).2 =
      gaussianPDFReal 0 v z.1 * gaussianPDFReal 0 v z.2 := by
  simp only [gaussianPDFReal, planarRot_apply, sub_zero]
  rw [mul_mul_mul_comm, mul_mul_mul_comm _ (Real.exp _), ← Real.exp_add, ← Real.exp_add]
  congr 2
  have h : (Real.sin θ * z.1 + Real.cos θ * z.2) ^ 2 + (Real.cos θ * z.1 - Real.sin θ * z.2) ^ 2 =
      z.1 ^ 2 + z.2 ^ 2 := by
    linear_combination (z.1 ^ 2 + z.2 ^ 2) * Real.sin_sq_add_cos_sq θ
  rw [← add_div, ← add_div, ← neg_add, ← neg_add, h]

/-- Rotation invariance of `N(0, v) ⊗ N(0, v)` on `ℝ × ℝ`, every `v ≥ 0`. -/
theorem measurePreserving_planarRot_gaussian (v : ℝ≥0) (θ : ℝ) :
    MeasurePreserving (planarRot θ) ((gaussianReal 0 v).prod (gaussianReal 0 v))
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
  have hmeas : Measurable (planarRot θ) := (planarRot θ).continuous_of_finiteDimensional.measurable
  by_cases hv : v = 0
  · subst hv
    refine ⟨hmeas, ?_⟩
    rw [gaussianReal_zero_var, Measure.dirac_prod_dirac]
    ext s hs
    rw [Measure.map_apply hmeas hs, Measure.dirac_apply' _ (hmeas hs), Measure.dirac_apply' _ hs]
    have h0 : planarRot θ ((0 : ℝ), (0 : ℝ)) = ((0 : ℝ), (0 : ℝ)) := by
      rw [Prod.mk_zero_zero, map_zero]
    have hpre : ((0 : ℝ), (0 : ℝ)) ∈ planarRot θ ⁻¹' s ↔ ((0 : ℝ), (0 : ℝ)) ∈ s := by
      rw [Set.mem_preimage, h0]
    by_cases h : ((0 : ℝ), (0 : ℝ)) ∈ s
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hpre.mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hpre.mp h)]
  · have hvol := measurePreserving_planarRot_volume θ
    let ρ : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF 0 v z.1 * gaussianPDF 0 v z.2
    have hρm : Measurable ρ :=
      ((measurable_gaussianPDF 0 v).comp measurable_fst).mul
        ((measurable_gaussianPDF 0 v).comp measurable_snd)
    have hρ (z : ℝ × ℝ) : ρ (planarRot θ z) = ρ z := by
      simp only [ρ, gaussianPDF]
      rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
        ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal_mul_planarRot]
    have hprod : (gaussianReal 0 v).prod (gaussianReal 0 v) =
        (volume : Measure (ℝ × ℝ)).withDensity ρ := by
      rw [gaussianReal_of_var_ne_zero 0 hv, prod_withDensity (measurable_gaussianPDF 0 v)
        (measurable_gaussianPDF 0 v), Measure.volume_eq_prod]
    rw [hprod]
    refine ⟨hmeas, ?_⟩
    ext s hs
    rw [Measure.map_apply hmeas hs, withDensity_apply _ (hmeas hs), withDensity_apply _ hs,
      ← lintegral_indicator (hmeas hs), ← lintegral_indicator hs]
    have hfun : (planarRot θ ⁻¹' s).indicator ρ = fun z => s.indicator ρ (planarRot θ z) := by
      funext z
      by_cases hz : planarRot θ z ∈ s
      · rw [indicator_of_mem (show z ∈ planarRot θ ⁻¹' s from hz), indicator_of_mem hz, hρ]
      · rw [indicator_of_notMem (show z ∉ planarRot θ ⁻¹' s from hz), indicator_of_notMem hz]
    rw [hfun, hvol.lintegral_comp (hρm.indicator hs)]

/-- The rotation `(x, y) ↦ (sin θ • x + cos θ • y, cos θ • x - sin θ • y)` of a pair of
vectors in `ι → ℝ`. -/
def pairRot {ι : Type} (θ : ℝ) (z : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (Real.sin θ • z.1 + Real.cos θ • z.2, Real.cos θ • z.1 - Real.sin θ • z.2)

/-- `pairRot` is jointly continuous in the angle and the pair. -/
theorem continuous_pairRot {ι : Type} :
    Continuous (fun q : ℝ × ((ι → ℝ) × (ι → ℝ)) => pairRot q.1 q.2) := by
  unfold pairRot
  fun_prop

/-- Law `μ ⊗ μ`, `μ = gaussianProduct v` on `ι → ℝ` (finite `ι`, any variances, zero allowed). For
every `θ`, `pairRot θ` preserves `μ ⊗ μ`; in particular `(sin θ X + cos θ Y, cos θ X - sin θ Y)`
is again a pair of independent `μ`-vectors. -/
theorem measurePreserving_pairRot {ι : Type} [Fintype ι] (v : ι → ℝ≥0) (θ : ℝ) :
    MeasurePreserving (pairRot θ) ((gaussianProduct v).prod (gaussianProduct v))
      ((gaussianProduct v).prod (gaussianProduct v)) := by
  have hγ : ∀ i, IsProbabilityMeasure (gaussianReal 0 (v i)) := fun i =>
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (v i)
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι
  have he : MeasurePreserving e (Measure.pi fun i => (gaussianReal 0 (v i)).prod
      (gaussianReal 0 (v i))) ((gaussianProduct v).prod (gaussianProduct v)) :=
    measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι _ _
  have hR : MeasurePreserving (fun (w : ι → ℝ × ℝ) i => planarRot θ (w i))
      (Measure.pi fun i => (gaussianReal 0 (v i)).prod (gaussianReal 0 (v i)))
      (Measure.pi fun i => (gaussianReal 0 (v i)).prod (gaussianReal 0 (v i))) :=
    measurePreserving_pi _ _ fun i => measurePreserving_planarRot_gaussian (v i) θ
  have hcomp := (he.comp hR).comp (he.symm e)
  convert hcomp using 1
  funext z
  ext i <;> simp [e, pairRot, planarRot_apply, MeasurableEquiv.arrowProdEquivProdArrow,
    Equiv.arrowProdEquivProdArrow]

end BlockBand.GaussianCalculus
