module

public import Mathlib
public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Model.Construction.GaussianWeakIntegrationByParts

/-!
# Lebesgue density of the centered Gaussian product law

When every variance is nonzero, `gaussianProduct v` on `ι → ℝ` is Lebesgue measure with the
continuous density `∏ⱼ gaussianPDFReal 0 (v j) (x j)`, so integrability and integrals against it
are density-weighted Lebesgue ones. A coordinate of variance zero vanishes almost surely.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianCalculus

open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι]

/-- The product Gaussian density `x ↦ ∏ⱼ gaussianPDFReal 0 (v j) (x j)` on `ι → ℝ`
(with respect to Lebesgue measure `volume = Measure.pi (fun _ => volume)`). -/
def productDensity (v : ι → ℝ≥0) (x : ι → ℝ) : ℝ :=
  ∏ j, gaussianPDFReal 0 (v j) (x j)

/-- The product Gaussian density is nonnegative. -/
theorem productDensity_nonneg (v : ι → ℝ≥0) (x : ι → ℝ) : 0 ≤ productDensity v x :=
  Finset.prod_nonneg fun j _ => gaussianPDFReal_nonneg 0 (v j) (x j)

/-- The product Gaussian density is continuous on `ι → ℝ`. -/
theorem continuous_productDensity (v : ι → ℝ≥0) : Continuous (productDensity v) :=
  continuous_finsetProd _ fun j _ =>
    ((Model.Construction.contDiff_gaussianDensity 0 (v j)).continuous).comp (continuous_apply j)

/-- The indicator of a box times the product density is the product of the
one-dimensional indicator-densities. -/
theorem indicator_pi_productDensity (v : ι → ℝ≥0) (s : ι → Set ℝ) (x : ι → ℝ) :
    (univ.pi s).indicator (productDensity v) x =
      ∏ j, (s j).indicator (gaussianPDFReal 0 (v j)) (x j) := by
  by_cases hx : x ∈ univ.pi s
  · rw [indicator_of_mem hx]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [indicator_of_mem (hx j (mem_univ j))]
  · rw [indicator_of_notMem hx]
    simp only [mem_pi, mem_univ, true_implies, not_forall] at hx
    obtain ⟨j, hj⟩ := hx
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (indicator_of_notMem hj _)).symm

/-- `gaussianProduct v` is Lebesgue measure with the product density, when every
coordinate variance is nonzero. -/
theorem gaussianProduct_eq_withDensity (v : ι → ℝ≥0) (hv : ∀ j, v j ≠ 0) :
    gaussianProduct v =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (productDensity v x)) := by
  unfold gaussianProduct
  apply Measure.pi_eq
  intro s hs
  have hS : MeasurableSet (univ.pi s) := MeasurableSet.univ_pi hs
  have hint1 (j : ι) : Integrable ((s j).indicator (gaussianPDFReal 0 (v j))) :=
    (integrable_gaussianPDFReal 0 (v j)).indicator (hs j)
  have hnn1 (j : ι) (y : ℝ) : 0 ≤ (s j).indicator (gaussianPDFReal 0 (v j)) y :=
    indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 (v j) y) y
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  have hind : (univ.pi s).indicator (fun x => ENNReal.ofReal (productDensity v x)) =
      fun x => ENNReal.ofReal (∏ j, (s j).indicator (gaussianPDFReal 0 (v j)) (x j)) := by
    funext x
    rw [← indicator_pi_productDensity]
    by_cases hx : x ∈ univ.pi s
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, ENNReal.ofReal_zero]
  rw [hind, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [volume_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [gaussianReal_of_var_ne_zero 0 (hv j), withDensity_apply _ (hs j),
        ← lintegral_indicator (hs j), ofReal_integral_eq_lintegral_ofReal (hint1 j)
          (Filter.Eventually.of_forall (hnn1 j))]
      congr 1
      funext y
      by_cases hy : y ∈ s j
      · simp only [indicator_of_mem hy, gaussianPDF]
      · simp only [indicator_of_notMem hy, ENNReal.ofReal_zero]
    · exact fun j _ => integral_nonneg (hnn1 j)
  · rw [volume_pi]
    exact Integrable.fintype_prod (f := fun j => (s j).indicator (gaussianPDFReal 0 (v j))) hint1
  · exact Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun j _ => hnn1 j (x j)

/-- Gaussian-product integrability is density-weighted Lebesgue integrability. -/
theorem integrable_gaussianProduct_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ι → ℝ≥0) (hv : ∀ j, v j ≠ 0) (h : (ι → ℝ) → E) :
    Integrable h (gaussianProduct v) ↔ Integrable (fun x => productDensity v x • h x) := by
  rw [gaussianProduct_eq_withDensity v hv]
  have hm : Measurable (fun x => ENNReal.ofReal (productDensity v x)) :=
    ENNReal.measurable_ofReal.comp (continuous_productDensity v).measurable
  simpa only [ENNReal.toReal_ofReal (productDensity_nonneg v _)] using
    integrable_withDensity_iff_integrable_smul' (μ := volume) (g := h) hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)

/-- Bochner integrals against the Gaussian product law are density-weighted Lebesgue
integrals. -/
theorem integral_gaussianProduct_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ι → ℝ≥0) (hv : ∀ j, v j ≠ 0) (h : (ι → ℝ) → E) :
    (∫ x, h x ∂gaussianProduct v) = ∫ x, productDensity v x • h x := by
  rw [gaussianProduct_eq_withDensity v hv]
  have hm : Measurable (fun x => ENNReal.ofReal (productDensity v x)) :=
    ENNReal.measurable_ofReal.comp (continuous_productDensity v).measurable
  simpa only [ENNReal.toReal_ofReal (productDensity_nonneg v _)] using
    integral_withDensity_eq_integral_toReal_smul (μ := volume) hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) h

/-- A degenerate coordinate vanishes almost surely under the Gaussian product law. -/
theorem ae_gaussianProduct_coord_eq_zero (v : ι → ℝ≥0) (i : ι) (hi : v i = 0) :
    ∀ᵐ x ∂gaussianProduct v, x i = 0 := by
  have : ∀ j, IsProbabilityMeasure (gaussianReal 0 (v j)) := fun j =>
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (v j)
  have hmp := measurePreserving_eval (fun j => gaussianReal 0 (v j)) i
  have h0 : ∀ᵐ y ∂gaussianReal 0 (v i), y = 0 := by
    rw [hi, gaussianReal_zero_var, ae_dirac_eq]
    exact Filter.eventually_pure.mpr rfl
  exact hmp.quasiMeasurePreserving.ae h0

end BlockBand.GaussianCalculus
