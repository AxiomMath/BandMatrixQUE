module

public import Mathlib
public import BlockBand.GaussianCalculus.ProductDensity
public import BlockBand.Model.Construction.GaussianIntegrationByParts

/-!
# Coordinate Gaussian integration by parts for everywhere differentiable sections

If `h` is differentiable along coordinate `i` everywhere, with derivative `h'`, then
`E[yᵢ h] = vᵢ E[h']` under `gaussianProduct v`, any variances allowed. The proof resamples
coordinate `i` (`measurePreserving_update`) and integrates by parts in one variable.

Law: `μ = gaussianProduct v` on `ι → ℝ`, finite `ι`, every variance `v i ≥ 0` (zero allowed,
including in the differentiated coordinate). The hypotheses are that `h` is differentiable along
every coordinate-`i` line with derivative `h'`, and that `h`, `h'`, `yᵢ h` are `μ`-integrable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianCalculus

open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Resampling coordinate `i` preserves the Gaussian product law:
`(y, t) ↦ update y i t` maps `μ ⊗ N(0, vᵢ)` to `μ = gaussianProduct v`. -/
theorem measurePreserving_update (v : ι → ℝ≥0) (i : ι) :
    MeasurePreserving (fun q : (ι → ℝ) × ℝ => Function.update q.1 i q.2)
      ((gaussianProduct v).prod (gaussianReal 0 (v i))) (gaussianProduct v) := by
  have hγ : ∀ j, IsProbabilityMeasure (gaussianReal 0 (v j)) := fun j =>
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (v j)
  have hmeas : Measurable (fun q : (ι → ℝ) × ℝ => Function.update q.1 i q.2) :=
    (continuous_fst.update i continuous_snd).measurable
  refine ⟨hmeas, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun q : (ι → ℝ) × ℝ => Function.update q.1 i q.2) ⁻¹' univ.pi s =
      (univ.pi fun j => if j = i then univ else s j) ×ˢ s i := by
    ext ⟨y, t⟩
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · rw [ite_eq_left hj]
          exact mem_univ _
        · rw [ite_eq_right hj]
          have := h j
          rwa [Function.update_of_ne hj] at this
      · have := h i
        rwa [Function.update_self] at this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj
        rwa [Function.update_self]
      · rw [Function.update_of_ne hj]
        have := h1 j
        rwa [ite_eq_right hj] at this
  rw [hpre, Measure.prod_prod, gaussianProduct, Measure.pi_pi,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => gaussianReal 0 (v j) (s j)) (Finset.mem_univ i),
    ite_eq_left rfl, measure_univ, one_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [ite_eq_right (Finset.ne_of_mem_erase hj)]

/-- Coordinate Gaussian IBP. Law `μ = gaussianProduct v` (any variances, zero allowed). If
`t ↦ h(update y i t)` has derivative `h'(update y i t)` at every `t`, for every `y`, and `h`,
`h'`, `yᵢ h` are `μ`-integrable, then `E[yᵢ h] = vᵢ E[h']`. -/
theorem integral_coord_mul_eq (v : ι → ℝ≥0) (i : ι) {h h' : (ι → ℝ) → ℝ}
    (hderiv : ∀ (y : ι → ℝ) (t : ℝ),
      HasDerivAt (fun s => h (Function.update y i s)) (h' (Function.update y i t)) t)
    (hh : Integrable h (gaussianProduct v)) (hh' : Integrable h' (gaussianProduct v))
    (hc : Integrable (fun y => y i * h y) (gaussianProduct v)) :
    ∫ y, y i * h y ∂gaussianProduct v = (v i : ℝ) * ∫ y, h' y ∂gaussianProduct v := by
  have hγ : ∀ j, IsProbabilityMeasure (gaussianReal 0 (v j)) := fun j =>
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (v j)
  have hμ : IsProbabilityMeasure (gaussianProduct v) := by
    unfold gaussianProduct
    infer_instance
  set μ := gaussianProduct v
  set T : (ι → ℝ) × ℝ → ι → ℝ := fun q => Function.update q.1 i q.2 with hTdef
  have hT : MeasurePreserving T (μ.prod (gaussianReal 0 (v i))) μ := measurePreserving_update v i
  have hcomp (φ : (ι → ℝ) → ℝ) (hφ : Integrable φ μ) :
      Integrable (fun q => φ (T q)) (μ.prod (gaussianReal 0 (v i))) ∧
        ∫ y, φ y ∂μ = ∫ q, φ (T q) ∂μ.prod (gaussianReal 0 (v i)) := by
    have hφ' : Integrable φ (Measure.map T (μ.prod (gaussianReal 0 (v i)))) := by
      rwa [hT.map_eq]
    refine ⟨(integrable_map_measure hφ'.aestronglyMeasurable hT.measurable.aemeasurable).mp hφ',
      ?_⟩
    rw [← integral_map hT.measurable.aemeasurable hφ'.aestronglyMeasurable, hT.map_eq]
  obtain ⟨hcI, hcE⟩ := hcomp _ hc
  obtain ⟨hhI', hhE'⟩ := hcomp _ hh'
  obtain ⟨hhI, -⟩ := hcomp _ hh
  rw [hcE, hhE', integral_prod _ hcI, integral_prod _ hhI', ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hcI.prod_right_ae, hhI'.prod_right_ae, hhI.prod_right_ae] with y hy1 hy2 hy3
  have hupd (t : ℝ) : T (y, t) i = t := by simp [hTdef]
  simp only [hupd] at hy1 ⊢
  exact BlockBand.Model.Construction.centered_gaussian_integration_by_parts (v i)
    (f := fun t => h (T (y, t))) (f' := fun t => h' (T (y, t))) (fun t => hderiv y t) hy3 hy2 hy1

end BlockBand.GaussianCalculus
