module

public import BlockBand.Endpoints.Response.TaggedConvexOrderCoreDefs
public import BlockBand.Endpoints.Response.ResponseVarianceGaussian
public import BlockBand.Counting.CircularGaussianMoments
public import BlockBand.Endpoints.Response.TaggedConvexOrderGaussian

/-!
# Gaussian concentration of a quadratic form

For a standard complex Gaussian `h ~ circularVectorLaw ι` and a Hermitian `B` with eigenvalues
`λ`, `E h*Bh = Σλ` and `E(h*Bh - d)² = (Σλ - d)² + Σλ²` (`tcc_quadForm_centered`). This is the
concentration used for the initial value of the tagged convex comparison.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal

theorem tcc_integrable_sq_half :
    Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 (1 / 2 : ℝ≥0)) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (2 : ℝ≥0)).integrable_norm_pow
    (p := 2) (by norm_num)
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- `E|h_a|² = 1` under `circularVectorLaw`. -/
theorem tcc_integral_normSq_coord {ι : Type} [Fintype ι] (a : ι) :
    Integrable (fun h : ι → ℂ => Complex.normSq (h a)) (circularVectorLaw ι) ∧
      ∫ h, Complex.normSq (h a) ∂circularVectorLaw ι = 1 := by
  set P := Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)
  have hc : Measurable (fun (r : ι × Fin 2 → ℝ) (a : ι) =>
      (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I) := by fun_prop
  have hm : Measurable (fun h : ι → ℂ => Complex.normSq (h a)) :=
    Complex.continuous_normSq.measurable.comp (measurable_pi_apply a)
  have hpt : (fun h : ι → ℂ => Complex.normSq (h a)) ∘
      (fun (r : ι × Fin 2 → ℝ) (a : ι) => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I) =
      fun r => r (a, 0) ^ 2 + r (a, 1) ^ 2 := by
    funext r; simp [Complex.normSq_apply, pow_two]
  have hi (p : ι × Fin 2) : Integrable (fun r : ι × Fin 2 → ℝ => r p ^ 2) P :=
    integrable_comp_eval (μ := fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) (i := p)
      (f := fun y : ℝ => y ^ 2) tcc_integrable_sq_half
  have hv (p : ι × Fin 2) : ∫ r, r p ^ 2 ∂P = 1 / 2 := by
    rw [integral_comp_eval (μ := fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) (i := p)
      (f := fun y : ℝ => y ^ 2) tcc_integrable_sq_half.aestronglyMeasurable,
      BlockBand.Counting.integral_sq_gaussianReal]
    simp
  constructor
  · unfold circularVectorLaw
    rw [integrable_map_measure hm.aestronglyMeasurable hc.aemeasurable, hpt]
    exact (hi _).add (hi _)
  · unfold circularVectorLaw
    rw [integral_map hc.aemeasurable hm.aestronglyMeasurable]
    have := congrArg (fun f => ∫ r, f r ∂P) hpt
    simp only [Function.comp_def] at this
    rw [this, integral_add (hi _) (hi _), hv, hv]
    norm_num

/-- `E Σ_k λ_k|h_k|² = Σ_k λ_k`. -/
theorem tcc_integral_diag {ι : Type} [Fintype ι] (l : ι → ℝ) :
    Integrable (fun h => rvG_diag l h) (circularVectorLaw ι) ∧
      ∫ h, rvG_diag l h ∂circularVectorLaw ι = ∑ k, l k := by
  unfold rvG_diag
  refine ⟨integrable_finsetSum _ fun k _ => (tcc_integral_normSq_coord k).1.const_mul _, ?_⟩
  rw [integral_finsetSum _ fun k _ => (tcc_integral_normSq_coord k).1.const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, (tcc_integral_normSq_coord k).2, mul_one]

/-- First and centered second moments of a Hermitian quadratic form: with `λ` the eigenvalues,
`E h*Bh = Σλ` and `E(h*Bh - d)² = (Σλ - d)² + Σλ²`. -/
theorem tcc_quadForm_centered {ι : Type} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (d : ℝ) :
    Integrable (fun h => quadForm B h) (circularVectorLaw ι) ∧
      ∫ h, quadForm B h ∂circularVectorLaw ι = ∑ k, hB.eigenvalues k ∧
      Integrable (fun h => (quadForm B h - d) ^ 2) (circularVectorLaw ι) ∧
      ∫ h, (quadForm B h - d) ^ 2 ∂circularVectorLaw ι =
        (∑ k, hB.eigenvalues k - d) ^ 2 + ∑ k, hB.eigenvalues k ^ 2 := by
  obtain ⟨-, i2, e2, -⟩ := rvG_quadForm_moments hB
  set U : Matrix ι ι ℂ := (hB.eigenvectorUnitary : Matrix ι ι ℂ)
  have hmap := rvG_circularVectorLaw_map_unitary U hB.eigenvectorUnitary.2
  have hU_m : Measurable (fun h : ι → ℂ => U *ᵥ h) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hmeas : AEStronglyMeasurable (fun h => quadForm B h)
      ((circularVectorLaw ι).map (fun h => U *ᵥ h)) :=
    (rvG_continuous_quadForm B).aestronglyMeasurable
  have hprob := tco_isProbabilityMeasure_circularVectorLaw (ι := ι)
  have i1 : Integrable (fun h => quadForm B h) (circularVectorLaw ι) := by
    rw [← hmap, integrable_map_measure hmeas hU_m.aemeasurable]
    simp only [Function.comp_def, U, rvG_quadForm_eigen]
    exact (tcc_integral_diag hB.eigenvalues).1
  have e1 : ∫ h, quadForm B h ∂circularVectorLaw ι = ∑ k, hB.eigenvalues k := by
    conv_lhs => rw [← hmap]
    rw [integral_map hU_m.aemeasurable hmeas]
    simp_rw [U, rvG_quadForm_eigen]
    exact (tcc_integral_diag hB.eigenvalues).2
  have hexp : (fun h => (quadForm B h - d) ^ 2) =
      fun h => quadForm B h ^ 2 - 2 * d * quadForm B h + d ^ 2 := by
    funext h; ring
  have i2' : Integrable (fun h => (quadForm B h - d) ^ 2) (circularVectorLaw ι) := by
    rw [hexp]; exact (i2.sub (i1.const_mul _)).add (integrable_const _)
  refine ⟨i1, e1, i2', ?_⟩
  have j1 : Integrable (fun h => quadForm B h ^ 2 - 2 * d * quadForm B h)
      (circularVectorLaw ι) := i2.sub (i1.const_mul _)
  rw [hexp, integral_add j1 (integrable_const _), integral_sub i2 (i1.const_mul _),
    integral_const_mul, e2, e1, integral_const]
  simp
  ring

end BlockBand.Endpoints
