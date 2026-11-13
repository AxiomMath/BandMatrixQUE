module

public import BlockBand.Palm.ScalarGaussianWeight
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Scalar Palm localization

Gaussian tail bounds for the scalar component of variance `c₀/N²`, and the resulting
exponentially small bound on the Palm kernel off the spectral window
(`scalarWeight_le_offWindow`).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The scalar Gaussian of variance `c₀/N²` has a sub-Gaussian moment generating function. -/
theorem scalarGaussian_hasSubgaussianMGF (c₀ : ℝ≥0) (N : ℕ) :
    HasSubgaussianMGF (fun g : ℝ => g) (scalarVariance c₀ N)
      (gaussianReal 0 (scalarVariance c₀ N)) := by
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, ?_⟩
  intro t
  rw [mgf_fun_id_gaussianReal]
  simp

/-- Right Gaussian tail for the scalar of variance `c₀/N²`. -/
theorem scalarGaussian_right_tail (c₀ : ℝ≥0) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (gaussianReal 0 (scalarVariance c₀ N)).real {g | δ ≤ g} ≤
      Real.exp (-δ ^ 2 / (2 * scalarVariance c₀ N)) :=
  (scalarGaussian_hasSubgaussianMGF c₀ N).measure_ge_le hδ

/-- Two-sided Gaussian tail for the scalar of variance `c₀/N²` (used with `δ = N^(-1+ε)/4`). -/
theorem scalarGaussian_abs_tail (c₀ : ℝ≥0) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (gaussianReal 0 (scalarVariance c₀ N)).real {g | δ ≤ |g|} ≤
      2 * Real.exp (-δ ^ 2 / (2 * scalarVariance c₀ N)) := by
  have hr := scalarGaussian_right_tail c₀ N hδ
  have hl := (scalarGaussian_hasSubgaussianMGF c₀ N).neg.measure_ge_le hδ
  have hset : {g : ℝ | δ ≤ |g|} = {g : ℝ | δ ≤ g} ∪ {g : ℝ | δ ≤ -g} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hset]
  apply (measureReal_union_le _ _).trans
  change (gaussianReal 0 (scalarVariance c₀ N)).real {g | δ ≤ g} +
    (gaussianReal 0 (scalarVariance c₀ N)).real {g | δ ≤ -g} ≤ _
  have hl' : (gaussianReal 0 (scalarVariance c₀ N)).real {g | δ ≤ -g} ≤
      Real.exp (-δ ^ 2 / (2 * scalarVariance c₀ N)) := hl
  linarith

/-- Pointwise Gaussian tail of the Palm kernel, with its normalizing prefactor. -/
theorem scalarWeight_le_gaussian_tail (c₀ : ℝ≥0) (N : ℕ)
    {E ν δ : ℝ} (hδ : 0 ≤ δ) (hfar : δ ≤ |E - ν|) :
    scalarWeight c₀ N E ν ≤
      (Real.sqrt (2 * Real.pi * scalarVariance c₀ N))⁻¹ *
        Real.exp (-δ ^ 2 / (2 * scalarVariance c₀ N)) := by
  unfold scalarWeight gaussianPDFReal
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  have hsq : δ ^ 2 ≤ (E - ν) ^ 2 := by
    nlinarith [sq_abs (E - ν), abs_nonneg (E - ν)]
  simp only [sub_zero]
  exact div_le_div_of_nonneg_right (neg_le_neg hsq) (by positivity)

/-- If the shifted terminal eigenvalue is outside its window and the scalar is small, then the
unshifted coordinate is at least `3δ/4` from `E`. -/
theorem scalar_unshifted_distance_ge
    {E ν g δ : ℝ} (hg : |g| ≤ δ / 4) (hfar : δ ≤ |ν + g - E|) :
    3 * δ / 4 ≤ |E - ν| := by
  have ht : |ν + g - E| ≤ |ν - E| + |g| := by
    simpa only [show ν + g - E = (ν - E) + g by ring] using abs_add_le (ν - E) g
  rw [abs_sub_comm ν E] at ht
  linarith

/-- Exponentially small off-window bound on the Palm kernel: under `|g| ≤ δ/4` and
`|ν + g - E| ≥ δ`, the exponent is `-9δ²/(32 c₀/N²)`. -/
theorem scalarWeight_le_offWindow (c₀ : ℝ≥0) (N : ℕ)
    {E ν g δ : ℝ} (hδ : 0 ≤ δ) (hg : |g| ≤ δ / 4)
    (hfar : δ ≤ |ν + g - E|) :
    scalarWeight c₀ N E ν ≤
      (Real.sqrt (2 * Real.pi * scalarVariance c₀ N))⁻¹ *
        Real.exp (-(3 * δ / 4) ^ 2 / (2 * scalarVariance c₀ N)) :=
  scalarWeight_le_gaussian_tail c₀ N (by positivity) (scalar_unshifted_distance_ge hg hfar)

end BlockBand.Palm
