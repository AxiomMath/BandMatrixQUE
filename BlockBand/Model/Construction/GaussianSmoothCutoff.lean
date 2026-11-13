module

public import BlockBand.Model.Construction.GaussianIntegrationByParts
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smooth cutoffs for the weak Gaussian identity

An explicit sequence of expanding smooth bump functions on `ℝ` with uniformly bounded
derivatives, along which integrals of an integrable function multiplied by the cutoff, or by its
derivative, converge as needed for the weak Gaussian integration by parts.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction
open MeasureTheory Filter
open scoped Topology

/-- Concrete expanding bump on the real line. -/
def gaussianSmoothCutoff (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (n : ℝ) + 1
  rOut := 2 * ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- All cutoffs are rescalings of one fixed smooth bump. -/
theorem gaussianSmoothCutoff_scaling (n : ℕ) (x : ℝ) :
    gaussianSmoothCutoff n x = gaussianSmoothCutoff 0 (x / ((n : ℝ) + 1)) := by
  have hR : (n : ℝ) + 1 ≠ 0 := by positivity
  have hratio : 2 * ((n : ℝ) + 1) / ((n : ℝ) + 1) = 2 := by field_simp
  simp only [ContDiffBump.apply, gaussianSmoothCutoff, Nat.cast_zero, zero_add,
    mul_one, inv_one, sub_zero, div_one, smul_eq_mul]
  rw [hratio]
  congr 1
  ring

/-- Exact derivative scaling, with the inverse expanding radius. -/
theorem deriv_gaussianSmoothCutoff (n : ℕ) (x : ℝ) :
    deriv (gaussianSmoothCutoff n) x =
      deriv (gaussianSmoothCutoff 0) (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
  have hb : Differentiable ℝ (gaussianSmoothCutoff 0) :=
    (show ContDiff ℝ 1 (gaussianSmoothCutoff 0) from (gaussianSmoothCutoff 0).contDiff).differentiable (by norm_num)
  have h := (hb (x / ((n : ℝ) + 1))).hasDerivAt.comp x
    ((hasDerivAt_id x).div_const ((n : ℝ) + 1))
  have he : (fun y => gaussianSmoothCutoff 0 (y / ((n : ℝ) + 1))) =
      gaussianSmoothCutoff n := by
    funext y
    exact (gaussianSmoothCutoff_scaling n y).symm
  simpa only [Function.comp_def, he, id_eq, one_div, ← div_eq_mul_inv] using h.deriv

/-- A single finite derivative bound works for every expanding cutoff. -/
theorem exists_bound_deriv_gaussianSmoothCutoff :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, ‖deriv (gaussianSmoothCutoff n) x‖ ≤ C := by
  have hc : Continuous (deriv (gaussianSmoothCutoff 0)) :=
    (show ContDiff ℝ 1 (gaussianSmoothCutoff 0) from (gaussianSmoothCutoff 0).contDiff).continuous_deriv le_rfl
  have hb : BddAbove (Set.range (fun x => ‖deriv (gaussianSmoothCutoff 0) x‖)) := by
    apply hc.norm.bddAbove_range_of_hasCompactSupport
    exact HasCompactSupport.comp_left (gaussianSmoothCutoff 0).hasCompactSupport.deriv norm_zero
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (Set.mem_range_self 0))
  refine ⟨C, hC0, ?_⟩
  intro n x
  rw [deriv_gaussianSmoothCutoff, norm_div]
  simp only [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  exact (hC (Set.mem_range_self _)).trans (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

/-- At each fixed point both the constant value and its zero derivative are
reached eventually. -/
theorem gaussianSmoothCutoff_eventually (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, gaussianSmoothCutoff n x = 1 ∧
      deriv (gaussianSmoothCutoff n) x = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn : ‖x‖ < (n : ℝ) + 1 := by linarith
  have hx : x ∈ Metric.ball (0 : ℝ) (gaussianSmoothCutoff n).rIn := by
    change dist x 0 < (n : ℝ) + 1
    simpa only [dist_zero_right] using hn
  have he := (gaussianSmoothCutoff n).eventuallyEq_one_of_mem_ball hx
  constructor
  · exact (gaussianSmoothCutoff n).one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  · rw [he.deriv_eq]
    simp

/-- Multiplying an integrable vector-valued function by these concrete cutoffs
converges in Bochner integral, for every measure. -/
theorem integral_gaussianSmoothCutoff_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure ℝ) {f : ℝ → E} (hf : Integrable f μ) :
    Tendsto (fun n : ℕ => ∫ x, gaussianSmoothCutoff n x • f x ∂μ)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact (gaussianSmoothCutoff n).continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable
  · exact hf.norm
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (gaussianSmoothCutoff n).nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) (gaussianSmoothCutoff n).le_one
  · exact Filter.Eventually.of_forall fun x => by
      have he : (fun n : ℕ => gaussianSmoothCutoff n x • f x) =ᶠ[atTop] fun _ => f x := by
        filter_upwards [gaussianSmoothCutoff_eventually x] with n hn
        simp [hn.1]
      exact (tendsto_congr' he).mpr tendsto_const_nhds

/-- The cutoff-derivative error tends to zero using only integrability of f;
the expanding radius need not impose any growth condition on f. -/
theorem integral_deriv_gaussianSmoothCutoff_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure ℝ) {f : ℝ → E} (hf : Integrable f μ) :
    Tendsto (fun n : ℕ => ∫ x, deriv (gaussianSmoothCutoff n) x • f x ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_gaussianSmoothCutoff
  have hc (n : ℕ) : Continuous (deriv (gaussianSmoothCutoff n)) :=
    (show ContDiff ℝ 1 (gaussianSmoothCutoff n) from (gaussianSmoothCutoff n).contDiff).continuous_deriv le_rfl
  have ht : Tendsto (fun n : ℕ => ∫ x, deriv (gaussianSmoothCutoff n) x • f x ∂μ)
      atTop (𝓝 (∫ _ : ℝ, (0 : E) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => C * ‖f x‖)
    · intro n
      exact (hc n).aestronglyMeasurable.smul hf.aestronglyMeasurable
    · exact hf.norm.const_mul C
    · intro n
      exact Filter.Eventually.of_forall fun x => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hC n x) (norm_nonneg _)
    · exact Filter.Eventually.of_forall fun x => by
        have he : (fun n : ℕ => deriv (gaussianSmoothCutoff n) x • f x) =ᶠ[atTop] fun _ => (0 : E) := by
          filter_upwards [gaussianSmoothCutoff_eventually x] with n hn
          simp [hn.2]
        exact (tendsto_congr' he).mpr tendsto_const_nhds
  simpa only [integral_zero] using ht

end BlockBand.Model.Construction
