module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Rotation invariance and directional moments of the standard Gaussian

The independent standard Gaussian pair `(X, Y)` is invariant under rotations
`(X cos θ + Y sin θ, -X sin θ + Y cos θ)`; for a fixed vector `v`, `⟨v, X⟩` is a centred normal
variable of variance `‖v‖²`, so `E |⟨v, X⟩|^p = ‖v‖^p E |g|^p` with `g` standard normal.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.GaussianGradient
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The independent standard Gaussian pair is rotation invariant. -/
theorem standardGaussianPair_rotation (θ : ℝ) :
    ((stdGaussian E).prod (stdGaussian E)).map (ContinuousLinearMap.rotation θ) =
      (stdGaussian E).prod (stdGaussian E) := by
  apply IsGaussian.map_rotation_eq_self
  simp

/-- Every inner product with a standard Gaussian vector is a centred normal variable with variance
the squared norm. -/
theorem standardGaussian_inner_law (v : E) :
    (stdGaussian E).map (innerSL ℝ v) =
      gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]

/-- The directional law is the standard real Gaussian scaled by the norm of the vector, including
the zero vector. -/
theorem standardGaussian_inner_law_scaled (v : E) :
    (stdGaussian E).map (innerSL ℝ v) =
      (gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x) := by
  rw [standardGaussian_inner_law, gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp [Real.toNNReal_of_nonneg]

/-- The `p`-th absolute moment of the real standard normal. -/
def normalMoment (p : ℝ) : ℝ := ∫ x : ℝ, ‖x‖ ^ p ∂gaussianReal 0 1

/-- The `p`-th absolute moment of the real standard normal is finite. -/
theorem integrable_normalMoment (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun x : ℝ => ‖x‖ ^ p) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) (ENNReal.ofReal p) (by simp)).integrable_norm_rpow'
  simpa only [id_eq, ENNReal.toReal_ofReal hp] using h

/-- The normal `p`-th moment is strictly positive for every `p ≥ 0`, including `p = 0`. -/
theorem normalMoment_pos (p : ℝ) (hp : 0 ≤ p) : 0 < normalMoment p := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hs : {x : ℝ | x ≠ 0} ⊆ Function.support (fun x : ℝ => ‖x‖ ^ p) := by
    intro x hx
    exact ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) p)
  have hm : gaussianReal 0 1 {x : ℝ | x ≠ 0} = 1 := by
    change gaussianReal 0 1 ({0} : Set ℝ)ᶜ = 1
    rw [measure_compl (measurableSet_singleton _) (by simp)]
    simp
  unfold normalMoment
  apply (integral_pos_iff_support_of_nonneg (fun x => Real.rpow_nonneg (norm_nonneg x) p)
    (integrable_normalMoment p hp)).2
  have hmpos : 0 < gaussianReal 0 1 {x : ℝ | x ≠ 0} := by rw [hm]; exact zero_lt_one
  exact hmpos.trans_le (measure_mono hs)

/-- The directional `p`-th moment: `E |⟨v, X⟩|^p = ‖v‖^p E |g|^p`. -/
theorem integral_standardGaussian_inner_rpow (v : E) (p : ℝ) :
    (∫ y : E, ‖⟪v, y⟫_ℝ‖ ^ p ∂stdGaussian E) = ‖v‖ ^ p * normalMoment p := by
  have hf : Measurable (fun x : ℝ => ‖x‖ ^ p) := by fun_prop
  calc
    (∫ y : E, ‖⟪v, y⟫_ℝ‖ ^ p ∂stdGaussian E) =
        ∫ x : ℝ, ‖x‖ ^ p ∂(stdGaussian E).map (innerSL ℝ v) := by
      rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
      rfl
    _ = ∫ x : ℝ, ‖x‖ ^ p ∂(gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x) := by
      rw [standardGaussian_inner_law_scaled]
    _ = ∫ x : ℝ, ‖‖v‖ * x‖ ^ p ∂gaussianReal 0 1 := by
      rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
    _ = ‖v‖ ^ p * normalMoment p := by
      simp_rw [norm_mul, norm_norm, Real.mul_rpow (norm_nonneg v) (norm_nonneg _)]
      rw [integral_const_mul]
      rfl

/-- The standard normal `p`-th moment as an extended nonnegative integral. -/
def normalEMoment (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ENNReal.ofReal (‖x‖ ^ p) ∂gaussianReal 0 1

/-- The directional moment as an extended nonnegative integral. -/
theorem lintegral_standardGaussian_inner_rpow (v : E) (p : ℝ) :
    (∫⁻ y : E, ENNReal.ofReal (‖⟪v, y⟫_ℝ‖ ^ p) ∂stdGaussian E) =
      ENNReal.ofReal (‖v‖ ^ p) * normalEMoment p := by
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (‖x‖ ^ p)) := by fun_prop
  calc
    (∫⁻ y : E, ENNReal.ofReal (‖⟪v, y⟫_ℝ‖ ^ p) ∂stdGaussian E) =
        ∫⁻ x : ℝ, ENNReal.ofReal (‖x‖ ^ p) ∂(stdGaussian E).map (innerSL ℝ v) := by
      rw [lintegral_map hf (by fun_prop)]
      rfl
    _ = ∫⁻ x : ℝ, ENNReal.ofReal (‖x‖ ^ p) ∂(gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x) := by
      rw [standardGaussian_inner_law_scaled]
    _ = ∫⁻ x : ℝ, ENNReal.ofReal (‖‖v‖ * x‖ ^ p) ∂gaussianReal 0 1 := by
      rw [lintegral_map hf (by fun_prop)]
    _ = _ := by
      simp_rw [norm_mul, norm_norm, Real.mul_rpow (norm_nonneg v) (norm_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg v) p)]
      rw [lintegral_const_mul _ hf]
      rfl

/-- The extended normal moment is finite and equals the real integral for all `p ≥ 0`. -/
theorem normalEMoment_eq_ofReal (p : ℝ) (hp : 0 ≤ p) :
    normalEMoment p = ENNReal.ofReal (normalMoment p) := by
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_normalMoment p hp)
    (ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg x) p))).symm

/-- Rotation averaging for nonnegative functions of the Gaussian pair; only measurability is
assumed. -/
theorem lintegral_standardGaussianPair_rotation (F : E × E → ℝ≥0∞)
    (hF : Measurable F) (θ : ℝ) :
    (∫⁻ q, F (ContinuousLinearMap.rotation θ q) ∂(stdGaussian E).prod (stdGaussian E)) =
      ∫⁻ q, F q ∂(stdGaussian E).prod (stdGaussian E) := by
  rw [← lintegral_map hF (by fun_prop), standardGaussianPair_rotation]

/-- Tonelli factorization of a weighted directional moment; the outer integral may be infinite. -/
theorem lintegral_weighted_directional (g : E → E) (hg : Measurable g)
    (w : E → ℝ≥0∞) (hw : Measurable w) (p : ℝ) :
    (∫⁻ q : E × E, w q.1 * ENNReal.ofReal (‖⟪g q.1, q.2⟫_ℝ‖ ^ p)
      ∂(stdGaussian E).prod (stdGaussian E)) =
      normalEMoment p * (∫⁻ x : E, w x * ENNReal.ofReal (‖g x‖ ^ p) ∂stdGaussian E) := by
  have hf : Measurable (fun q : E × E =>
      w q.1 * ENNReal.ofReal (‖⟪g q.1, q.2⟫_ℝ‖ ^ p)) := by fun_prop
  rw [lintegral_prod _ hf.aemeasurable]
  have inner (x : E) :
      (∫⁻ y : E, w x * ENNReal.ofReal (‖⟪g x, y⟫_ℝ‖ ^ p) ∂stdGaussian E) =
        normalEMoment p * (w x * ENNReal.ofReal (‖g x‖ ^ p)) := by
    rw [lintegral_const_mul _ (by fun_prop), lintegral_standardGaussian_inner_rpow]
    ring
  simp_rw [inner]
  exact lintegral_const_mul _ (by fun_prop)

end BlockBand.DeterminantScore.GaussianGradient
