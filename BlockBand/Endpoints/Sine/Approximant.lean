module

public import BlockBand.Endpoints.Sine.FiniteFredholm
public import BlockBand.Endpoints.Sine.TrigSystem
public import BlockBand.Endpoints.VagueMeasurability

/-!
# Circular projection approximants of the sine law

The approximant `cueLaw M` is the determinantal point process of `2M+1` points on the window
`cueWindow M` with density `(N!)⁻¹ det [cueBasis M i (x j)]²`. Its Laplace functional is the
Fredholm series of the kernel `cueKernel M` (`integral_exp_neg_cueLaw`), by the Andréief identity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory
open scoped ENNReal NNReal

/-- Reference measure of the approximant: Lebesgue measure on `cueWindow M`. -/
def cueMeasure (M : ℕ) : Measure ℝ := volume.restrict (cueWindow M)

instance (M : ℕ) : IsFiniteMeasure (cueMeasure M) := by
  unfold cueMeasure; infer_instance

/-- Determinantal density `(N!)⁻¹ det [cueBasis M i (x j)]²` on `Fin (2M+1) → ℝ`. -/
def cueDensity (M : ℕ) (x : Fin (2 * M + 1) → ℝ) : ℝ :=
  ((Fintype.card (Fin (2 * M + 1))).factorial : ℝ)⁻¹ *
    (Matrix.of fun i j => cueBasis M i (x j)).det ^ 2

theorem cueDensity_nonneg (M : ℕ) (x : Fin (2 * M + 1) → ℝ) : 0 ≤ cueDensity M x := by
  unfold cueDensity; positivity

theorem continuous_cueDensity (M : ℕ) : Continuous (cueDensity M) := by
  unfold cueDensity
  refine continuous_const.mul (Continuous.pow ?_ 2)
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun i j => ?_
  exact (continuous_cueBasis M i).comp (continuous_apply j)

theorem measurable_cueDensity (M : ℕ) : Measurable (cueDensity M) :=
  (continuous_cueDensity M).measurable

/-- The finite Fredholm identity for the approximant, for every measurable
bounded weight `φ`. -/
theorem integral_cueDensity_mul_prod (M : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hφb : ∃ C, ∀ a, |φ a| ≤ C) :
    ∫ x, cueDensity M x * ∏ j, (1 - φ (x j)) ∂Measure.pi (fun _ => cueMeasure M) =
      fredholmSeries (cueKernel M) (cueMeasure M) φ := by
  rw [finiteProjection_fredholmSeries_eq (cueMeasure M) (cueBasis M) (measurable_cueBasis M)
    ⟨1, fun i a => abs_cueBasis_le_one M i a⟩ (cueBasis_orthonormal M) (cueKernel M)
    (fun _ _ => rfl) φ hφ hφb, ← integral_const_mul]
  congr 1
  ext x
  unfold cueDensity
  ring

theorem integral_cueDensity (M : ℕ) :
    ∫ x, cueDensity M x ∂Measure.pi (fun _ => cueMeasure M) = 1 := by
  have h := det_one_sub_weightedGram_eq_integral (cueMeasure M) (cueBasis M)
    (measurable_cueBasis M) ⟨1, fun i a => abs_cueBasis_le_one M i a⟩
    (cueBasis_orthonormal M) (fun _ => 0) measurable_const ⟨0, fun _ => by simp⟩
  have hW : weightedGram (cueMeasure M) (cueBasis M) (fun _ => 0) = 0 := by
    ext p q; simp [weightedGram]
  rw [hW, sub_zero, Matrix.det_one] at h
  rw [h, ← integral_const_mul]
  congr 1
  ext x
  simp [cueDensity]

/-- The law of the `2M+1` approximant points on `Fin (2M+1) → ℝ`. -/
def cuePointLaw (M : ℕ) : Measure (Fin (2 * M + 1) → ℝ) :=
  (Measure.pi fun _ => cueMeasure M).withDensity fun x => ((cueDensity M x).toNNReal : ℝ≥0∞)

theorem integrable_cueDensity (M : ℕ) :
    Integrable (cueDensity M) (Measure.pi fun _ => cueMeasure M) :=
  Integrable.of_integral_ne_zero (by rw [integral_cueDensity]; exact one_ne_zero)

instance (M : ℕ) : IsProbabilityMeasure (cuePointLaw M) := by
  constructor
  rw [cuePointLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change ∫⁻ x, ENNReal.ofReal (cueDensity M x) ∂_ = 1
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cueDensity M)
    (Filter.Eventually.of_forall (cueDensity_nonneg M)), integral_cueDensity, ENNReal.ofReal_one]

theorem integral_cuePointLaw (M : ℕ) (g : (Fin (2 * M + 1) → ℝ) → ℝ) :
    ∫ x, g x ∂cuePointLaw M =
      ∫ x, cueDensity M x * g x ∂Measure.pi (fun _ => cueMeasure M) := by
  rw [cuePointLaw, integral_withDensity_eq_integral_smul
    ((measurable_cueDensity M).real_toNNReal)]
  congr 1
  ext x
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (cueDensity_nonneg M x)]

/-- The approximant as a law on the vague state space. -/
def cueLaw (M : ℕ) : ProbabilityMeasure (VaguePointMeasure ℝ) :=
  ⟨(cuePointLaw M).map finitePointMeasure, inferInstance⟩

theorem measurable_finitePointMeasure_cue (M : ℕ) :
    Measurable (finitePointMeasure : (Fin (2 * M + 1) → ℝ) → VaguePointMeasure ℝ) :=
  measurable_finitePointMeasure

/-- Laplace functional of the approximant. For every `f` in `C_c(ℝ)`,
`E exp (-ξ(f)) = fredholmSeries (cueKernel M) (volume.restrict (cueWindow M)) (1 - exp (-f))`. -/
theorem integral_exp_neg_cueLaw (M : ℕ) (f : CompactlySupportedContinuousMap ℝ ℝ) :
    ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(cueLaw M : Measure (VaguePointMeasure ℝ)) =
      fredholmSeries (cueKernel M) (cueMeasure M) (fun x => 1 - Real.exp (-f x)) := by
  change ∫ ξ, _ ∂((cuePointLaw M).map finitePointMeasure) = _
  rw [integral_map (measurable_finitePointMeasure_cue M).aemeasurable, integral_cuePointLaw]
  swap
  · exact (Real.continuous_exp.measurable.comp (measurable_coordinate f).neg).aestronglyMeasurable
  have hb : ∃ C, ∀ a, |1 - Real.exp (-f a)| ≤ C := by
    obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    exact ⟨1 + Real.exp C, fun a => by
      refine (abs_sub _ _).trans ?_
      rw [abs_one, abs_of_pos (Real.exp_pos _)]
      gcongr
      have := hC a
      rw [Real.norm_eq_abs] at this
      change |f a| ≤ C at this
      linarith [neg_abs_le (f a)]⟩
  rw [← integral_cueDensity_mul_prod M _ (by fun_prop) hb]
  congr 1
  ext x
  rw [integral_finitePointMeasure x f f.continuous, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp

end BlockBand.Endpoints
