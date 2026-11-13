module

public import BlockBand.Endpoints.Sine.Approximant
public import BlockBand.Endpoints.Sine.GramDet
public import BlockBand.Endpoints.Sine.Simple
public import BlockBand.Endpoints.LaplaceDetermination
public import BlockBand.Endpoints.LaplaceLimit

/-!
# Existence and uniqueness of the intensity-one sine law

The sine law is obtained as a limit of the circular projection approximants `cueLaw M`: their
Laplace functionals converge to the sine Laplace functional, their expected counts are bounded,
and the limit law is unique and a.s. simple (`existsUnique_isSineLaw`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter
open scoped ENNReal Topology

theorem abs_det_cueKernel_le_one (M : ℕ) (k : ℕ) (y : Fin k → ℝ) :
    |Matrix.det (fun a b : Fin k => cueKernel M (y a) (y b))| ≤ 1 :=
  abs_kernel_det_le_one (cueBasis M) (cueKernel M) (fun _ _ => rfl) (cueKernel_self M) k y

/-- Every determinant of the sine kernel matrix lies in `[-1, 1]` (in fact in
`[0, 1]`), as the limit of the approximant Gram determinants. -/
theorem abs_det_sineKernel_le_one (k : ℕ) (y : Fin k → ℝ) :
    |Matrix.det (fun a b : Fin k => sineKernel (y a) (y b))| ≤ 1 :=
  abs_det_le_one_of_tendsto (fun M k y => abs_det_cueKernel_le_one M k y)
    (fun x y => tendsto_cueKernel x y) k y

theorem measurable_cueKernel (M : ℕ) : Measurable (Function.uncurry (cueKernel M)) :=
  (continuous_cueKernel M).measurable

/-- Laplace functionals of the approximants converge to the sine Laplace functional, for every
compactly supported continuous `f`. -/
theorem tendsto_integral_exp_neg_cueLaw (f : CompactlySupportedContinuousMap ℝ ℝ) :
    Tendsto (fun M : ℕ => ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure)
        ∂(cueLaw M : Measure (VaguePointMeasure ℝ))) atTop
      (𝓝 (sineLaplaceFunctional f)) := by
  set φ : ℝ → ℝ := fun x => 1 - Real.exp (-f x)
  have hφ0 : ∀ x, x ∉ tsupport f → φ x = 0 := by
    intro x hx
    simp [φ, image_eq_zero_of_notMem_tsupport hx]
  have hφint : Integrable φ := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact HasCompactSupport.intro f.hasCompactSupport hφ0
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport f ⊆ Set.Icc (-R) R := by
    obtain ⟨R, hR⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
    refine ⟨R, fun y hy => ?_⟩
    have := hR hy
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp this
  have hev : ∀ᶠ M : ℕ in atTop,
      ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(cueLaw M : Measure (VaguePointMeasure ℝ)) =
        fredholmSeries (cueKernel M) volume φ := by
    filter_upwards [eventually_gt_atTop ⌈R⌉₊] with M hM
    rw [integral_exp_neg_cueLaw, cueMeasure]
    refine fredholmSeries_restrict (cueKernel M) fun x hx => hφ0 x fun hxs => hx ?_
    have hy := hR hxs
    have hRM : R < M := by
      have := Nat.le_ceil R
      have : (⌈R⌉₊ : ℝ) < M := by exact_mod_cast hM
      linarith
    refine ⟨?_, ?_⟩ <;> linarith [hy.1, hy.2]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  rw [sineLaplaceFunctional_eq_fredholmSeries]
  exact tendsto_fredholmSeries (fun M => measurable_cueKernel M)
    (fun M k y => abs_det_cueKernel_le_one M k y) (fun x y => tendsto_cueKernel x y) hφint

/-- Expected counts of the approximants: `E ξ(g) = ∫_{window} g ≤ ∫ g`. -/
theorem lintegral_coordinate_cueLaw_le (M : ℕ) (g : CompactlySupportedContinuousMap ℝ ℝ)
    (hg : ∀ x, 0 ≤ g x) :
    ∫⁻ ξ, ENNReal.ofReal (∫ x, g x ∂ξ.measure) ∂(cueLaw M : Measure (VaguePointMeasure ℝ)) ≤
      ∫⁻ y, ENNReal.ofReal (g y) := by
  rw [lintegral_coordinate_eq_of_fredholm (cueLaw M) (abs_det_cueKernel_le_one M)
    (cueKernel_self M) (cueMeasure M) (fun f _ => integral_exp_neg_cueLaw M f) g hg,
    ofReal_integral_eq_lintegral_ofReal]
  · exact setLIntegral_le_lintegral _ _
  · exact (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).integrableOn
  · exact Filter.Eventually.of_forall hg

/-- Existence of a law satisfying `IsSineLaw`. -/
theorem exists_isSineLaw :
    ∃ P : ProbabilityMeasure (VaguePointMeasure ℝ), IsSineLaw P := by
  obtain ⟨Q, hQ⟩ := exists_law_of_tendsto_laplace cueLaw
    (fun g hg => ⟨∫⁻ y, ENNReal.ofReal (g y),
      (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).lintegral_lt_top.ne,
      fun M => lintegral_coordinate_cueLaw_le M g hg⟩)
    sineLaplaceFunctional (fun f _ => tendsto_integral_exp_neg_cueLaw f)
  exact ⟨Q, ae_isSimple_of_sineLaplace Q abs_det_sineKernel_le_one hQ, hQ⟩

/-- Intensity-one sine law: existence and uniqueness on `VaguePointMeasure ℝ` with its vague
Borel σ-algebra. There is exactly one probability law that is a.s. simple and whose Laplace
functional at every nonnegative `f ∈ C_c(ℝ)` is the sine-kernel Fredholm expansion. This is the
clause `∃! sineLaw, IsSineLaw sineLaw` of `HasCriticalEndpoints`; it uses no external input. -/
theorem existsUnique_isSineLaw :
    ∃! P : ProbabilityMeasure (VaguePointMeasure ℝ), IsSineLaw P := by
  obtain ⟨P, hP⟩ := exists_isSineLaw
  exact ⟨P, hP, fun Q hQ => isSineLaw_unique hQ hP⟩

end BlockBand.Endpoints
