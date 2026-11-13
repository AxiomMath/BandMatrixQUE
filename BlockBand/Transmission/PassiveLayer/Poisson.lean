module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Half-plane Poisson average at `i` for bounded holomorphic functions

Let `F : ℂ → E` be continuous on the closed upper half-plane, holomorphic on the open
upper half-plane and bounded there (`E` a complex Banach space). Then

* `poisson_upperHalfPlane`: `F(i) = (2π)⁻¹ ∫₀^{2π} F(t(θ)) dθ`, where
  `t(θ) = Re cayley(e^{iθ}) ∈ ℝ` and `cayley w = i(1+w)/(1-w)` (`t(θ) = -cot(θ/2)`);
* `enorm_le_lintegral_cayley`: `‖F(i)‖ ≤ ∫ ‖F(t)‖ dν`;
* `enorm_rpow_le_lintegral_cayley`: `‖F(i)‖^p ≤ ∫ ‖F(t)‖^p dν` for `p ≥ 1`.

Here `ν = cayleyLaw`, the probability law `(2π)⁻¹ dθ` on `(0, 2π]`. Its image under `t` is the
Cauchy law `dt/(π(1+t²))`. That identification is not needed: the only use is that `F` is
evaluated at real points.

The proof applies the mean value property (`DiffContOnCl.circleAverage`) to `F ∘ cayley` on
the disks of radius `r < 1`, then takes `r ↑ 1` by dominated convergence (bound `M`). No
subharmonicity and no limit of `F` at infinity is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

/-- The Cayley map `w ↦ i(1+w)/(1-w)` (unit disk → upper half-plane, `0 ↦ i`). -/
def cayley (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

theorem cayley_im (w : ℂ) : (cayley w).im = (1 - normSq w) / normSq (1 - w) := by
  rw [cayley, div_im]
  simp [normSq_apply]
  ring

theorem cayley_zero : cayley 0 = I := by simp [cayley]

theorem circleMap_one_ne_one {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) : circleMap 0 1 θ ≠ 1 := by
  intro h
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h2 : θ = n * (2 * π) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hp := Real.pi_pos
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hn
    nlinarith
  · subst hn; simp at h2; linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-- The closed upper half-plane. -/
def upperClosed : Set ℂ := {ζ | 0 ≤ ζ.im}
/-- The open upper half-plane. -/
def upperOpen : Set ℂ := {ζ | 0 < ζ.im}

theorem isOpen_upperOpen : IsOpen upperOpen := isOpen_lt continuous_const Complex.continuous_im

/-- The real boundary point `t(θ) = Re cayley(e^{iθ})`. -/
def realCayley (θ : ℝ) : ℝ := (cayley (circleMap 0 1 θ)).re

theorem one_sub_ne_zero_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  rw [this] at hw; simp at hw

theorem cayley_im_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayley w).im := by
  rw [cayley_im]
  have h1 : normSq w < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have h2 : 0 < normSq (1 - w) := normSq_pos.mpr (one_sub_ne_zero_of_norm_lt hw)
  exact div_pos (by linarith) h2

theorem cayley_circleMap_eq {θ : ℝ} : cayley (circleMap 0 1 θ) = (realCayley θ : ℂ) := by
  apply Complex.ext
  · simp [realCayley]
  · rw [cayley_im, normSq_eq_norm_sq, norm_circleMap_zero]; simp

theorem differentiableAt_cayley {w : ℂ} (hw : 1 - w ≠ 0) : DifferentiableAt ℂ cayley w := by
  show DifferentiableAt ℂ (fun w : ℂ => I * (1 + w) / (1 - w)) w
  exact ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
    ((differentiableAt_const _).sub differentiableAt_id) hw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem average_cayley_radius [CompleteSpace E] {F : ℂ → E} (hd : DifferentiableOn ℂ F upperOpen)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F (cayley (circleMap 0 r θ)) = F I := by
  have hdiff : DifferentiableOn ℂ (F ∘ cayley) (closure (ball (0 : ℂ) |r|)) := by
    rw [abs_of_pos hr0, closure_ball _ hr0.ne']
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    have hw1 : ‖w‖ < 1 := by linarith
    have hF : DifferentiableAt ℂ F (cayley w) :=
      (hd _ (cayley_im_pos hw1)).differentiableAt
        (isOpen_upperOpen.mem_nhds (cayley_im_pos hw1))
    exact (hF.comp w (differentiableAt_cayley (one_sub_ne_zero_of_norm_lt hw1))).differentiableWithinAt
  have := hdiff.diffContOnCl.circleAverage
  rw [Real.circleAverage_def] at this
  simpa [cayley_zero] using this

theorem continuous_cayley_circleMap {r : ℝ} (hr : |r| < 1) :
    Continuous fun θ : ℝ => cayley (circleMap 0 r θ) := by
  show Continuous fun θ : ℝ => I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ)
  refine (continuous_const.mul (continuous_const.add (continuous_circleMap 0 r))).div
    (continuous_const.sub (continuous_circleMap 0 r)) fun θ => ?_
  exact one_sub_ne_zero_of_norm_lt (by rw [norm_circleMap_zero]; exact hr)

/-- **Half-plane mean value (Poisson) identity at `i`.** -/
theorem poisson_upperHalfPlane [CompleteSpace E] {F : ℂ → E} {M : ℝ}
    (hc : ContinuousOn F upperClosed) (hd : DifferentiableOn ℂ F upperOpen)
    (hb : ∀ ζ ∈ upperClosed, ‖F ζ‖ ≤ M) :
    F I = (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F (realCayley θ) := by
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r ∧ r < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr using hr
  have hlim : Tendsto (fun r : ℝ => ∫ θ in (0 : ℝ)..2 * π, F (cayley (circleMap 0 r θ)))
      (𝓝[<] 1) (𝓝 (∫ θ in (0 : ℝ)..2 * π, F (cayley (circleMap 0 1 θ)))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [hev] with r hr
      have hr' : |r| < 1 := by rw [abs_of_pos hr.1]; exact hr.2
      exact (hc.comp_continuous (continuous_cayley_circleMap hr') fun θ =>
        (cayley_im_pos (by rw [norm_circleMap_zero]; exact hr')).le).aestronglyMeasurable
    · filter_upwards [hev] with r hr
      refine ae_of_all _ fun θ _ => hb _ (cayley_im_pos ?_).le
      rw [norm_circleMap_zero, abs_of_pos hr.1]; exact hr.2
    · have hne : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 2 * π := by
        rw [ae_iff]; simp
      filter_upwards [hne] with θ hθ hmem
      rw [uIoc_of_le (by positivity)] at hmem
      have hu : 1 - circleMap 0 1 θ ≠ 0 := sub_ne_zero.mpr
        (circleMap_one_ne_one hmem.1 (lt_of_le_of_ne hmem.2 hθ)).symm
      have hcont : ContinuousAt (fun r : ℝ => cayley (circleMap 0 r θ)) 1 := by
        show ContinuousAt (fun r : ℝ => I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ)) 1
        have hcm : Continuous fun r : ℝ => circleMap 0 r θ := by
          simp only [circleMap]; fun_prop
        exact (continuous_const.mul (continuous_const.add hcm)).continuousAt.div
          (continuous_const.sub hcm).continuousAt hu
      have hin : Tendsto (fun r : ℝ => cayley (circleMap 0 r θ)) (𝓝[<] 1)
          (𝓝[upperClosed] (cayley (circleMap 0 1 θ))) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [hev] with r hr
        exact (cayley_im_pos (by rw [norm_circleMap_zero, abs_of_pos hr.1]; exact hr.2)).le
      have hmem' : cayley (circleMap 0 1 θ) ∈ upperClosed := by
        show 0 ≤ (cayley (circleMap 0 1 θ)).im
        rw [cayley_circleMap_eq]; simp
      exact (hc _ hmem').tendsto.comp hin
  have hconst : Tendsto (fun r : ℝ => (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
      F (cayley (circleMap 0 r θ))) (𝓝[<] 1) (𝓝 (F I)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with r hr
    exact (average_cayley_radius hd hr.1 hr.2).symm
  rw [tendsto_nhds_unique hconst (hlim.const_smul _)]
  simp only [cayley_circleMap_eq]

theorem measurable_cayley : Measurable cayley := by
  show Measurable fun w : ℂ => I * (1 + w) / (1 - w)
  fun_prop

theorem measurable_realCayley : Measurable realCayley := by
  unfold realCayley
  exact Complex.measurable_re.comp (measurable_cayley.comp (continuous_circleMap 0 1).measurable)

/-- The boundary law of the Cayley average: `(2π)⁻¹ dθ` on `(0, 2π]`. -/
def cayleyLaw : Measure ℝ :=
  ENNReal.ofReal (2 * π)⁻¹ • (volume.restrict (Ioc (0 : ℝ) (2 * π)))

instance : IsProbabilityMeasure cayleyLaw := by
  constructor
  rw [cayleyLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  rw [sub_zero, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem enorm_le_lintegral_cayley [CompleteSpace E] {F : ℂ → E} {M : ℝ}
    (hc : ContinuousOn F upperClosed) (hd : DifferentiableOn ℂ F upperOpen)
    (hb : ∀ ζ ∈ upperClosed, ‖F ζ‖ ≤ M) :
    ‖F I‖ₑ ≤ ∫⁻ θ, ‖F (realCayley θ)‖ₑ ∂cayleyLaw := by
  rw [poisson_upperHalfPlane hc hd hb, enorm_smul,
    intervalIntegral.integral_of_le (by positivity), cayleyLaw, lintegral_smul_measure,
    Real.enorm_eq_ofReal (by positivity), smul_eq_mul]
  gcongr
  exact enorm_integral_le_lintegral_enorm _

theorem enorm_rpow_le_lintegral_cayley [CompleteSpace E] {F : ℂ → E} {M : ℝ}
    (hc : ContinuousOn F upperClosed) (hd : DifferentiableOn ℂ F upperOpen)
    (hb : ∀ ζ ∈ upperClosed, ‖F ζ‖ ≤ M) {p : ℝ} (hp : 1 ≤ p) :
    ‖F I‖ₑ ^ p ≤ ∫⁻ θ, ‖F (realCayley θ)‖ₑ ^ p ∂cayleyLaw := by
  have hp0 : 0 < p := by linarith
  have hcont : Continuous fun t : ℝ => F t :=
    hc.comp_continuous continuous_ofReal fun t => by simp [upperClosed]
  set g : ℝ → ENNReal := fun θ => ‖F (realCayley θ)‖ₑ
  have hg : AEStronglyMeasurable g cayleyLaw :=
    (hcont.enorm.measurable.comp measurable_realCayley).aestronglyMeasurable
  have hle := eLpNorm_le_eLpNorm_of_exponent_le (μ := cayleyLaw) (f := g)
    (show (1 : ENNReal) ≤ ENNReal.ofReal p by simpa using ENNReal.ofReal_le_ofReal hp)
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by simp; linarith) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le] at hle
  simp only [enorm_eq_self, g] at hle
  calc ‖F I‖ₑ ^ p ≤ (∫⁻ θ, ‖F (realCayley θ)‖ₑ ∂cayleyLaw) ^ p :=
        ENNReal.rpow_le_rpow (enorm_le_lintegral_cayley hc hd hb) hp0.le
    _ ≤ ((∫⁻ θ, ‖F (realCayley θ)‖ₑ ^ p ∂cayleyLaw) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow hle hp0.le
    _ = _ := by rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  all_goals exact hg

end BlockBand.Transmission.PassiveLayer
