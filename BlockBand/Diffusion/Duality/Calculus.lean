module
public import BlockBand.Diffusion.Duality.SpaceTime
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Time cutoffs for the space-time generator

* `stGen_congr`: `stGen` only depends on the germ of `u`.
* `stGen_mul_time`: for `χ ∈ C²(ℝ)` and `u` of class `C²` at `p`,
  `stGen b a (χ(s) u) p = χ'(s) u(p) + χ(s) stGen b a u p`.
* `IsTimeWindow χ c c₂`: `χ ∈ C²`, `0 ≤ χ ≤ 1`, monotone, `χ = 0` on `(-∞, c]`, `χ = 1` on
  `[c₂, ∞)`. Consequences: `χ' ≥ 0`, `χ' = 0` off `[c, c₂]`, `χ'` bounded, and
  `∫_{(0,t]} χ' = 1` for `0 ≤ c`, `c₂ ≤ t`. `isTimeWindow_smoothTransition` gives one for every
  `c < c₂` (Mathlib's `Real.smoothTransition`).
-/

namespace BlockBand.Diffusion
open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {d : ℕ}

theorem stGen_congr {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {u v : ℝ × (Fin d → ℝ) → ℝ} {p : ℝ × (Fin d → ℝ)} (h : u =ᶠ[𝓝 p] v) :
    stGen b a u p = stGen b a v p := by
  simp only [stGen, partialTime, partialSpace, partialSpace2, h.fderiv_eq, h.fderiv.fderiv_eq]

theorem stGen_zero (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (p : ℝ × (Fin d → ℝ)) : stGen b a (fun _ => 0) p = 0 := by
  simp [stGen, partialTime, partialSpace, partialSpace2]

/-- **Product with a time cutoff.** -/
theorem stGen_mul_time (b : (Fin d → ℝ) → Fin d → ℝ)
    (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ)
    {u : ℝ × (Fin d → ℝ) → ℝ} {p : ℝ × (Fin d → ℝ)} (hu : ContDiffAt ℝ 2 u p) :
    stGen b a (fun q => χ q.1 * u q) p = deriv χ p.1 * u p + χ p.1 * stGen b a u p := by
  have hχd : ∀ x, HasDerivAt χ (deriv χ x) x := fun x =>
    ((hχ.differentiable (by norm_num)) x).hasDerivAt
  have hχ1 : ContDiff ℝ 1 (deriv χ) := hχ.iterate_deriv' 1 1
  have hχ2 : ∀ x, HasDerivAt (deriv χ) (deriv (deriv χ) x) x := fun x =>
    ((hχ1.differentiable (by norm_num)) x).hasDerivAt
  have hT : ∀ q : ℝ × (Fin d → ℝ), HasFDerivAt (fun q : ℝ × (Fin d → ℝ) => χ q.1)
      (deriv χ q.1 • ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ)) q :=
    fun q => (hχd q.1).comp_hasFDerivAt q (hasFDerivAt_fst)
  have hud : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ u q :=
    (hu.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num)
  have hφ : ∀ q, DifferentiableAt ℝ u q →
      HasFDerivAt (fun q : ℝ × (Fin d → ℝ) => χ q.1 * u q) (χ q.1 • fderiv ℝ u q +
        u q • (deriv χ q.1 • ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ))) q := fun q hq =>
    (hT q).mul hq.hasFDerivAt
  have hfd : fderiv ℝ (fun q : ℝ × (Fin d → ℝ) => χ q.1 * u q) =ᶠ[𝓝 p] fun q =>
      χ q.1 • fderiv ℝ u q + u q • (deriv χ q.1 • ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ)) :=
    hud.mono fun q hq => (hφ q hq).fderiv
  have hDu : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) p) p :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hT2 : ∀ q : ℝ × (Fin d → ℝ), HasFDerivAt (fun q : ℝ × (Fin d → ℝ) => deriv χ q.1)
      (deriv (deriv χ) q.1 • ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ)) q :=
    fun q => (hχ2 q.1).comp_hasFDerivAt q (hasFDerivAt_fst)
  have hG := (hT2 p).smul_const (ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ))
  have hF := ((hT p).smul hDu).add ((hud.self_of_nhds.hasFDerivAt).smul hG)
  have h1 := hfd.self_of_nhds
  have h2 := hfd.fderiv_eq.trans hF.fderiv
  simp only [stGen, partialTime, partialSpace, partialSpace2, h1, h2]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
    mul_zero, zero_mul, add_zero, mul_one]
  simp only [mul_left_comm _ (χ p.1), ← Finset.mul_sum]
  ring

/-!
### Time windows
-/

/-- A `C²` monotone cutoff from `0` (on `(-∞, c]`) to `1` (on `[c₂, ∞)`). -/
structure IsTimeWindow (χ : ℝ → ℝ) (c c₂ : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 χ
  mono : Monotone χ
  nonneg : ∀ r, 0 ≤ χ r
  le_one : ∀ r, χ r ≤ 1
  zero : ∀ r ≤ c, χ r = 0
  one : ∀ r, c₂ ≤ r → χ r = 1

namespace IsTimeWindow

variable {χ : ℝ → ℝ} {c c₂ : ℝ}

theorem deriv_nonneg (h : IsTimeWindow χ c c₂) (r : ℝ) : 0 ≤ deriv χ r := h.mono.deriv_nonneg

theorem deriv_eq_zero_of_lt (h : IsTimeWindow χ c c₂) {r : ℝ} (hr : r < c) : deriv χ r = 0 := by
  have : χ =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hr] with x hx
    exact h.zero x (le_of_lt hx)
  rw [this.deriv_eq]; simp

theorem deriv_eq_zero_of_gt (h : IsTimeWindow χ c c₂) {r : ℝ} (hr : c₂ < r) : deriv χ r = 0 := by
  have : χ =ᶠ[𝓝 r] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact h.one x (le_of_lt hx)
  rw [this.deriv_eq]; simp

theorem deriv_eq_zero (h : IsTimeWindow χ c c₂) {r : ℝ} (hr : r ∉ Icc c c₂) : deriv χ r = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at hr
  rcases hr with hr | hr
  · exact h.deriv_eq_zero_of_lt hr
  · exact h.deriv_eq_zero_of_gt hr

theorem continuous_deriv (h : IsTimeWindow χ c c₂) : Continuous (deriv χ) :=
  h.contDiff.continuous_deriv (by norm_num)

theorem exists_bound (h : IsTimeWindow χ c c₂) : ∃ K, 0 ≤ K ∧ ∀ r, |deriv χ r| ≤ K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.continuous_deriv.continuousOn (s := Icc c c₂))
  refine ⟨max K 0, le_max_right _ _, fun r => ?_⟩
  by_cases hr : r ∈ Icc c c₂
  · exact (Real.norm_eq_abs _ ▸ hK r hr).trans (le_max_left _ _)
  · rw [h.deriv_eq_zero hr, abs_zero]; exact le_max_right _ _

/-- `∫_{(0,t]} χ' = 1` when the window lies in `[0, t]`. -/
theorem integral_deriv (h : IsTimeWindow χ c c₂) {t : ℝ} (h0 : 0 ≤ c) (ht : c₂ ≤ t) :
    ∫ r in Ioc (0 : ℝ) t, deriv χ r = 1 := by
  have hc2 : c ≤ c₂ := by
    by_contra hlt
    push Not at hlt
    have := h.zero c₂ hlt.le
    rw [h.one c₂ le_rfl] at this
    exact one_ne_zero this
  rw [← intervalIntegral.integral_of_le (h0.trans (hc2.trans ht)),
    intervalIntegral.integral_deriv_eq_sub (fun x _ =>
      (h.contDiff.differentiable (by norm_num)) x)
      (h.continuous_deriv.intervalIntegrable _ _), h.one t ht, h.zero 0 h0, sub_zero]

end IsTimeWindow

theorem isTimeWindow_smoothTransition {c c₂ : ℝ} (hc : c < c₂) :
    IsTimeWindow (fun r => Real.smoothTransition ((r - c) / (c₂ - c))) c c₂ := by
  have hpos : 0 < c₂ - c := sub_pos.2 hc
  refine ⟨?_, ?_, fun r => Real.smoothTransition.nonneg _, fun r => Real.smoothTransition.le_one _,
    fun r hr => ?_, fun r hr => ?_⟩
  · exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  · intro x y hxy
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hpos.le)
  · exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      hpos.le)
  · exact Real.smoothTransition.one_of_one_le ((one_le_div hpos).2 (by linarith))

end BlockBand.Diffusion
