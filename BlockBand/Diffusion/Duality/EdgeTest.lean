module
public import BlockBand.Diffusion.Duality.Lyapunov
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Edge tests `εψ(ℓ/ε)` for the null-boundary-time argument

`edgePsi s = s β(s)` with `β` a smooth bump equal to `1` on `[-1, 1]` and supported in
`(-2, 2)`: `ψ = edgePsi` is smooth, `ψ'(0) = 1`, `ψ'` and `ψ''` vanish for `|s| > 2`, and
`ψ`, `ψ'`, `s ↦ s ψ''(s)` are bounded.

For an edge of the closed strip given by an affine coordinate `ℓ(y) = α y_i + β₀`
(`x = 0`: `i = 0, ℓ = y₀`; `y = 0`: `i = 1, ℓ = y₁`; `y = 1`: `i = 1, ℓ = 1 − y₁`) the test
`edgeFun ε (y) = ε ψ(ℓ(y)/ε)` has `|edgeFun| ≤ ε sup |ψ|`, and on the closed strip its
`𝒟₀`-generator is bounded uniformly in `ε ∈ (0, 1]` and converges, as `ε → 0`, to
`(D₀/2) 1{ℓ(y) = 0}`.
-/

namespace BlockBand.Diffusion
open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic

/-- The bump `β`: `1` on `[-1, 1]`, support `(-2, 2)`. -/
def edgeBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- `ψ(s) = s β(s)`. -/
def edgePsi (s : ℝ) : ℝ := s * edgeBump s

theorem contDiff_edgePsi : ContDiff ℝ (⊤ : ℕ∞) edgePsi :=
  contDiff_id.mul edgeBump.contDiff

theorem edgeBump_eq_zero {s : ℝ} (hs : 2 ≤ |s|) : edgeBump s = 0 := by
  have : s ∉ Function.support edgeBump := by
    rw [edgeBump.support_eq]
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact hs
  exact Function.notMem_support.1 this

theorem edgePsi_eventually_zero {s : ℝ} (hs : 2 < |s|) : edgePsi =ᶠ[𝓝 s] fun _ => 0 := by
  have : ∀ᶠ x in 𝓝 s, 2 < |x| := (continuous_abs.tendsto s).eventually (Ioi_mem_nhds hs)
  filter_upwards [this] with x hx
  simp [edgePsi, edgeBump_eq_zero hx.le]

theorem deriv_edgePsi_eq_zero {s : ℝ} (hs : 2 < |s|) : deriv edgePsi s = 0 := by
  rw [(edgePsi_eventually_zero hs).deriv_eq]; simp

theorem deriv2_edgePsi_eq_zero {s : ℝ} (hs : 2 < |s|) : deriv (deriv edgePsi) s = 0 := by
  have : deriv edgePsi =ᶠ[𝓝 s] fun _ => 0 := by
    have h2 : ∀ᶠ x in 𝓝 s, 2 < |x| := (continuous_abs.tendsto s).eventually (Ioi_mem_nhds hs)
    filter_upwards [h2] with x hx using deriv_edgePsi_eq_zero hx
  rw [this.deriv_eq]; simp

theorem deriv_edgePsi_zero : deriv edgePsi 0 = 1 := by
  have : edgePsi =ᶠ[𝓝 0] fun s => s := by
    have h1 : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 1 := by
      have := (continuous_abs.tendsto (0 : ℝ)).eventually (Iio_mem_nhds (show |(0 : ℝ)| < 1 by
        simp))
      exact this
    filter_upwards [h1] with x hx
    have : edgeBump x = 1 := edgeBump.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      exact hx.le.trans (by norm_num [edgeBump]))
    simp [edgePsi, this]
  rw [this.deriv_eq]; simp

theorem continuous_deriv_edgePsi : Continuous (deriv edgePsi) :=
  contDiff_edgePsi.continuous_deriv (by simp)

theorem continuous_deriv2_edgePsi : Continuous (deriv (deriv edgePsi)) :=
  ((contDiff_edgePsi.of_le (by simp) : ContDiff ℝ 2 edgePsi).iterate_deriv' 1 1).continuous_deriv
    (by simp)

/-- A function continuous on `ℝ` and vanishing for `|s| > 2` is bounded. -/
theorem exists_bound_of_vanish {h : ℝ → ℝ} (hc : Continuous h) (hz : ∀ s, 2 < |s| → h s = 0) :
    ∃ C, 0 ≤ C ∧ ∀ s, |h s| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s => ?_⟩
  by_cases hs : 2 < |s|
  · rw [hz s hs, abs_zero]; exact le_max_right _ _
  · push Not at hs
    exact (Real.norm_eq_abs _ ▸ hC s (abs_le.1 hs)).trans (le_max_left _ _)

theorem exists_bound_edgePsi : ∃ C, 0 ≤ C ∧ ∀ s, |edgePsi s| ≤ C :=
  exists_bound_of_vanish contDiff_edgePsi.continuous fun _ hs =>
    (edgePsi_eventually_zero hs).self_of_nhds

theorem exists_bound_deriv_edgePsi : ∃ C, 0 ≤ C ∧ ∀ s, |deriv edgePsi s| ≤ C :=
  exists_bound_of_vanish continuous_deriv_edgePsi fun _ hs => deriv_edgePsi_eq_zero hs

theorem exists_bound_mul_deriv2_edgePsi :
    ∃ C, 0 ≤ C ∧ ∀ s, |s * deriv (deriv edgePsi) s| ≤ C :=
  exists_bound_of_vanish (continuous_id.mul continuous_deriv2_edgePsi) fun _ hs => by
    rw [deriv2_edgePsi_eq_zero hs, mul_zero]

/-!
### One-dimensional chain rule
-/

theorem hasDerivAt_edge (ε α β₀ : ℝ) (hε : ε ≠ 0) (t : ℝ) :
    HasDerivAt (fun t => ε * edgePsi ((α * t + β₀) / ε))
      (α * deriv edgePsi ((α * t + β₀) / ε)) t := by
  have h1 : HasDerivAt (fun t => (α * t + β₀) / ε) (α / ε) t :=
    (((hasDerivAt_id t).const_mul α).add_const β₀).div_const ε |>.congr_deriv (by simp)
  have h2 := ((contDiff_edgePsi.differentiable (by simp)) ((α * t + β₀) / ε)).hasDerivAt
  refine ((h2.comp t h1).const_mul ε).congr_deriv ?_
  rw [show ε * (deriv edgePsi ((α * t + β₀) / ε) * (α / ε)) =
    α * deriv edgePsi ((α * t + β₀) / ε) * (ε / ε) by ring, div_self hε, mul_one]

theorem hasDerivAt_edge' (ε α β₀ : ℝ) (t : ℝ) :
    HasDerivAt (fun t => α * deriv edgePsi ((α * t + β₀) / ε))
      (α ^ 2 * deriv (deriv edgePsi) ((α * t + β₀) / ε) / ε) t := by
  have h1 : HasDerivAt (fun t => (α * t + β₀) / ε) (α / ε) t :=
    (((hasDerivAt_id t).const_mul α).add_const β₀).div_const ε |>.congr_deriv (by simp)
  have h2 := ((((contDiff_edgePsi.of_le (by simp) : ContDiff ℝ 2 edgePsi).iterate_deriv' 1
    1).differentiable (by simp))
    ((α * t + β₀) / ε)).hasDerivAt
  refine ((h2.comp t h1).const_mul α).congr_deriv ?_
  simp only [Function.iterate_one]
  ring

/-!
### The edge tests and their generators
-/

/-- `x`-edge test `ε ψ(y₀/ε)`. -/
def edgeFunX (ε : ℝ) (y : Fin 2 → ℝ) : ℝ := ε * edgePsi ((1 * y 0 + 0) / ε) + 0

/-- `y = 0` edge test `ε ψ(y₁/ε)`. -/
def edgeFunY0 (ε : ℝ) (y : Fin 2 → ℝ) : ℝ := 0 + ε * edgePsi ((1 * y 1 + 0) / ε)

/-- `y = 1` edge test `ε ψ((1 − y₁)/ε)`. -/
def edgeFunY1 (ε : ℝ) (y : Fin 2 → ℝ) : ℝ := 0 + ε * edgePsi ((-1 * y 1 + 1) / ε)

theorem contDiff_edgeFunX (ε : ℝ) : ContDiff ℝ 2 (edgeFunX ε) := by
  unfold edgeFunX
  exact (contDiff_const.mul ((contDiff_edgePsi.of_le (by simp)).comp
    (((contDiff_const.mul (contDiff_apply ℝ ℝ 0)).add contDiff_const).div_const ε))).add
    contDiff_const

theorem contDiff_edgeFunY0 (ε : ℝ) : ContDiff ℝ 2 (edgeFunY0 ε) := by
  unfold edgeFunY0
  exact contDiff_const.add (contDiff_const.mul ((contDiff_edgePsi.of_le (by simp)).comp
    (((contDiff_const.mul (contDiff_apply ℝ ℝ 1)).add contDiff_const).div_const ε)))

theorem contDiff_edgeFunY1 (ε : ℝ) : ContDiff ℝ 2 (edgeFunY1 ε) := by
  unfold edgeFunY1
  exact contDiff_const.add (contDiff_const.mul ((contDiff_edgePsi.of_le (by simp)).comp
    (((contDiff_const.mul (contDiff_apply ℝ ℝ 1)).add contDiff_const).div_const ε)))

theorem mpGenerator_edgeFunX (D0 ε : ℝ) (hε : ε ≠ 0) (y : Fin 2 → ℝ) :
    mpGenerator (baseDrift D0) (baseCov D0) (edgeFunX ε) y =
      D0 / 2 * (1 + 2 * y 0) * deriv edgePsi (y 0 / ε) +
        1 / 2 * (D0 * (y 0 * (1 + y 0)) * (deriv (deriv edgePsi) (y 0 / ε) / ε)) := by
  have e := mpGenerator_sep (baseDrift D0) (baseCov D0) (y := y)
    (G := fun t => ε * edgePsi ((1 * t + 0) / ε)) (H := fun _ => 0)
    (G1 := fun t => 1 * deriv edgePsi ((1 * t + 0) / ε))
    (G2 := fun t => 1 ^ 2 * deriv (deriv edgePsi) ((1 * t + 0) / ε) / ε)
    (H1 := fun _ => 0) (H2 := fun _ => 0)
    (Eventually.of_forall fun t => hasDerivAt_edge ε 1 0 hε t) (hasDerivAt_edge' ε 1 0 _)
    (Eventually.of_forall fun t => hasDerivAt_const t 0) (hasDerivAt_const _ 0)
  have hf : edgeFunX ε = fun w => (fun t => ε * edgePsi ((1 * t + 0) / ε)) (w 0) +
      (fun _ => (0 : ℝ)) (w 1) := rfl
  rw [hf, e]
  simp [baseDrift, baseCov]

theorem mpGenerator_edgeFunY0 (D0 ε : ℝ) (hε : ε ≠ 0) (y : Fin 2 → ℝ) :
    mpGenerator (baseDrift D0) (baseCov D0) (edgeFunY0 ε) y =
      D0 / 2 * (1 - 2 * y 1) * deriv edgePsi (y 1 / ε) +
        1 / 2 * (D0 * (y 1 * (1 - y 1)) * (deriv (deriv edgePsi) (y 1 / ε) / ε)) := by
  have e := mpGenerator_sep (baseDrift D0) (baseCov D0) (y := y)
    (G := fun _ => 0) (H := fun t => ε * edgePsi ((1 * t + 0) / ε))
    (G1 := fun _ => 0) (G2 := fun _ => 0)
    (H1 := fun t => 1 * deriv edgePsi ((1 * t + 0) / ε))
    (H2 := fun t => 1 ^ 2 * deriv (deriv edgePsi) ((1 * t + 0) / ε) / ε)
    (Eventually.of_forall fun t => hasDerivAt_const t 0) (hasDerivAt_const _ 0)
    (Eventually.of_forall fun t => hasDerivAt_edge ε 1 0 hε t) (hasDerivAt_edge' ε 1 0 _)
  have hf : edgeFunY0 ε = fun w => (fun _ => (0 : ℝ)) (w 0) +
      (fun t => ε * edgePsi ((1 * t + 0) / ε)) (w 1) := rfl
  rw [hf, e]
  simp [baseDrift, baseCov]

theorem mpGenerator_edgeFunY1 (D0 ε : ℝ) (hε : ε ≠ 0) (y : Fin 2 → ℝ) :
    mpGenerator (baseDrift D0) (baseCov D0) (edgeFunY1 ε) y =
      -(D0 / 2 * (1 - 2 * y 1) * deriv edgePsi ((1 - y 1) / ε)) +
        1 / 2 * (D0 * (y 1 * (1 - y 1)) * (deriv (deriv edgePsi) ((1 - y 1) / ε) / ε)) := by
  have e := mpGenerator_sep (baseDrift D0) (baseCov D0) (y := y)
    (G := fun _ => 0) (H := fun t => ε * edgePsi ((-1 * t + 1) / ε))
    (G1 := fun _ => 0) (G2 := fun _ => 0)
    (H1 := fun t => -1 * deriv edgePsi ((-1 * t + 1) / ε))
    (H2 := fun t => (-1) ^ 2 * deriv (deriv edgePsi) ((-1 * t + 1) / ε) / ε)
    (Eventually.of_forall fun t => hasDerivAt_const t 0) (hasDerivAt_const _ 0)
    (Eventually.of_forall fun t => hasDerivAt_edge ε (-1) 1 hε t)
    (hasDerivAt_edge' ε (-1) 1 _)
  have hf : edgeFunY1 ε = fun w => (fun _ => (0 : ℝ)) (w 0) +
      (fun t => ε * edgePsi ((-1 * t + 1) / ε)) (w 1) := rfl
  rw [hf, e]
  simp only [baseDrift, baseCov]
  simp
  ring_nf

end BlockBand.Diffusion
