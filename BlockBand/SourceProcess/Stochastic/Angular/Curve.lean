module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Complex angular contract: trigonometric curves and the second-order chain rule

* `trigCurve v t = v₀ + (cos t - 1) v₁ + sin t v₂ + (cos t - 1)² v₃ + (cos t - 1) sin t v₄
  - sin² t v₅`, with derivative `trigCurveD` (`hasDerivAt_trigCurve`), `γ'(0) = v₂` and
  `γ''(0) = -v₁ - 2 v₅` (`hasDerivAt_trigCurveD`);
* `hasDerivAt_deriv_comp`: for `g` of class `C²` at `γ 0`,
  `(g ∘ γ)''(0) = D²g(γ 0)[γ'(0), γ'(0)] + Dg(γ 0)[γ''(0)]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open Filter Topology

/-- A trigonometric curve through `v₀` (the shape of `t ↦ R(t) D R(t)*`). -/
def trigCurve {E : Type*} [AddCommGroup E] [Module ℝ E] (v₀ v₁ v₂ v₃ v₄ v₅ : E) (t : ℝ) : E :=
  v₀ + (Real.cos t - 1) • v₁ + Real.sin t • v₂ + ((Real.cos t - 1) * (Real.cos t - 1)) • v₃ +
    ((Real.cos t - 1) * Real.sin t) • v₄ - (Real.sin t * Real.sin t) • v₅

/-- The velocity of `trigCurve`. -/
def trigCurveD {E : Type*} [AddCommGroup E] [Module ℝ E] (v₁ v₂ v₃ v₄ v₅ : E) (t : ℝ) : E :=
  (-Real.sin t) • v₁ + Real.cos t • v₂ + (2 * (Real.cos t - 1) * (-Real.sin t)) • v₃ +
    (-Real.sin t * Real.sin t + (Real.cos t - 1) * Real.cos t) • v₄ -
    (2 * Real.sin t * Real.cos t) • v₅

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v₀ v₁ v₂ v₃ v₄ v₅ : E)

theorem trigCurve_zero : trigCurve v₀ v₁ v₂ v₃ v₄ v₅ 0 = v₀ := by simp [trigCurve]

theorem trigCurveD_zero : trigCurveD v₁ v₂ v₃ v₄ v₅ 0 = v₂ := by simp [trigCurveD]

theorem hasDerivAt_trigCurve (t : ℝ) :
    HasDerivAt (trigCurve v₀ v₁ v₂ v₃ v₄ v₅) (trigCurveD v₁ v₂ v₃ v₄ v₅ t) t := by
  have hc := (Real.hasDerivAt_cos t).sub_const 1
  have hs := Real.hasDerivAt_sin t
  have h := (((((hasDerivAt_const t v₀).add (hc.smul_const v₁)).add (hs.smul_const v₂)).add
    ((hc.mul hc).smul_const v₃)).add ((hc.mul hs).smul_const v₄)).sub ((hs.mul hs).smul_const v₅)
  convert h using 1
  · funext t; simp only [trigCurve]; rfl
  · simp only [trigCurveD]
    module

theorem hasDerivAt_trigCurveD :
    HasDerivAt (trigCurveD v₁ v₂ v₃ v₄ v₅) (-v₁ - (2 : ℝ) • v₅) 0 := by
  have hc := Real.hasDerivAt_cos 0
  have hs := Real.hasDerivAt_sin 0
  have hc1 := hc.sub_const 1
  have h := ((((hs.neg.smul_const v₁).add (hc.smul_const v₂)).add
    ((((hc1.const_mul 2).mul hs.neg)).smul_const v₃)).add
    (((hs.neg.mul hs).add (hc1.mul hc)).smul_const v₄)).sub
    ((((hs.const_mul 2).mul hc)).smul_const v₅)
  convert h using 1
  · funext t; simp only [trigCurveD]; rfl
  · simp only [Pi.neg_apply, Real.sin_zero, Real.cos_zero]
    module

/-- **Second-order chain rule along a curve.** -/
theorem hasDerivAt_deriv_comp {g : E → ℝ} {γ γ' : ℝ → E} {γ'' : E}
    (hg : ContDiffAt ℝ 2 g (γ 0)) (h1 : ∀ t, HasDerivAt γ (γ' t) t) (h2 : HasDerivAt γ' γ'' 0) :
    HasDerivAt (deriv (g ∘ γ))
      (fderiv ℝ (fderiv ℝ g) (γ 0) (γ' 0) (γ' 0) + fderiv ℝ g (γ 0) γ'') 0 := by
  have hev : ∀ᶠ x in 𝓝 (γ 0), DifferentiableAt ℝ g x :=
    (hg.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), deriv (g ∘ γ) t = fderiv ℝ g (γ t) (γ' t) := by
    filter_upwards [(h1 0).continuousAt.eventually hev] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (h1 t)).deriv
  have hD : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) (γ 0)) (γ 0) :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h3 := (hD.comp_hasDerivAt (0 : ℝ) (h1 0)).clm_apply h2
  exact h3.congr_of_eventuallyEq hev'

end BlockBand.SourceProcess.Stochastic.ComplexAngular
