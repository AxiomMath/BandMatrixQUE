module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.Convex.Basic

/-!
# Prékopa's theorem on log-concave marginals, as a hypothesis

This file states Theorem 6 of Prékopa (Acta Sci. Math. 34 (1973), 335–343) as the hypothesis
`SourceContract`: if `f ≥ 0` is log-concave on `ℝⁿ × ℝᵐ` and `A ⊆ ℝᵐ` is convex, then
`x ↦ ∫_A f(x, y) dy` is log-concave on `ℝⁿ`. The marginal is a Lebesgue integral with values in
`[0, ∞]` (it may be infinite), with respect to the completed Lebesgue measure; no integrability or
normalization of `f` is assumed, and `n, m` may be zero.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.External.Prekopa

open MeasureTheory
open scoped NNReal ENNReal

/-- Log-concavity of `f : E → [0, ∞]`: `f(x)^a f(y)^{1-a} ≤ f(ax + (1-a)y)` for all `x, y` and
`0 < a < 1`. -/
def LogConcave {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ≥0∞) : Prop :=
  ∀ x y : E, ∀ a : ℝ, 0 < a → a < 1 →
    f x ^ a * f y ^ (1-a) ≤ f (a • x + (1-a) • y)

/-- A finite nonnegative function on `ℝⁿ × ℝᵐ` is log-concave. -/
def JointLogConcave (n m : ℕ)
    (f : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ≥0) : Prop :=
  LogConcave (fun z => (f z : ℝ≥0∞))

/-- The marginal `x ↦ ∫_A f(x, y) dy ∈ [0, ∞]`, a lower Lebesgue integral with respect to the
completed Lebesgue measure on `ℝᵐ` (so that every convex `A` is measurable). -/
def marginal {n m : ℕ}
    (f : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ≥0)
    (A : Set (Fin m → ℝ)) (x : Fin n → ℝ) : ℝ≥0∞ := by
  classical
  exact ∫⁻ y : NullMeasurableSpace (Fin m → ℝ) (volume : Measure (Fin m → ℝ)),
    if y ∈ A then (f (x,y) : ℝ≥0∞) else 0
      ∂(volume : Measure (Fin m → ℝ)).completion

/-- Prékopa's Theorem 6: marginals of log-concave functions over convex sets are log-concave. -/
structure SourceContract : Prop where
  theorem6 : ∀ (n m : ℕ)
    (f : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ≥0)
    (A : Set (Fin m → ℝ)),
    JointLogConcave n m f → Convex ℝ A → LogConcave (marginal f A)

/-- The marginal of a log-concave `f` over a convex `A` is log-concave, given `SourceContract`. -/
theorem logConcave_marginal (source : SourceContract) {n m : ℕ}
    (f : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ≥0)
    (A : Set (Fin m → ℝ)) (hf : JointLogConcave n m f) (hA : Convex ℝ A) :
    LogConcave (marginal f A) :=
  source.theorem6 n m f A hf hA

end BlockBand.External.Prekopa
