module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The base diffusion: definitions

The base diffusion on the strip `[0, ∞) × [0, 1]` (`exBaseStrip`) with generator
`𝒟₀ f = (D₀/2)[x(1+x) f_xx + (1+2x) f_x + y(1−y) f_yy + (1−2y) f_y]` (`exBaseGenerator`).
`IsExBaseDiffusion` says that a continuous adapted process started at `z` stays in the strip and
solves the martingale problem for `𝒟₀` on smooth compactly supported tests; `HasExBaseDiffusion`
asserts that such a process exists on some filtered probability space.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-- The closed strip `[0, ∞) × [0, 1]` (state space of the base diffusion). -/
def exBaseStrip : Set (ℝ × ℝ) := Ici 0 ×ˢ Icc 0 1

/-- The independent Legendre–Jacobi base generator:
`𝒟₀ f = (D₀/2)[x(1+x)f_xx + (1+2x)f_x + y(1-y)f_yy + (1-2y)f_y]`
`= (D₀/2){∂_x[x(1+x)∂_x f] + ∂_y[y(1-y)∂_y f]}`.
-/
def exBaseGenerator (D0 : ℝ) (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  D0 / 2 *
    ((z.1 * (1 + z.1) * fderiv ℝ (fun w => fderiv ℝ f w (1, 0)) z (1, 0) +
        (1 + 2 * z.1) * fderiv ℝ f z (1, 0)) +
      (z.2 * (1 - z.2) * fderiv ℝ (fun w => fderiv ℝ f w (0, 1)) z (0, 1) +
        (1 - 2 * z.2) * fderiv ℝ f z (0, 1)))

/-- **The base diffusion started at `z`**: an adapted process with continuous paths in the closed
strip, `Z₀ = z`, solving the martingale problem of `𝒟₀` for every smooth compactly supported test
`f` on `ℝ²`:
`f(Z_t) - ∫_0^t 𝒟₀ f(Z_u) du` is a `𝓖`-martingale.
-/
structure IsExBaseDiffusion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ) (z : ℝ × ℝ)
    (Z : ℝ≥0 → Ω → ℝ × ℝ) : Prop where
  prob : IsProbabilityMeasure P
  adapted : ∀ t, Measurable[𝓖 t] (Z t)
  start : ∀ᵐ ω ∂P, Z 0 ω = z
  paths : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω) ∧ ∀ t, Z t ω ∈ exBaseStrip
  martingale : ∀ f : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
    Martingale (fun t ω => f (Z t ω) - ∫ u in Ioc (0 : ℝ) t, exBaseGenerator D0 f (Z u.toNNReal ω))
      𝓖 P

/-- The base diffusion from `z` exists (on some filtered probability space). -/
def HasExBaseDiffusion (D0 : ℝ) (z : ℝ × ℝ) : Prop :=
  ∃ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ × ℝ), IsExBaseDiffusion P 𝓖 D0 z Z

end BlockBand.Diffusion
