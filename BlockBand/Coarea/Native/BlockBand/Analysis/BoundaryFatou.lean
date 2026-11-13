module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Fatou passage to resolvent boundary values

This file isolates the measure-theoretic last step in the projected Wegner
argument.  Positive-height resolvent traces are nonnegative.  If they converge
almost everywhere as the regulator tends to zero and their expectations have
a uniform bound, Fatou's lemma transfers exactly the same bound to the boundary
value.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Filter MeasureTheory
open scoped ENNReal Topology

/-- Fatou boundary-value principle used in the projected Wegner lemma.

The sequence is `ℝ≥0∞`-valued so nonnegativity is built into the type.  The
hypotheses record only almost-everywhere measurability, almost-everywhere
convergence along `atTop`, and the same finite-height bound `C` for every
regulator.  No domination or integrability of the boundary value is assumed. -/
theorem lintegral_boundary_le_of_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hfg : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hC : ∀ n, ∫⁻ ω, f n ω ∂μ ≤ C) :
    ∫⁻ ω, g ω ∂μ ≤ C := by
  calc
    ∫⁻ ω, g ω ∂μ =
        ∫⁻ ω, liminf (fun n => f n ω) atTop ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hfg] with ω hω
          exact hω.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂μ) atTop :=
      lintegral_liminf_le' hf
    _ ≤ C := by
      refine Filter.liminf_le_of_le
        (Filter.isBoundedUnder_of_eventually_ge
          (Filter.Eventually.of_forall fun _ => bot_le)) ?_
      intro b hb
      have hboth : ∀ᶠ n in atTop,
          b ≤ ∫⁻ ω, f n ω ∂μ ∧ ∫⁻ ω, f n ω ∂μ ≤ C :=
        hb.and (Filter.Eventually.of_forall hC)
      rcases hboth.exists with ⟨n, hn⟩
      exact hn.1.trans hn.2

end CoareaNative.BlockBand
