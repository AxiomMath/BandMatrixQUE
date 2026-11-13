module

public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.ScalarPrekopaLeindlerProof
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Value truncation for the scalar Prékopa–Leindler inequality

Truncation `min f n` of an `ℝ≥0∞`-valued function at natural heights `n`. The truncations are
bounded by `f`, preserve measurability, and converge pointwise to `f`, also where `f` is `∞`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PrekopaNative.BlockBand

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- Natural-height value truncation of an `ENNReal`-valued function. -/
def ennrealValueTruncation {α : Type*} (f : α → ℝ≥0∞) (n : ℕ) (x : α) : ℝ≥0∞ :=
  min (f x) (n : ℝ≥0∞)

/-- Value truncation never exceeds the original function. -/
theorem ennrealValueTruncation_le {α : Type*} (f : α → ℝ≥0∞) (n : ℕ) :
    ennrealValueTruncation f n ≤ f := by
  intro x
  exact min_le_left _ _

/-- Measurability is preserved by natural-height value truncation. -/
theorem measurable_ennrealValueTruncation {α : Type*} [MeasurableSpace α]
    {f : α → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    Measurable (ennrealValueTruncation f n) := by
  exact hf.min measurable_const

/-- Natural-height truncations converge pointwise to the original extended
nonnegative value, including when that value is `∞`. -/
theorem tendsto_ennrealValueTruncation (u : ℝ≥0∞) :
    Tendsto (fun n : ℕ => min u (n : ℝ≥0∞)) atTop (𝓝 u) := by
  simpa [min_comm] using
    (ENNReal.tendsto_nat_nhds_top.min tendsto_const_nhds :
      Tendsto (fun n : ℕ => min (n : ℝ≥0∞) u) atTop (𝓝 (min ∞ u)))

end PrekopaNative.BlockBand
