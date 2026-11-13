module

public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.ScalarPrekopaTruncation
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Spatial truncation for the scalar Prékopa–Leindler inequality

Restriction of an `ℝ≥0∞`-valued function on the real line to the expanding compact windows
`[-n, n]`. The restrictions are bounded by the function, preserve measurability and increase
with `n`, and every real point lies in all sufficiently large windows.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PrekopaNative.BlockBand

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- The compact real window of natural radius `n`. -/
def realCompactWindow (n : ℕ) : Set ℝ :=
  Set.Icc (-(n : ℝ)) (n : ℝ)

/-- Each natural-radius window is Lebesgue measurable. -/
theorem measurableSet_realCompactWindow (n : ℕ) :
    MeasurableSet (realCompactWindow n) := by
  exact measurableSet_Icc

/-- Natural-radius windows expand monotonically. -/
theorem monotone_realCompactWindow : Monotone realCompactWindow := by
  intro n m hnm x hx
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  constructor <;> dsimp [realCompactWindow] at hx ⊢ <;> linarith [hx.1, hx.2]

/-- Spatial restriction of an `ENNReal`-valued function to `[-n,n]`. -/
def ennrealSpatialTruncation (f : ℝ → ℝ≥0∞) (n : ℕ) : ℝ → ℝ≥0∞ :=
  (realCompactWindow n).indicator f

/-- Spatial restriction never exceeds the original nonnegative function. -/
theorem ennrealSpatialTruncation_le (f : ℝ → ℝ≥0∞) (n : ℕ) :
    ennrealSpatialTruncation f n ≤ f := by
  intro x
  by_cases hx : x ∈ realCompactWindow n
  · simp [ennrealSpatialTruncation, hx]
  · simp [ennrealSpatialTruncation, hx]

/-- Measurability is preserved by restriction to a compact window. -/
theorem measurable_ennrealSpatialTruncation {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) (n : ℕ) :
    Measurable (ennrealSpatialTruncation f n) := by
  exact hf.indicator (measurableSet_realCompactWindow n)

/-- Spatial truncations increase as their compact windows expand. -/
theorem monotone_ennrealSpatialTruncation (f : ℝ → ℝ≥0∞) :
    Monotone (ennrealSpatialTruncation f) := by
  intro n m hnm x
  by_cases hx : x ∈ realCompactWindow n
  · have hxm : x ∈ realCompactWindow m := monotone_realCompactWindow hnm hx
    simp [ennrealSpatialTruncation, hx, hxm]
  · simp [ennrealSpatialTruncation, hx]

/-- Every real point eventually belongs to all sufficiently large natural
compact windows. -/
theorem eventually_mem_realCompactWindow (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, x ∈ realCompactWindow n := by
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  filter_upwards [eventually_ge_atTop n] with m hm
  have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  change (-(m : ℝ) ≤ x ∧ x ≤ (m : ℝ))
  constructor <;> linarith [neg_abs_le x, le_abs_self x]

end PrekopaNative.BlockBand
