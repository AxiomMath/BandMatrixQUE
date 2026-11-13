module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Dyadic approximation of a horizon strictly from below

For `a ≥ 0`, the dyadic times `dyTime n (dyIdx n a) = (⌈2ⁿ a⌉₊ - 1) / 2ⁿ` are at most `a`,
strictly below `a` when `a > 0`, and converge to `a` as `n → ∞`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornStopped

open Filter Topology MeasureTheory
open scoped NNReal

/-- The dyadic index `⌈2ⁿ a⌉₊ - 1`. -/
def dyIdx (n : ℕ) (a : ℝ≥0) : ℕ := ⌈(2 : ℝ) ^ n * (a : ℝ)⌉₊ - 1

/-- The dyadic time `k / 2ⁿ`. -/
def dyTime (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

theorem measurable_dyIdx (n : ℕ) : Measurable (dyIdx n) :=
  (measurable_of_countable fun k : ℕ => k - 1).comp
    (Nat.measurable_ceil.comp (measurable_const.mul measurable_coe_nnreal_real))

theorem coe_dyTime (n k : ℕ) : (dyTime n k : ℝ) = k / 2 ^ n := by
  simp [dyTime]

theorem dyIdx_zero (n : ℕ) : dyIdx n 0 = 0 := by simp [dyIdx]

theorem dyTime_zero (n : ℕ) : dyTime n 0 = 0 := by simp [dyTime]

/-- `2ⁿ a - 1 ≤ dyIdx n a ≤ 2ⁿ a`, strictly below when `a > 0`. -/
theorem dyIdx_bounds (n : ℕ) (a : ℝ≥0) :
    (2 : ℝ) ^ n * a - 1 ≤ dyIdx n a ∧ (dyIdx n a : ℝ) ≤ 2 ^ n * a ∧
      (0 < a → (dyIdx n a : ℝ) < 2 ^ n * a) := by
  set y : ℝ := (2 : ℝ) ^ n * a with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 := Nat.le_ceil y
  have h2 := Nat.ceil_lt_add_one hy0
  rcases Nat.eq_zero_or_pos ⌈y⌉₊ with hk | hk
  · have hy00 : y = 0 := le_antisymm (by simpa [hk] using h1) hy0
    have hd : dyIdx n a = 0 := by simp [dyIdx, ← hy, hk]
    refine ⟨by simp [hd, hy00], by simp [hd, hy00], fun ha => ?_⟩
    exact absurd hy00 (by rw [hy]; positivity)
  · have hd : (dyIdx n a : ℝ) = ⌈y⌉₊ - 1 := by
      simp only [dyIdx, ← hy]; rw [Nat.cast_sub hk, Nat.cast_one]
    refine ⟨by rw [hd]; linarith, by rw [hd]; linarith, fun _ => by rw [hd]; linarith⟩

theorem dyTime_lt {n : ℕ} {a : ℝ≥0} (ha : 0 < a) : dyTime n (dyIdx n a) < a := by
  rw [← NNReal.coe_lt_coe, coe_dyTime, div_lt_iff₀ (by positivity), mul_comm]
  exact (dyIdx_bounds n a).2.2 ha

theorem dyTime_le (n : ℕ) (a : ℝ≥0) : dyTime n (dyIdx n a) ≤ a := by
  rw [← NNReal.coe_le_coe, coe_dyTime, div_le_iff₀ (by positivity), mul_comm]
  exact (dyIdx_bounds n a).2.1

theorem tendsto_dyTime (a : ℝ≥0) : Tendsto (fun n => dyTime n (dyIdx n a)) atTop (𝓝 a) := by
  rw [← NNReal.tendsto_coe]
  have hlow : Tendsto (fun n : ℕ => (a : ℝ) - (1 / 2 : ℝ) ^ n) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    fun n => NNReal.coe_le_coe.2 (dyTime_le n a)
  have h := (dyIdx_bounds n a).1
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  simp only [coe_dyTime, one_div, inv_pow]
  rw [le_div_iff₀ h2, sub_mul, inv_mul_cancel₀ h2.ne', mul_comm]
  exact h

end BlockBand.SourceProcess.BornStopped
