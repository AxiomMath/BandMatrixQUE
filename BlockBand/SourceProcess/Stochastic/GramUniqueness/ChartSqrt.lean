module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Lipschitz
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A Lipschitz square root away from a spectral gap

`cutSqrt δ x = min (√(max x δ)) ((2/√δ) · max (x - δ/2) 0)` (`δ > 0`): globally Lipschitz
(`lipschitzWith_cutSqrt`, constant `2/√δ`), `0` for `x ≤ δ/2`, `√x` for `x ≥ δ`; hence
`cutSqrt δ x ^ 2 = x` for `x ∈ {0} ∪ [δ, ∞)` (`cutSqrt_mul_self`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open scoped NNReal

/-- The square root cut off below the gap `(0, δ)`. -/
def cutSqrt (δ x : ℝ) : ℝ := min (Real.sqrt (max x δ)) ((2 / Real.sqrt δ) * max (x - δ / 2) 0)

theorem cutSqrt_of_le {δ x : ℝ} (hx : x ≤ δ / 2) : cutSqrt δ x = 0 := by
  have : max (x - δ / 2) 0 = 0 := max_eq_right (by linarith)
  rw [cutSqrt, this, mul_zero]
  exact min_eq_right (Real.sqrt_nonneg _)

theorem cutSqrt_of_ge {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) : cutSqrt δ x = Real.sqrt x := by
  have h1 : max x δ = x := max_eq_left hx
  have h2 : max (x - δ / 2) 0 = x - δ / 2 := max_eq_left (by linarith)
  rw [cutSqrt, h1, h2]
  refine min_eq_left ?_
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsx : Real.sqrt δ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ hs]
  nlinarith [Real.sqrt_nonneg x]

theorem cutSqrt_mul_self {δ x : ℝ} (hδ : 0 < δ) (hx : x = 0 ∨ δ ≤ x) :
    cutSqrt δ x * cutSqrt δ x = x := by
  rcases hx with h | h
  · rw [h, cutSqrt_of_le (by linarith), mul_zero]
  · rw [cutSqrt_of_ge hδ h, Real.mul_self_sqrt (by linarith)]

theorem cutSqrt_zero (δ : ℝ) (hδ : 0 ≤ δ) : cutSqrt δ 0 = 0 := cutSqrt_of_le (by linarith)

theorem lipschitzWith_sqrt_max {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal (2 / Real.sqrt δ)) fun x => Real.sqrt (max x δ) := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  set a := max x δ
  set b := max y δ
  have ha : δ ≤ a := le_max_right _ _
  have hb : δ ≤ b := le_max_right _ _
  have hsa : Real.sqrt δ ≤ Real.sqrt a := Real.sqrt_le_sqrt ha
  have hsb : Real.sqrt δ ≤ Real.sqrt b := Real.sqrt_le_sqrt hb
  have hab : |a - b| ≤ |x - y| := abs_max_sub_max_le_abs x y δ
  have key : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a - b| := by
    rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt a + Real.sqrt b), ← abs_mul]
    congr 1
    nlinarith [Real.mul_self_sqrt (show 0 ≤ a by linarith),
      Real.mul_self_sqrt (show 0 ≤ b by linarith)]
  have h2 : |Real.sqrt a - Real.sqrt b| * Real.sqrt δ ≤ |a - b| := by
    rw [← key]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hs]
  nlinarith [abs_nonneg (Real.sqrt a - Real.sqrt b), abs_nonneg (x - y)]

theorem lipschitzWith_ramp {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal (2 / Real.sqrt δ))
      fun x => (2 / Real.sqrt δ) * max (x - δ / 2) 0 := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity), ← mul_sub, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.sqrt δ)]
  have h := abs_max_sub_max_le_abs (x - δ / 2) (y - δ / 2) 0
  rw [show x - δ / 2 - (y - δ / 2) = x - y by ring] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **`cutSqrt δ` is globally Lipschitz.** -/
theorem lipschitzWith_cutSqrt {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal (2 / Real.sqrt δ)) (cutSqrt δ) := by
  have h := (lipschitzWith_sqrt_max hδ).min (lipschitzWith_ramp hδ)
  rw [max_self] at h
  exact h

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
