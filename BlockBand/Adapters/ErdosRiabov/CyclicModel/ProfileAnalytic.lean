module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ProfileAdmissibility
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ERAdmissibilityComplete
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib

/-!
# Scalar Fourier estimates for the cyclic Erdős–Riabov profile

The Fourier symbol of the nearest-neighbour cyclic block covariance is `1 - 2b(1 - cos θ)`
(`cyclicSymbol`). For `b ≥ 0` it lies in `[1 - 4b, 1]`, and on `|θ| ≤ π` its gap satisfies
`1 - cyclicSymbol b θ ≥ (4b/π²)θ²`. The constants depend only on the coupling, not on the ring size
or its parity. These are the scalar estimates used in Example 2.7 of Erdős–Riabov.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERProfileAnalytic

open scoped BigOperators
open ERProfile

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Real Fourier symbol of the nearest-neighbour cyclic block covariance. -/
def cyclicSymbol (b θ : ℝ) : ℝ := 1 - 2 * b * (1 - Real.cos θ)

/-- Exact Fourier gap.  This is the scalar content behind the spectral-gap
coefficient and makes its dependence on the fixed coupling explicit. -/
theorem one_sub_cyclicSymbol (b θ : ℝ) :
    1 - cyclicSymbol b θ = 2 * b * (1 - Real.cos θ) := by
  unfold cyclicSymbol
  ring

/-- Quantitative principal-interval Fourier gap, uniform in ring length and parity.
The constant is exactly `4b/π²`. -/
theorem cyclicSymbol_quadratic_gap {b θ : ℝ} (hb : 0 ≤ b)
    (hθ : |θ| ≤ Real.pi) :
    (4 * b / Real.pi ^ 2) * θ ^ 2 ≤ 1 - cyclicSymbol b θ := by
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθ
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  rw [one_sub_cyclicSymbol]
  calc
    (4 * b / Real.pi ^ 2) * θ ^ 2 =
        2 * b * ((2 / Real.pi ^ 2) * θ ^ 2) := by ring
    _ ≤ 2 * b * (1 - Real.cos θ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith

/-- The scalar symbol never exceeds one for nonnegative coupling. -/
theorem cyclicSymbol_le_one {b θ : ℝ} (hb : 0 ≤ b) :
    cyclicSymbol b θ ≤ 1 := by
  rw [cyclicSymbol]
  nlinarith [Real.cos_le_one θ]

/-- For the paper's range `b<1/2`, the symbol is bounded below by `1-4b>-1`. -/
theorem one_sub_four_b_le_cyclicSymbol {b θ : ℝ} (hb : 0 ≤ b) :
    1 - 4 * b ≤ cyclicSymbol b θ := by
  rw [cyclicSymbol]
  have hcos := (Real.abs_cos_le_one θ)
  rw [abs_le] at hcos
  nlinarith

/-- Uniform spectral enclosure `|Ĉ(θ)|≤1` at every admissible coupling. -/
theorem abs_cyclicSymbol_le_one (p : Params) (θ : ℝ) :
    |cyclicSymbol p.b θ| ≤ 1 := by
  rw [abs_le]
  constructor
  · have hlo := one_sub_four_b_le_cyclicSymbol (b := p.b) (θ := θ) p.b_pos.le
    linarith [p.b_lt_half]
  · exact cyclicSymbol_le_one p.b_pos.le

end ERProfileAnalytic
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
