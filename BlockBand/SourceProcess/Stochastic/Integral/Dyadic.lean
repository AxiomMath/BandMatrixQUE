module
public import BlockBand.SourceProcess.Stochastic.Integral.Grid
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Dyadic upper approximation and an `L²` limit criterion

* `dyadicUp n y = ⌈y / 2^{-n}⌉ 2^{-n}`: a grid value in `2^{-n} ℕ` with
  `y ≤ dyadicUp n y < y + 2^{-n}`, `dyadicUp n y ≤ N 2^{-n} ↔ y ≤ N 2^{-n}`, monotone in `y`,
  and `dyadicUp n y → y`.
* `tendsto_toLp_of_integral_sq`: on any measure, `∫ (G_n − G)² → 0` gives `L²` convergence
  of the classes.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverCompletion

/-- The dyadic mesh `2^{-n}`. -/
def dyadicStep (n : ℕ) : ℝ≥0 := (2⁻¹ : ℝ≥0) ^ n

theorem dyadicStep_pos (n : ℕ) : 0 < dyadicStep n :=
  pow_pos (inv_pos.2 two_pos) n

/-- The dyadic upper approximation `⌈y 2^n⌉ 2^{-n}`. -/
def dyadicUp (n : ℕ) (y : ℝ≥0) : ℝ≥0 := (⌈y / dyadicStep n⌉₊ : ℝ≥0) * dyadicStep n

theorem le_dyadicUp (n : ℕ) (y : ℝ≥0) : y ≤ dyadicUp n y := by
  have h := Nat.le_ceil (y / dyadicStep n)
  calc y = y / dyadicStep n * dyadicStep n := (div_mul_cancel₀ y (dyadicStep_pos n).ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h (zero_le : (0 : ℝ≥0) ≤ dyadicStep n)

theorem dyadicUp_lt (n : ℕ) (y : ℝ≥0) : dyadicUp n y < y + dyadicStep n := by
  have h := Nat.ceil_lt_add_one (zero_le : (0 : ℝ≥0) ≤ y / dyadicStep n)
  calc dyadicUp n y < (y / dyadicStep n + 1) * dyadicStep n :=
        mul_lt_mul_of_pos_right h (dyadicStep_pos n)
    _ = y + dyadicStep n := by rw [add_mul, div_mul_cancel₀ y (dyadicStep_pos n).ne', one_mul]

theorem dyadicUp_le_iff (n N : ℕ) (y : ℝ≥0) :
    dyadicUp n y ≤ N * dyadicStep n ↔ y ≤ N * dyadicStep n := by
  rw [dyadicUp, mul_le_mul_iff_left₀ (dyadicStep_pos n), Nat.cast_le, Nat.ceil_le,
    div_le_iff₀ (dyadicStep_pos n)]

theorem dyadicUp_mono (n : ℕ) {y z : ℝ≥0} (hyz : y ≤ z) : dyadicUp n y ≤ dyadicUp n z := by
  have hc : ⌈y / dyadicStep n⌉₊ ≤ ⌈z / dyadicStep n⌉₊ :=
    Nat.ceil_mono (div_le_div_of_nonneg_right hyz (zero_le : (0 : ℝ≥0) ≤ dyadicStep n))
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (zero_le : (0 : ℝ≥0) ≤ dyadicStep n)

theorem tendsto_dyadicUp (y : ℝ≥0) : Tendsto (fun n => dyadicUp n y) atTop (𝓝 y) := by
  have hs : Tendsto (fun n => y + dyadicStep n) atTop (𝓝 y) := by
    simpa only [add_zero, dyadicStep] using tendsto_const_nhds.add
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ≥0))
        (by rw [inv_lt_one₀ two_pos]; exact one_lt_two))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (le_dyadicUp · y) (fun n => (dyadicUp_lt n y).le)

/-- `∫ (G_n − G)² → 0` implies convergence of the `L²` classes. -/
theorem tendsto_toLp_of_integral_sq {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {G : ℕ → α → ℝ} {G₀ : α → ℝ} (hG : ∀ n, MemLp (G n) 2 ν) (hG₀ : MemLp G₀ 2 ν)
    (h : Tendsto (fun n => ∫ x, (G n x - G₀ x) ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => (hG n).toLp (G n)) atTop (𝓝 (hG₀.toLp G₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (n : ℕ) : ‖(hG n).toLp (G n) - hG₀.toLp G₀‖ =
      Real.sqrt (∫ x, (G n x - G₀ x) ^ 2 ∂ν) := by
    rw [← MemLp.toLp_sub, ← Real.sqrt_sq (norm_nonneg _), norm_sq_toLp ((hG n).sub hG₀)]
    rfl
  simp_rw [he]
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  exact this

end BlockBand.SourceProcess.Stochastic.Integral
