module

public import BlockBand.Transmission.Generator.DriftOneBound

/-!
# Tools for the `k = 1` drift sum: the bulk mixing statement and moment arithmetic

* **`PassiveSourceMixingBulk`** (a statement; proved from the input hypotheses as
  `SourceMixingBulk.passiveSourceMixingBulk_holds`): the mixing display of
  `PassiveSourceMixingContract` with `E ∈ bulkInterval κ` quantified after `C, W₀`
  (bulk-uniform constants). It is what `PowerDriftSummable` needs along a moving energy; the
  fixed-`E` version is `SourceMixing.mixing_of_mass`.
* `pow_add_one_le`, `amgm3`, `eLpNorm_two_le_of_integral_sq`, `integral_pow_le_of_lintegral`:
  real/measure arithmetic.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal

/-- **Bulk-uniform source mixing**, with the constants uniform on compact bulk sets:
`b, κ, ε < T, p` first; then
`C, W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ` and `εW ≤ r ≤ TW`,
`‖Tr(Q_rf_r)‖_p + ‖‖Q_r^{1/2}f_rQ_r^{1/2}‖_HS‖_p ≤ C W^{-1/2}`.
The fixed-`E` case is
`PassiveSourceMixingContract.mixing`, proved as
`SourceMixing.passiveSourceMixing_holds`.
-/
def PassiveSourceMixingBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ ε T p : ℝ, 0 < κ → 0 < ε → ε < T → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => (passiveQ b E (pathX b E W r ω) *
            passiveF b E (pathX b E W r ω)).trace) (ENNReal.ofReal p) (growthPathLaw W b) +
          eLpNorm (fun ω => hsSandwich (passiveQ b E (pathX b E W r ω))
            (passiveF b E (pathX b E W r ω))) (ENNReal.ofReal p) (growthPathLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W)

theorem pow_add_one_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (x + 1) ^ n ≤ 2 ^ n * (x ^ n + 1) := by
  rcases le_total x 1 with h | h
  · calc (x + 1) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (x ^ n + 1) := le_mul_of_one_le_right (by positivity)
          (by have := pow_nonneg hx n; linarith)
  · calc (x + 1) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * x ^ n := mul_pow 2 x n
      _ ≤ 2 ^ n * (x ^ n + 1) := by gcongr; linarith

theorem amgm3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
  nlinarith [mul_nonneg (mul_nonneg hx hy) hz, sq_nonneg (x - y), sq_nonneg (y - z),
    sq_nonneg (x - z), mul_nonneg hx (sq_nonneg (y - z)), mul_nonneg hy (sq_nonneg (x - z)),
    mul_nonneg hz (sq_nonneg (x - y)), add_nonneg (add_nonneg hx hy) hz]

/-- `0 ≤ f ≤ B` a.e. and `∫ f² ≤ A` give `‖f‖₂ ≤ √A`. -/
theorem eLpNorm_two_le_of_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    {B : ℝ} (hfB : ∀ᵐ ω ∂μ, f ω ≤ B) {A : ℝ} (hI : ∫ ω, f ω ^ 2 ∂μ ≤ A) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt A) := by
  have hmem : MemLp f 2 μ := (memLp_top_of_bound hf B (by
    filter_upwards [hf0, hfB] with ω h0 h1
    rw [Real.norm_of_nonneg h0]; exact h1)).mono_exponent le_top
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by simp
  rw [h2]
  have heq : ∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ = ∫ ω, f ω ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf0] with ω hω
    rw [Real.norm_of_nonneg hω, Real.rpow_two]
  rw [heq]
  have h0 : 0 ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt hI

/-- From a `lintegral` moment bound to the real `n`-th moment. -/
theorem integral_pow_le_of_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ ((n : ℕ) : ℝ) ∂μ ≤ ENNReal.ofReal C) :
    ∫ ω, f ω ^ n ∂μ ≤ C := by
  rw [integral_eq_lintegral_of_nonneg_ae (by filter_upwards [hf0] with ω h using pow_nonneg h n)
    (hf.pow_const n).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hC (le_trans (le_of_eq ?_) h)
  refine lintegral_congr_ae ?_
  filter_upwards [hf0] with ω hω
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω, ENNReal.ofReal_rpow_of_nonneg hω (by positivity),
    Real.rpow_natCast]

end BlockBand.Transmission.Generator
