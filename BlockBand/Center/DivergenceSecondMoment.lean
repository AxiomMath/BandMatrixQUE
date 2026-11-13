module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

/-!
# Finite divergence cross-term estimate

From the Gaussian divergence isometry `E D² = ((2W)²/s) Σ_e E f_e² + Σ_{e ≠ g} E[df_{e,g} df_{g,e}]`
and the bounds `E f_e² ≤ A/W⁴`, `E df_{e,g}² ≤ (B/W²)(a_{eg} + W^{-1/2})²` with
`Σ_g a_{eg}² ≤ R`, the second moment satisfies
`E D² ≤ (4A/s + 2BR) n/W² + 2B n²/W³`, `n = card ι`, which is `O(n/W²)` for `n ≤ TW`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory
open scoped BigOperators

/-- Square integrability of two real functions gives integrability of their product. -/
theorem integrable_mul_of_integrable_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ)
    (hg2 : Integrable (fun ω => g ω ^ 2) μ) :
    Integrable (fun ω => f ω * g ω) μ := by
  apply ((hf2.add hg2).div_const 2).mono' (hf.mul hg)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  have habs : |f ω * g ω| ≤ (f ω ^ 2 + g ω ^ 2) / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (f ω - g ω), sq_nonneg (f ω + g ω)]
  exact habs

/-- Real cross-moment estimate using only first-derivative squares. -/
theorem integral_mul_le_half_square_sum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ)
    (hg2 : Integrable (fun ω => g ω ^ 2) μ) :
    (∫ ω, f ω * g ω ∂μ) ≤
      ((∫ ω, f ω ^ 2 ∂μ) + ∫ ω, g ω ^ 2 ∂μ) / 2 := by
  calc
    (∫ ω, f ω * g ω ∂μ) ≤ ∫ ω, (f ω ^ 2 + g ω ^ 2) / 2 ∂μ := by
      apply integral_mono (integrable_mul_of_integrable_sq hf hg hf2 hg2)
        ((hf2.add hg2).div_const 2)
      intro ω
      change f ω * g ω ≤ (f ω ^ 2 + g ω ^ 2) / 2
      nlinarith [sq_nonneg (f ω - g ω)]
    _ = _ := by rw [integral_div, integral_add hf2 hg2]

/-- The complete off-diagonal cross sum is bounded by the complete derivative
square sum. Transposition preserves the ordered off-diagonal pairs, so no
independence between `df_{e,g}` and `df_{g,e}` is needed. -/
theorem cross_moment_sum_le_square_sum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (df : ι → ι → Ω → ℝ)
    (hm : ∀ e g, AEStronglyMeasurable (df e g) μ)
    (h2 : ∀ e g, Integrable (fun ω => df e g ω ^ 2) μ) :
    (∑ e, ∑ g ∈ Finset.univ.erase e,
      ∫ ω, df e g ω * df g e ω ∂μ) ≤
      ∑ e, ∑ g, ∫ ω, df e g ω ^ 2 ∂μ := by
  have hpair : ∀ e g,
      (∫ ω, df e g ω * df g e ω ∂μ) ≤
        ((∫ ω, df e g ω ^ 2 ∂μ) + ∫ ω, df g e ω ^ 2 ∂μ) / 2 :=
    fun e g => integral_mul_le_half_square_sum (hm e g) (hm g e) (h2 e g) (h2 g e)
  have hnonneg : ∀ e g, 0 ≤ ∫ ω, df e g ω ^ 2 ∂μ :=
    fun e g => integral_nonneg fun _ => sq_nonneg _
  calc
    (∑ e, ∑ g ∈ Finset.univ.erase e,
      ∫ ω, df e g ω * df g e ω ∂μ) ≤
        ∑ e, ∑ g ∈ Finset.univ.erase e,
          ((∫ ω, df e g ω ^ 2 ∂μ) + ∫ ω, df g e ω ^ 2 ∂μ) / 2 := by
      exact Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun g _ => hpair e g
    _ ≤ ∑ e, ∑ g,
        ((∫ ω, df e g ω ^ 2 ∂μ) + ∫ ω, df g e ω ^ 2 ∂μ) / 2 := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro g _ _
      positivity
    _ = ∑ e, ∑ g, ∫ ω, df e g ω ^ 2 ∂μ := by
      simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun e g => ∫ ω, df g e ω ^ 2 ∂μ)]
      ring

/-- Row-square summability turns a decay-plus-floor bound into the `n + n²/W`
form: `Σ_{e,g} (a_{eg} + ε)² ≤ 2nR + 2n²ε²`. The kernel `a` is any real kernel; nonnegativity
of its entries is unnecessary. -/
theorem decay_floor_square_sum_le
    {ι : Type*} [Fintype ι] (a : ι → ι → ℝ) (ε R : ℝ)
    (hrow : ∀ e, ∑ g, a e g ^ 2 ≤ R) :
    (∑ e, ∑ g, (a e g + ε) ^ 2) ≤
      2 * (Fintype.card ι : ℝ) * R + 2 * (Fintype.card ι : ℝ) ^ 2 * ε ^ 2 := by
  calc
    (∑ e, ∑ g, (a e g + ε) ^ 2) ≤
        ∑ e, ∑ g, (2 * a e g ^ 2 + 2 * ε ^ 2) := by
      exact Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun g _ => by
        nlinarith [sq_nonneg (a e g - ε)]
    _ = 2 * (∑ e, ∑ g, a e g ^ 2) +
        2 * (Fintype.card ι : ℝ) ^ 2 * ε ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have htotal : (∑ e, ∑ g, a e g ^ 2) ≤ (Fintype.card ι : ℝ) * R := by
        simpa using Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hrow e)
      linarith

/-- The cross contribution to the second moment, from first-derivative bounds
`E df_{e,g}² ≤ B (a_{eg} + ε)²` with row-square summable `a`. -/
theorem cross_moment_sum_le_decay_budget
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (df : ι → ι → Ω → ℝ)
    (hm : ∀ e g, AEStronglyMeasurable (df e g) μ)
    (h2 : ∀ e g, Integrable (fun ω => df e g ω ^ 2) μ)
    (a : ι → ι → ℝ) (ε R B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ e, ∑ g, a e g ^ 2 ≤ R)
    (hbound : ∀ e g, (∫ ω, df e g ω ^ 2 ∂μ) ≤ B * (a e g + ε) ^ 2) :
    (∑ e, ∑ g ∈ Finset.univ.erase e,
      ∫ ω, df e g ω * df g e ω ∂μ) ≤
      B * (2 * (Fintype.card ι : ℝ) * R +
        2 * (Fintype.card ι : ℝ) ^ 2 * ε ^ 2) := by
  calc
    _ ≤ ∑ e, ∑ g, ∫ ω, df e g ω ^ 2 ∂μ :=
      cross_moment_sum_le_square_sum μ df hm h2
    _ ≤ ∑ e, ∑ g, B * (a e g + ε) ^ 2 := by
      exact Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun g _ => hbound e g
    _ = B * (∑ e, ∑ g, (a e g + ε) ^ 2) := by
      simp only [← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (decay_floor_square_sum_le a ε R hrow) hB

/-- Second-moment bound from the Gaussian divergence isometry, with `n = card ι` and
`σ² = s/(2W)²`. The isometry, the functions `f`, `df` and the row summability of the kernel are
hypotheses; no dimension limit is taken. -/
theorem secondMoment_le_physical_budget_of_isometry
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (df : ι → ι → Ω → ℝ) (D : Ω → ℝ)
    (hm : ∀ e g, AEStronglyMeasurable (df e g) μ)
    (h2 : ∀ e g, Integrable (fun ω => df e g ω ^ 2) μ)
    (a : ι → ι → ℝ) (W s A B R : ℝ) (hW : 0 < W) (hs : 0 < s) (hB : 0 ≤ B)
    (hrow : ∀ e, ∑ g, a e g ^ 2 ≤ R)
    (hf : ∀ e, (∫ ω, f e ω ^ 2 ∂μ) ≤ A / W ^ 4)
    (hdf : ∀ e g, (∫ ω, df e g ω ^ 2 ∂μ) ≤
      (B / W ^ 2) * (a e g + 1 / Real.sqrt W) ^ 2)
    (hisometry : (∫ ω, D ω ^ 2 ∂μ) =
      ((2 * W) ^ 2 / s) * (∑ e, ∫ ω, f e ω ^ 2 ∂μ) +
      ∑ e, ∑ g ∈ Finset.univ.erase e,
        ∫ ω, df e g ω * df g e ω ∂μ) :
    (∫ ω, D ω ^ 2 ∂μ) ≤
      (4 * A / s + 2 * B * R) * (Fintype.card ι : ℝ) / W ^ 2 +
        2 * B * (Fintype.card ι : ℝ) ^ 2 / W ^ 3 := by
  have hfloor : (1 / Real.sqrt W) ^ 2 = 1 / W := by
    rw [div_pow, one_pow, Real.sq_sqrt hW.le]
  have hdiagonal : (∑ e, ∫ ω, f e ω ^ 2 ∂μ) ≤
      (Fintype.card ι : ℝ) * (A / W ^ 4) := by
    simpa using Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hf e)
  have hcross := cross_moment_sum_le_decay_budget μ df hm h2 a
    (1 / Real.sqrt W) R (B / W ^ 2) (div_nonneg hB (sq_nonneg W)) hrow hdf
  rw [hfloor] at hcross
  rw [hisometry]
  calc
    _ ≤ ((2 * W) ^ 2 / s) * ((Fintype.card ι : ℝ) * (A / W ^ 4)) +
        (B / W ^ 2) * (2 * (Fintype.card ι : ℝ) * R +
          2 * (Fintype.card ι : ℝ) ^ 2 * (1 / W)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hdiagonal (by positivity)) hcross
    _ = _ := by
      field_simp [hW.ne', hs.ne']
      ring

/-- For `n ≤ TW` the `n²/W³` term is absorbed: uniformly over all finite edge sets in that
range, not as a large-`n` limit. -/
theorem physical_budget_le_linear_budget
    {n W T C B : ℝ} (hn : 0 ≤ n) (hW : 0 < W) (hB : 0 ≤ B)
    (hrange : n ≤ T * W) :
    C * n / W ^ 2 + 2 * B * n ^ 2 / W ^ 3 ≤ (C + 2 * B * T) * n / W ^ 2 := by
  have hn2 : n ^ 2 ≤ T * W * n := by nlinarith
  calc
    _ ≤ C * n / W ^ 2 + 2 * B * (T * W * n) / W ^ 3 := by
      gcongr
    _ = _ := by
      field_simp [hW.ne']

/-- If `D` is a.e. strongly measurable, `D²` is integrable and `∫ D² ≤ V`, then `D ∈ L²(μ)` and
`‖D‖_{L²} ≤ √V`. The `MemLp` conclusion rules out an infinite extended norm; `μ` is any
measure. -/
theorem memLp_two_and_lpNorm_le_sqrt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {D : Ω → ℝ} {V : ℝ}
    (hm : AEStronglyMeasurable D μ)
    (h2 : Integrable (fun ω => D ω ^ 2) μ)
    (hbound : (∫ ω, D ω ^ 2 ∂μ) ≤ V) :
    MemLp D 2 μ ∧ lpNorm D 2 μ ≤ Real.sqrt V := by
  constructor
  · apply (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).mp
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h2
  · rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hm]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hbound

end BlockBand.Center
