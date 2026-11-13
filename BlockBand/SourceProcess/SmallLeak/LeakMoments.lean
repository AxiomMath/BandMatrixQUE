module

public import BlockBand.SourceProcess.FullSource.MomentStep
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Hölder bounds for the summed leakage recursion

For `0 ≤ δ` with `‖δ‖₄ ≤ D` and `0 ≤ g ≤ V` with `E g ≤ x`:
`E[δ√g] ≤ D√x`, `E√g ≤ √x`, `E[δ²g] ≤ D²√(Vx)` (`moment_bounds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Cauchy–Schwarz: `E[fg] ≤ √(Ef²)√(Eg²)` for nonnegative square-integrable `f, g`. -/
theorem integral_mul_le_sqrt {f g : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf : Integrable (fun ω => f ω ^ 2) μ) (hg : Integrable (fun ω => g ω ^ 2) μ) :
    ∫ ω, f ω * g ω ∂μ ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hf2 : MemLp f (ENNReal.ofReal 2) μ := by rw [h2]; exact (memLp_two_iff_integrable_sq hfm).2 hf
  have hg2 : MemLp g (ENNReal.ofReal 2) μ := by rw [h2]; exact (memLp_two_iff_integrable_sq hgm).2 hg
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (ae_of_all _ hf0) (ae_of_all _ hg0) hf2 hg2
  simp only [Real.rpow_two] at h
  rwa [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h

/-- **The three moment bounds.** -/
theorem moment_bounds {δ g : Ω → ℝ} {D V x : ℝ} (hδ0 : ∀ ω, 0 ≤ δ ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hgm : AEStronglyMeasurable g μ) (hgV : ∀ᵐ ω ∂μ, g ω ≤ V) (hD : 0 ≤ D)
    (hδ : MomBd μ δ ((4 : ℕ) : ℝ) D) (hx : ∫ ω, g ω ∂μ ≤ x) :
    (Integrable (fun ω => δ ω * Real.sqrt (g ω)) μ ∧
      ∫ ω, δ ω * Real.sqrt (g ω) ∂μ ≤ D * Real.sqrt x) ∧
    (Integrable (fun ω => Real.sqrt (g ω)) μ ∧ ∫ ω, Real.sqrt (g ω) ∂μ ≤ Real.sqrt x) ∧
    (Integrable (fun ω => δ ω ^ 2 * g ω) μ ∧
      ∫ ω, δ ω ^ 2 * g ω ∂μ ≤ D ^ 2 * Real.sqrt (V * x)) ∧
    Integrable g μ := by
  have hV : 0 ≤ V ∨ True := Or.inr trivial
  clear hV
  have hgI : Integrable g μ := by
    refine Integrable.mono' (integrable_const (max V 0)) hgm (hgV.mono fun ω h => ?_)
    rw [Real.norm_of_nonneg (hg0 ω)]; exact h.trans (le_max_left _ _)
  obtain ⟨h4i, h4b⟩ := integral_abs_pow_le (ν := μ) (n := 4) (by norm_num) hD hδ
  obtain ⟨h2i, h2b⟩ := integral_abs_pow_le (ν := μ) (n := 2) (by norm_num) hD
    (hδ.exponent_mono (by norm_num))
  simp only [abs_of_nonneg (hδ0 _)] at h4i h4b h2i h2b
  have hδm : AEStronglyMeasurable δ μ := hδ.1
  have hsgm : AEStronglyMeasurable (fun ω => Real.sqrt (g ω)) μ :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hgm)
  have hsq : ∀ ω, Real.sqrt (g ω) ^ 2 = g ω := fun ω => Real.sq_sqrt (hg0 ω)
  have hsgi2 : Integrable (fun ω => Real.sqrt (g ω) ^ 2) μ := by simp only [hsq]; exact hgI
  have hx0 : ∫ ω, g ω ∂μ ≤ x := hx
  have hEg : 0 ≤ ∫ ω, g ω ∂μ := integral_nonneg hg0
  -- `E[δ√g]`
  have i1 : Integrable (fun ω => δ ω * Real.sqrt (g ω)) μ := by
    refine Integrable.mono' (h2i.add hgI) (hδm.mul hsgm) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hδ0 ω) (Real.sqrt_nonneg _))]
    show δ ω * Real.sqrt (g ω) ≤ δ ω ^ 2 + g ω
    have := sq_nonneg (δ ω - Real.sqrt (g ω)); have := hsq ω
    have := mul_nonneg (hδ0 ω) (Real.sqrt_nonneg (g ω))
    nlinarith
  have b1 := integral_mul_le_sqrt hδ0 (fun ω => Real.sqrt_nonneg _) hδm hsgm h2i hsgi2
  simp only [hsq] at b1
  have b1' : ∫ ω, δ ω * Real.sqrt (g ω) ∂μ ≤ D * Real.sqrt x := by
    refine b1.trans (mul_le_mul ?_ (Real.sqrt_le_sqrt hx0) (Real.sqrt_nonneg _) hD)
    rw [show D = Real.sqrt (D ^ 2) from (Real.sqrt_sq hD).symm]; exact Real.sqrt_le_sqrt h2b
  -- `E√g`
  have i2 : Integrable (fun ω => Real.sqrt (g ω)) μ := by
    refine Integrable.mono' ((integrable_const 1).add hgI) hsgm (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    show Real.sqrt (g ω) ≤ 1 + g ω
    have := sq_nonneg (Real.sqrt (g ω) - 1); have := hsq ω
    nlinarith
  have b2 := integral_mul_le_sqrt (f := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (fun ω => Real.sqrt_nonneg (g ω)) aestronglyMeasurable_const hsgm (integrable_const _) hsgi2
  simp only [one_mul, one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one,
    Real.sqrt_one, hsq] at b2
  -- `E[δ²g]`
  have hg2 : Integrable (fun ω => g ω ^ 2) μ := by
    refine Integrable.mono' (hgI.const_mul (max V 0)) (hgm.pow 2) (hgV.mono fun ω h => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (h.trans (le_max_left _ _)) (hg0 ω)
  have i3 : Integrable (fun ω => δ ω ^ 2 * g ω) μ := by
    refine Integrable.mono' (h4i.add hg2) ((hδm.pow 2).mul hgm)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hg0 ω))]
    show δ ω ^ 2 * g ω ≤ δ ω ^ 4 + g ω ^ 2
    have := sq_nonneg (δ ω ^ 2 - g ω); have := mul_nonneg (sq_nonneg (δ ω)) (hg0 ω)
    nlinarith
  have b3 := integral_mul_le_sqrt (f := fun ω => δ ω ^ 2) (fun ω => sq_nonneg _) hg0
    (hδm.pow 2) hgm (by simp only [← pow_mul]; exact h4i) hg2
  have hg2b : ∫ ω, g ω ^ 2 ∂μ ≤ max V 0 * x := by
    refine (integral_mono_ae hg2 (hgI.const_mul (max V 0)) (hgV.mono fun ω h => ?_)).trans ?_
    · show g ω ^ 2 ≤ max V 0 * g ω
      rw [sq]; exact mul_le_mul_of_nonneg_right (h.trans (le_max_left _ _)) (hg0 ω)
    · rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hx0 (le_max_right _ _)
  have b3' : ∫ ω, δ ω ^ 2 * g ω ∂μ ≤ D ^ 2 * Real.sqrt (max V 0 * x) := by
    refine b3.trans (mul_le_mul ?_ (Real.sqrt_le_sqrt hg2b) (Real.sqrt_nonneg _) (by positivity))
    simp only [← pow_mul]
    rw [show D ^ 2 = Real.sqrt ((D ^ 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm, ← pow_mul]
    exact Real.sqrt_le_sqrt h4b
  refine ⟨⟨i1, b1'⟩, ⟨i2, b2.trans (Real.sqrt_le_sqrt hx0)⟩, ⟨i3, ?_⟩, hgI⟩
  rcases le_or_gt V 0 with hV0 | hV0
  · have hz : ∀ᵐ ω ∂μ, δ ω ^ 2 * g ω = 0 := hgV.mono fun ω h => by
      rw [le_antisymm (h.trans hV0) (hg0 ω), mul_zero]
    rw [integral_congr_ae hz, integral_zero]; positivity
  · rwa [max_eq_left hV0.le] at b3'

end BlockBand.SourceProcess.SmallLeak
