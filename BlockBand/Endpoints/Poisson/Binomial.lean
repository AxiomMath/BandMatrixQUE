module

public import BlockBand.Endpoints.FinitePointMeasure
public import BlockBand.PointProcess.Specifications

/-!
# Binomial approximants of the unit Poisson law

The configuration of `2n+2` independent uniform points on the window `(-(n+1), n+1)` has
Laplace functional converging to that of the unit-intensity Poisson process, and its expected
counts are bounded by Lebesgue measure.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- Number of binomial points at stage `n`. -/
def binomialCount (n : ℕ) : ℕ := 2 * n + 2

/-- The symmetric window `(-(n+1), n+1)` of length `binomialCount n`. -/
def binomialWindow (n : ℕ) : Set ℝ := Set.Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1)

theorem measurableSet_binomialWindow (n : ℕ) : MeasurableSet (binomialWindow n) :=
  measurableSet_Ioo

theorem volume_binomialWindow (n : ℕ) :
    volume (binomialWindow n) = ENNReal.ofReal (binomialCount n) := by
  rw [binomialWindow, Real.volume_Ioo, binomialCount]
  congr 1
  push_cast
  ring

theorem binomialCount_pos (n : ℕ) : (0 : ℝ) < binomialCount n := by
  unfold binomialCount; positivity

/-- The uniform probability law on the binomial window. -/
def binomialUniform (n : ℕ) : Measure ℝ := volume[|binomialWindow n]

instance (n : ℕ) : IsProbabilityMeasure (binomialUniform n) := by
  unfold binomialUniform
  refine cond_isProbabilityMeasure_of_finite ?_ ?_
  · rw [volume_binomialWindow]
    exact (ENNReal.ofReal_pos.mpr (binomialCount_pos n)).ne'
  · rw [volume_binomialWindow]; exact ENNReal.ofReal_ne_top

/-- The law of the `2n+2` independent uniform points. -/
def binomialPointLaw (n : ℕ) : Measure (Fin (binomialCount n) → ℝ) :=
  Measure.pi fun _ => binomialUniform n

instance (n : ℕ) : IsProbabilityMeasure (binomialPointLaw n) := by
  unfold binomialPointLaw; infer_instance

theorem integral_binomialUniform (n : ℕ) (g : ℝ → ℝ) :
    ∫ y, g y ∂binomialUniform n =
      (binomialCount n : ℝ)⁻¹ * ∫ y in binomialWindow n, g y := by
  rw [binomialUniform, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul,
    volume_binomialWindow, ENNReal.toReal_inv, ENNReal.toReal_ofReal (binomialCount_pos n).le]

/-- For `f` supported in the window, the uniform mean of `exp (-f)` is
`1 - (∫ (1 - exp (-f))) / (2n+2)`. -/
theorem integral_exp_neg_binomialUniform (n : ℕ)
    (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : tsupport f ⊆ binomialWindow n) :
    ∫ y, Real.exp (-f y) ∂binomialUniform n =
      1 - (∫ y, (1 - Real.exp (-f y))) / (binomialCount n : ℝ) := by
  have hint : Integrable (fun y => 1 - Real.exp (-f y)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine f.hasCompactSupport.mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro h0
    exact hy (by rw [h0, neg_zero, Real.exp_zero, sub_self])
  have hzero : ∀ y ∉ binomialWindow n, 1 - Real.exp (-f y) = 0 := by
    intro y hy
    have : f y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hf h))
    rw [this, neg_zero, Real.exp_zero, sub_self]
  have hsplit : ∫ y in binomialWindow n, Real.exp (-f y) =
      (binomialCount n : ℝ) - ∫ y in binomialWindow n, (1 - Real.exp (-f y)) := by
    have hfin : volume (binomialWindow n) < ∞ := by
      rw [volume_binomialWindow]; exact ENNReal.ofReal_lt_top
    have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (binomialWindow n) :=
      integrableOn_const hfin.ne
    have hrw : ∫ y in binomialWindow n, Real.exp (-f y) =
        ∫ y in binomialWindow n, ((1 : ℝ) - (1 - Real.exp (-f y))) := by
      congr 1; ext y; ring
    rw [hrw, integral_sub h1 hint.integrableOn, setIntegral_const, smul_eq_mul, mul_one,
      Measure.real, volume_binomialWindow, ENNReal.toReal_ofReal (binomialCount_pos n).le]
  rw [integral_binomialUniform, hsplit,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  field_simp [(binomialCount_pos n).ne']

/-- Exact Laplace transform of the binomial configuration for any real test. -/
theorem integral_exp_neg_sum_binomialPointLaw (n : ℕ) (g : ℝ → ℝ) :
    ∫ x, Real.exp (-∑ j, g (x j)) ∂binomialPointLaw n =
      (∫ y, Real.exp (-g y) ∂binomialUniform n) ^ binomialCount n := by
  have h : ∀ x : Fin (binomialCount n) → ℝ,
      Real.exp (-∑ j, g (x j)) = ∏ j, Real.exp (-g (x j)) := by
    intro x
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [h]
  rw [binomialPointLaw, integral_fintype_prod_eq_prod (fun _ y => Real.exp (-g y)),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Laplace transforms of the binomial approximants converge to the unit
Poisson Laplace functional `exp (-∫ (1 - exp (-f)))`, for every compactly supported
continuous `f` (no sign condition is needed). -/
theorem tendsto_integral_exp_neg_sum_binomialPointLaw
    (f : CompactlySupportedContinuousMap ℝ ℝ) :
    Tendsto (fun n => ∫ x, Real.exp (-∑ j, f (x j)) ∂binomialPointLaw n) atTop
      (𝓝 (Real.exp (-∫ y, (1 - Real.exp (-f y))))) := by
  set a := ∫ y, (1 - Real.exp (-f y))
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport f ⊆ Set.Icc (-R) R := by
    obtain ⟨R, hR⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
    refine ⟨R, fun y hy => ?_⟩
    have := hR hy
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp this
  have hev : ∀ᶠ n : ℕ in atTop,
      ∫ x, Real.exp (-∑ j, f (x j)) ∂binomialPointLaw n =
        (1 + (-a) / (binomialCount n : ℝ)) ^ binomialCount n := by
    filter_upwards [eventually_gt_atTop ⌈R⌉₊] with n hn
    have hsub : tsupport f ⊆ binomialWindow n := by
      intro y hy
      have hy' := hR hy
      have hRn : R < (n : ℝ) + 1 := by
        have := Nat.le_ceil R
        have : (⌈R⌉₊ : ℝ) < n := by exact_mod_cast hn
        linarith
      exact ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
    rw [integral_exp_neg_sum_binomialPointLaw, integral_exp_neg_binomialUniform n f hsub]
    congr 1
    simp only [a]
    ring
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have hlim := Real.tendsto_one_add_div_pow_exp (-a)
  have hcount : Tendsto binomialCount atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => ?_⟩
    unfold binomialCount
    omega
  exact hlim.comp hcount

/-- Expected counts: `E ∑ j, g (x j) ≤ ∫ g` for nonnegative continuous `g`,
in extended nonnegative reals. -/
theorem lintegral_sum_binomialPointLaw_le (n : ℕ) (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ y, 0 ≤ g y) :
    ∫⁻ x, ENNReal.ofReal (∑ j, g (x j)) ∂binomialPointLaw n ≤
      ∫⁻ y, ENNReal.ofReal (g y) := by
  have h : ∀ x : Fin (binomialCount n) → ℝ,
      ENNReal.ofReal (∑ j, g (x j)) = ∑ j, ENNReal.ofReal (g (x j)) := by
    intro x
    exact ENNReal.ofReal_sum_of_nonneg fun j _ => hg0 (x j)
  simp_rw [h]
  rw [lintegral_finsetSum Finset.univ (f := fun (j : Fin (binomialCount n)) (x : Fin (binomialCount n) → ℝ) =>
      ENNReal.ofReal (g (x j)))
    (fun j _ => (ENNReal.measurable_ofReal.comp hg.measurable).comp (measurable_pi_apply j))]
  have hj : ∀ j : Fin (binomialCount n),
      ∫⁻ x, ENNReal.ofReal (g (x j)) ∂binomialPointLaw n =
        ∫⁻ y, ENNReal.ofReal (g y) ∂binomialUniform n := by
    intro j
    rw [binomialPointLaw]
    exact (measurePreserving_eval (fun _ => binomialUniform n) j).lintegral_comp
      (ENNReal.measurable_ofReal.comp hg.measurable)
  simp_rw [hj]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, binomialUniform,
    ProbabilityTheory.cond, lintegral_smul_measure, volume_binomialWindow, smul_eq_mul,
    ← mul_assoc]
  have hc : ((binomialCount n : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (binomialCount n))⁻¹ = 1 := by
    rw [ENNReal.ofReal_natCast]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast (binomialCount_pos n).ne')
      (ENNReal.natCast_ne_top _)
  rw [hc, one_mul]
  exact setLIntegral_le_lintegral _ _

end BlockBand.Endpoints
