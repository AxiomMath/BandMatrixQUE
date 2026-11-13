module

public import BlockBand.SourceProcess.ComplexSourceLaw.ExtMatrix
public import BlockBand.SourceProcess.ComplexSourceLaw.ExtJensen
public import BlockBand.SourceProcess.ComplexSourceLaw.KcMoments

/-!
# The trace term of the extended source moments

The trace of the extended source matrix `A_Q` is a weighted sum of same-tag forms `ξ_k*Gξ_k`, so
Jensen and the same-tag raw bound at unit mass give `E|Tr A_Q|^p ≤ S^{p-1} · S · C`,
`S = Σ_k q_k/W` (`lintegral_trace_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws

variable {W n : ℕ}

/-- The unit-mass same-tag form `ξ_k*Gξ_k` at path `ω` and Gaussian `g`. -/
def tagZ (b E : ℝ) (k : Fin n) (ω : GrowthPath W) (g : Fin W → ℂ) : ℂ :=
  tagForm (fullInverse b E W n ω).toBlocks₁₁ (tagVector W n k 1 g) (tagVector W n k 1 g)

theorem measurable_tagZ_rpow (b E : ℝ) (k : Fin n) (p : ℝ) :
    Measurable fun x : GrowthPath W × (Fin W → ℂ) =>
      ENNReal.ofReal (‖tagZ b E k x.1 x.2‖ ^ p) :=
  ((measurable_tagForm ((measurable_interior b E n).comp measurable_fst)
    ((measurable_tagVector n k 1).comp measurable_snd)
    ((measurable_tagVector n k 1).comp measurable_snd)).norm.pow_const p).ennreal_ofReal

/-- Pointwise in the path: `|Tr A_Q|^p ≤ S^{p-1} Σ_k w_k E_g|ξ_k*Gξ_k|^p`. -/
theorem trace_rpow_le (b E : ℝ) (q : Fin n → ℝ) (hq : ∀ k, 0 ≤ q k) (ω : GrowthPath W)
    {p : ℝ} (hp : 1 ≤ p) :
    ENNReal.ofReal (‖(extendedSourceMatrix b E W n q ω).trace‖ ^ p) ≤
      ENNReal.ofReal ((∑ k, q k / W) ^ (p - 1)) * ∑ k, ENNReal.ofReal (q k / W) *
        ∫⁻ g, ENNReal.ofReal (‖tagZ b E k ω g‖ ^ p) ∂circularVectorLaw (Fin W) := by
  have hw : ∀ k, 0 ≤ q k / W := fun k => div_nonneg (hq k) (Nat.cast_nonneg W)
  have hp0 : 0 ≤ p := by linarith
  set a : Fin n → ℝ := fun k => ∫ g, ‖tagZ b E k ω g‖ ∂circularVectorLaw (Fin W)
  have ha : ∀ k, 0 ≤ a k := fun k => integral_nonneg fun _ => norm_nonneg _
  have h1 : ‖(extendedSourceMatrix b E W n q ω).trace‖ ≤ ∑ k, q k / W * a k := by
    rw [trace_extended b E q hq ω]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw k)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (hw k)
  have h2 := (Real.rpow_le_rpow (norm_nonneg _) h1 hp0).trans
    (weighted_rpow_le Finset.univ (fun k => q k / W) a (fun k _ => hw k) (fun k _ => ha k) hp)
  refine (ENNReal.ofReal_le_ofReal h2).trans ?_
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Finset.sum_nonneg fun k _ => hw k) _),
    ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg (hw k) (Real.rpow_nonneg (ha k) p)]
  gcongr with k
  rw [ENNReal.ofReal_mul (hw k)]
  gcongr
  have hint : Integrable (fun g => ‖tagZ b E k ω g‖) (circularVectorLaw (Fin W)) :=
    (integrable_tagZ (fullInverse b E W n ω).toBlocks₁₁ k).norm
  have hF : Measurable fun g => ENNReal.ofReal ‖tagZ b E k ω g‖ :=
    (measurable_tagForm measurable_const (measurable_tagVector n k 1)
      (measurable_tagVector n k 1)).norm.ennreal_ofReal
  rw [← ENNReal.ofReal_rpow_of_nonneg (ha k) hp0,
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => norm_nonneg _)]
  exact (rpow_lintegral_le _ hF.aemeasurable hp).trans_eq
    (lintegral_congr fun g => ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0)

/-- **The trace term**: `E|Tr A_Q|^p ≤ S^{p-1} · S · C`, `S = Σ_k q_k/W`, from the same-tag raw
bound at unit mass. -/
theorem lintegral_trace_le (b E : ℝ) (q : Fin n → ℝ) (hq : ∀ k, 0 ≤ q k) {p C : ℝ} (hp : 1 ≤ p)
    (hraw : RawTagBoundAt b E W n p C) :
    ∫⁻ ω, ENNReal.ofReal (‖(extendedSourceMatrix b E W n q ω).trace‖ ^ p) ∂growthPathLaw W b ≤
      ENNReal.ofReal ((∑ k, q k / W) ^ (p - 1)) *
        (ENNReal.ofReal (∑ k, q k / W) * ENNReal.ofReal C) := by
  have hw : ∀ k, 0 ≤ q k / W := fun k => div_nonneg (hq k) (Nat.cast_nonneg W)
  have hFk : ∀ k : Fin n, Measurable fun ω => ∫⁻ g, ENNReal.ofReal (‖tagZ b E k ω g‖ ^ p)
      ∂circularVectorLaw (Fin W) := fun k =>
    (measurable_tagZ_rpow (W := W) b E k p).lintegral_prod_right'
  refine (lintegral_mono fun ω => trace_rpow_le b E q hq ω hp).trans ?_
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => (hFk k).const_mul _),
    lintegral_finsetSum _ fun k _ => (hFk k).const_mul _]
  refine mul_le_mul_right ?_ _
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ => hw k, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [lintegral_const_mul _ (hFk k)]
  refine mul_le_mul_right ?_ _
  rw [← lintegral_prod _ (measurable_tagZ_rpow b E k p).aemeasurable]
  have h := (hraw k k 1 1 zero_le_one zero_le_one).2
  simp only [mul_one, Real.one_rpow] at h
  exact h

end BlockBand.SourceProcess.ComplexSourceLaw
