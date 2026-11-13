module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Fatou for centered `L^p` norms

`eLpNorm_centered_le_of_tendsto`: on a probability space, if `F_n → f` a.e., the means of `F_n`
are bounded and `‖F_n - E F_n‖_p ≤ B` for all `n`, then `‖f - E f‖_p ≤ 2B` (`f` integrable).
Proof: a convergent subsequence of the means (`tendsto_subseq_of_bounded`), Fatou
(`Lp.eLpNorm_lim_le_liminf_eLpNorm`), and `|E f - c| ≤ ‖f - c‖_p`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem enorm_integral_le_eLpNorm {f : Ω → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable f μ) :
    ‖∫ x, f x ∂μ‖ₑ ≤ eLpNorm f p μ := by
  refine (enorm_integral_le_lintegral_enorm f).trans ?_
  rw [← eLpNorm_one_eq_lintegral_enorm]
  exact eLpNorm_le_eLpNorm_of_exponent_le hp
  all_goals exact hf

theorem eLpNorm_sub_const_le {f : Ω → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p) (c d : ℂ) : eLpNorm (fun x => f x - d) p μ ≤ eLpNorm (fun x => f x - c) p μ + ‖c - d‖ₑ := by
  have h : (fun x => f x - d) = (fun x => f x - c) + fun _ => c - d := by funext x; simp
  rw [h]
  refine (eLpNorm_add_le (f := fun x => f x - c) (g := fun _ => c - d) (μ := μ) hp).trans ?_
  gcongr
  rw [eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ), measure_univ,
    ENNReal.one_rpow, mul_one]

/-- **Fatou for centered `L^p` norms** along an a.e. convergent sequence with bounded means. -/
theorem eLpNorm_centered_le_of_tendsto {F : ℕ → Ω → ℂ} {f : Ω → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hf : AEStronglyMeasurable f μ)
    (hfi : Integrable f μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) {K : ℝ}
    (hK : ∀ n, ‖∫ x, F n x ∂μ‖ ≤ K) {B : ℝ≥0∞}
    (hB : ∀ n, eLpNorm (fun x => F n x - ∫ y, F n y ∂μ) p μ ≤ B) :
    eLpNorm (fun x => f x - ∫ y, f y ∂μ) p μ ≤ 2 * B := by
  obtain ⟨c, -, φ, hφ, hc⟩ := tendsto_subseq_of_bounded (x := fun n => ∫ x, F n x ∂μ)
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := K))
    (fun n => by simpa using hK n)
  have h1 : eLpNorm (fun x => f x - c) p μ ≤ B := by
    have hFa := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p) (μ := μ)
      (f := fun k x => F (φ k) x - ∫ y, F (φ k) y ∂μ)
      (fun k => (hF _).sub aestronglyMeasurable_const) (fun x => f x - c)
      (hf.sub aestronglyMeasurable_const) (by
        filter_upwards [hlim] with x hx
        exact ((hx.comp hφ.tendsto_atTop).sub hc))
    exact hFa.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun k => hB (φ k)))
  have h2 : ‖c - ∫ y, f y ∂μ‖ₑ ≤ B := by
    have : c - ∫ y, f y ∂μ = -∫ y, (f y - c) ∂μ := by
      rw [integral_sub hfi (integrable_const c)]; simp
    rw [this, enorm_neg]
    exact (enorm_integral_le_eLpNorm hp (hf.sub aestronglyMeasurable_const)).trans h1
  calc _ ≤ eLpNorm (fun x => f x - c) p μ + ‖c - ∫ y, f y ∂μ‖ₑ :=
        eLpNorm_sub_const_le hp c _
    _ ≤ B + B := add_le_add h1 h2
    _ = 2 * B := by ring

end BlockBand.Transmission.PassiveLayer
