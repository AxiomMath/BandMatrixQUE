module

public import BlockBand.SourceProcess.SourceProcessLaw.Sampling
public import BlockBand.SourceProcess.ComplexSourceLaw.Gaussian
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite Dirac mixtures on `ℕ` and the tag-location law

* `diracMix s w = Σ_{k∈s} w_k⁺ δ_k`; every function is integrable (`integrable_diracMix`),
  `integral_diracMix`, and `mix_prod` (Fubini against a finite measure `μ`).
* `tagSampleLaw_eq`: for `m > 0` the law is `diracMix (range n) (q_k/(Wm))`;
  `isProbabilityMeasure_tagSampleLaw` for `q ≥ 0`; `isProbabilityMeasure_circularVectorLaw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess.SourceProcessLaw
open scoped ENNReal

/-- `Σ_{k∈s} w_k⁺ δ_k`. -/
def diracMix (s : Finset ℕ) (w : ℕ → ℝ) : Measure ℕ :=
  ∑ k ∈ s, ENNReal.ofReal (w k) • Measure.dirac k

instance (s : Finset ℕ) (w : ℕ → ℝ) : IsFiniteMeasure (diracMix s w) := by
  refine ⟨?_⟩
  simp only [diracMix, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun k _ => ENNReal.ofReal_lt_top

theorem integrable_diracMix (s : Finset ℕ) (w : ℕ → ℝ) (h : ℕ → ℝ) :
    Integrable h (diracMix s w) :=
  integrable_finsetSum_measure.2 fun _ _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

theorem integral_diracMix (s : Finset ℕ) {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (h : ℕ → ℝ) :
    ∫ k, h k ∂diracMix s w = ∑ k ∈ s, w k * h k := by
  rw [diracMix, integral_finsetSum_measure fun _ _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw k), smul_eq_mul]

/-- **Fubini against a finite Dirac mixture.** -/
theorem mix_prod {β : Type*} [MeasurableSpace β] {μ : Measure β} [IsFiniteMeasure μ]
    (s : Finset ℕ) {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) {f : ℕ × β → ℝ} (hf : Measurable f)
    (hs : ∀ k, Integrable (fun y => f (k, y)) μ) :
    Integrable f ((diracMix s w).prod μ) ∧
      ∫ x, f x ∂(diracMix s w).prod μ = ∑ k ∈ s, w k * ∫ y, f (k, y) ∂μ := by
  have hi : Integrable f ((diracMix s w).prod μ) :=
    (integrable_prod_iff hf.aestronglyMeasurable).2 ⟨ae_of_all _ hs, integrable_diracMix s w _⟩
  exact ⟨hi, by rw [integral_prod _ hi, integral_diracMix s hw]⟩

theorem tagSampleLaw_eq {W n : ℕ} {q : ℝ → ℝ} (hm : 0 < gridMass W n q) :
    tagSampleLaw W n q = diracMix (Finset.range n)
      (fun k => q (((k + 1 : ℕ) : ℝ) / W) / (W * gridMass W n q)) := by
  simp only [tagSampleLaw, hm, ite_true, diracMix]

theorem gridMass_nonneg (W n : ℕ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) : 0 ≤ gridMass W n q :=
  Finset.sum_nonneg fun _ _ => div_nonneg (hq _) (Nat.cast_nonneg _)

theorem isProbabilityMeasure_tagSampleLaw (W n : ℕ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) :
    IsProbabilityMeasure (tagSampleLaw W n q) := by
  by_cases hm : 0 < gridMass W n q
  · rw [tagSampleLaw_eq hm]
    refine ⟨?_⟩
    simp only [diracMix, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ =>
      div_nonneg (hq _) (mul_nonneg (Nat.cast_nonneg _) hm.le), ← Finset.sum_div]
    have e : ∑ k ∈ Finset.range n, q (((k + 1 : ℕ) : ℝ) / W) = W * gridMass W n q := by
      rcases Nat.eq_zero_or_pos W with hW | hW
      · subst hW; simp [gridMass] at hm
      · simp only [gridMass, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        field_simp
    rw [e, div_self (mul_pos (by
      rcases Nat.eq_zero_or_pos W with hW | hW
      · subst hW; simp [gridMass] at hm
      · exact_mod_cast hW) hm).ne', ENNReal.ofReal_one]
  · simp only [tagSampleLaw, hm, ite_false]
    infer_instance

instance isProbabilityMeasure_circularVectorLaw (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (circularVectorLaw ι) := by
  unfold circularVectorLaw; infer_instance

end BlockBand.SourceProcess.Sampling
