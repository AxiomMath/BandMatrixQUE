module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Explicit `L^p` moment bounds and their algebra

`MomBd μ f p C`: `f` is a.e.-strongly measurable and `‖f‖_{L^p(μ)} ≤ C`. Closure lemmas
(probability `μ` where needed): constants, sums (Minkowski, `p ≥ 1`), products (Hölder,
exponents `2p, 2p → p`), domination, monotonicity in `C` and in the exponent, and the passage
from `∫ ‖f‖^p ≤ C` (`of_lintegral`). Constants are explicit, so uniformity over a family is
read off from the constants.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- `f` is a.e.-strongly measurable with `‖f‖_p ≤ C`. -/
def MomBd (μ : Measure α) (f : α → ℝ) (p C : ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C

theorem MomBd.const (c p : ℝ) (hp : 0 < p) : MomBd μ (fun _ => c) p |c| := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  rw [eLpNorm_const c (by simpa using hp) (IsProbabilityMeasure.ne_zero μ), measure_univ,
    ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]

omit [IsProbabilityMeasure μ] in
theorem MomBd.add {f g : α → ℝ} {p C₁ C₂ : ℝ} (hp : 1 ≤ p) (hf : MomBd μ f p C₁)
    (hg : MomBd μ g p C₂) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) : MomBd μ (fun x => f x + g x) p (C₁ + C₂) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  have := eLpNorm_add_le (f := f) (g := g) (μ := μ)
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal p by simpa using ENNReal.ofReal_le_ofReal hp)
  rw [ENNReal.ofReal_add h₁ h₂]
  exact this.trans (add_le_add hf.2 hg.2)

omit [IsProbabilityMeasure μ] in
theorem MomBd.mul {f g : α → ℝ} {p C₁ C₂ : ℝ} (hp : 0 < p) (hf : MomBd μ f (2 * p) C₁)
    (hg : MomBd μ g (2 * p) C₂) (h₁ : 0 ≤ C₁) : MomBd μ (fun x => f x * g x) p (C₁ * C₂) := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  have hT : ENNReal.HolderTriple (ENNReal.ofReal (2 * p)) (ENNReal.ofReal (2 * p))
      (ENNReal.ofReal p) := by
    constructor
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hp,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal (2 * p)) (q := ENNReal.ofReal (2 * p))
    (r := ENNReal.ofReal p) hf.1 hg.1
  rw [ENNReal.ofReal_mul h₁]
  exact (le_of_eq (by rfl)).trans (this.trans (mul_le_mul' hf.2 hg.2))

omit [IsProbabilityMeasure μ] in
theorem MomBd.mono {f g : α → ℝ} {p C : ℝ} (hg : MomBd μ g p C) (hf : AEStronglyMeasurable f μ)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) : MomBd μ f p C :=
  ⟨hf, (eLpNorm_mono_ae_real hf h).trans hg.2⟩

omit [IsProbabilityMeasure μ] in
theorem MomBd.of_le {f : α → ℝ} {p C C' : ℝ} (hf : MomBd μ f p C) (h : C ≤ C') : MomBd μ f p C' :=
  ⟨hf.1, hf.2.trans (ENNReal.ofReal_le_ofReal h)⟩

theorem MomBd.exponent_mono {f : α → ℝ} {p q C : ℝ} (hpq : p ≤ q) (hf : MomBd μ f q C) :
    MomBd μ f p C :=
  ⟨hf.1, (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)).trans hf.2⟩

omit [IsProbabilityMeasure μ] in
theorem MomBd.of_lintegral {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {p C : ℝ} (hp : 0 < p)
    (hC : 0 ≤ C) (h : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≤ ENNReal.ofReal C) : MomBd μ f p (C ^ (1 / p)) := by
  refine ⟨hf, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.ofReal_rpow_of_nonneg hC (by positivity)]
  exact ENNReal.rpow_le_rpow h (by positivity)

omit [IsProbabilityMeasure μ] in
theorem MomBd.nonneg {f : α → ℝ} {p C : ℝ} (hf : MomBd μ f p C) : MomBd μ f p (max C 0) :=
  hf.of_le (le_max_left _ _)

omit [IsProbabilityMeasure μ] in
theorem MomBd.const_mul {f : α → ℝ} {p C c : ℝ} (hf : MomBd μ f p C) (hc : 0 ≤ c) :
    MomBd μ (fun x => c * f x) p (c * C) := by
  refine ⟨hf.1.const_mul c, ?_⟩
  have h := eLpNorm_const_smul c f (ENNReal.ofReal p) μ
  rw [show (c • f) = fun x => c * f x from rfl] at h
  rw [h, Real.enorm_eq_ofReal hc]
  calc ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal c * ENNReal.ofReal C :=
        by gcongr; exact hf.2
    _ = _ := (ENNReal.ofReal_mul hc).symm

end BlockBand.Transmission.PassiveLayer
