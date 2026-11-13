module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Conditional Jensen for a weighted average

`jensen_lintegral`: for any measure `μ`, an integrable weight `g ≥ 0` with mass `Z = ∫g`, a
complex `X` with `gX` integrable, and `ρ > 1`:
`Z · |∫gX / Z|^ρ ≤ ∫ g|X|^ρ` (lower integral on the right, so no integrability of `g|X|^ρ` is
assumed). Proof by the supporting line of `y ↦ y^ρ` at the weighted mean of `|X|` (Bernoulli's
inequality `one_add_mul_self_le_rpow_one_add`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.RbarMoment

open MeasureTheory

/-- The supporting line of `y ↦ y^ρ` at `a > 0`. -/
theorem rpow_tangent_le {a y ρ : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (hρ : 1 ≤ ρ) :
    a ^ ρ + ρ * a ^ (ρ - 1) * (y - a) ≤ y ^ ρ := by
  have hs : -1 ≤ y / a - 1 := by have := div_nonneg hy ha.le; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs hρ
  rw [add_sub_cancel, Real.div_rpow hy ha.le] at hb
  have hapos : 0 < a ^ ρ := Real.rpow_pos_of_pos ha ρ
  have h2 := mul_le_mul_of_nonneg_left hb hapos.le
  rw [mul_div_cancel₀ _ hapos.ne'] at h2
  rw [Real.rpow_sub_one ha.ne']
  calc a ^ ρ + ρ * (a ^ ρ / a) * (y - a) = a ^ ρ * (1 + ρ * (y / a - 1)) := by
        field_simp
    _ ≤ y ^ ρ := h2

/-- **Weighted Jensen**: `Z · |∫gX / Z|^ρ ≤ ∫ g|X|^ρ` for `ρ > 1`. -/
theorem jensen_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → ℝ}
    (hg0 : ∀ ω, 0 ≤ g ω) (hgi : Integrable g μ) {X : Ω → ℂ} (hXm : AEStronglyMeasurable X μ)
    (hgX : Integrable (fun ω => (g ω : ℂ) * X ω) μ) {ρ : ℝ} (hρ : 1 < ρ) :
    ENNReal.ofReal (∫ ω, g ω ∂μ) *
        ENNReal.ofReal (‖(∫ ω, (g ω : ℂ) * X ω ∂μ) / ((∫ ω, g ω ∂μ : ℝ) : ℂ)‖ ^ ρ) ≤
      ∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (‖X ω‖ ^ ρ) ∂μ := by
  set Z := ∫ ω, g ω ∂μ
  have hZ0 : 0 ≤ Z := integral_nonneg hg0
  set N := ‖∫ ω, (g ω : ℂ) * X ω ∂μ‖
  have hnm : ∀ ω, ‖(g ω : ℂ) * X ω‖ = g ω * ‖X ω‖ := fun ω => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg0 ω)]
  have hy : Integrable (fun ω => g ω * ‖X ω‖) μ :=
    hgX.norm.congr (ae_of_all _ fun ω => hnm ω)
  set Y := ∫ ω, g ω * ‖X ω‖ ∂μ
  have hNY : N ≤ Y := by
    calc N ≤ ∫ ω, ‖(g ω : ℂ) * X ω‖ ∂μ := norm_integral_le_integral_norm _
      _ = Y := integral_congr_ae (ae_of_all _ fun ω => hnm ω)
  rcases hZ0.eq_or_lt with hZ | hZ
  · rw [← hZ, ENNReal.ofReal_zero, zero_mul]; exact bot_le
  by_cases hI : (∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (‖X ω‖ ^ ρ) ∂μ) = ⊤
  · rw [hI]; exact le_top
  have hnn : ∀ ω, 0 ≤ g ω * ‖X ω‖ ^ ρ := fun ω => mul_nonneg (hg0 ω) (by positivity)
  have hpe : ∀ ω, ENNReal.ofReal (g ω * ‖X ω‖ ^ ρ) =
      ENNReal.ofReal (g ω) * ENNReal.ofReal (‖X ω‖ ^ ρ) := fun ω =>
    ENNReal.ofReal_mul (hg0 ω)
  have hφ : Integrable (fun ω => g ω * ‖X ω‖ ^ ρ) μ := by
    refine ⟨hgi.1.mul (hXm.norm.aemeasurable.pow_const ρ).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ ω, ‖g ω * ‖X ω‖ ^ ρ‖ₑ = ENNReal.ofReal (g ω) * ENNReal.ofReal (‖X ω‖ ^ ρ) :=
      fun ω => by rw [Real.enorm_eq_ofReal (hnn ω), hpe ω]
    simp_rw [this]
    exact lt_top_iff_ne_top.2 hI
  have hIeq : (∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (‖X ω‖ ^ ρ) ∂μ) =
      ENNReal.ofReal (∫ ω, g ω * ‖X ω‖ ^ ρ ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hφ (ae_of_all _ hnn)]
    simp_rw [hpe]
  rw [hIeq, ← ENNReal.ofReal_mul hZ0]
  apply ENNReal.ofReal_le_ofReal
  have hnorm : ‖(∫ ω, (g ω : ℂ) * X ω ∂μ) / (Z : ℂ)‖ = N / Z := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ0]
  rw [hnorm]
  set a := Y / Z
  have ha0 : 0 ≤ a := div_nonneg (le_trans (norm_nonneg _) hNY) hZ0
  have h1 : Z * (N / Z) ^ ρ ≤ Z * a ^ ρ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg (norm_nonneg _) hZ0)
      (div_le_div_of_nonneg_right hNY hZ0) (by linarith)) hZ0
  refine le_trans h1 ?_
  rcases ha0.eq_or_lt with ha | ha
  · rw [← ha, Real.zero_rpow (by linarith), mul_zero]
    exact integral_nonneg hnn
  set c := ρ * a ^ (ρ - 1)
  have hpt : ∀ ω, a ^ ρ * g ω + c * (g ω * ‖X ω‖) - c * a * g ω ≤ g ω * ‖X ω‖ ^ ρ := by
    intro ω
    have := mul_le_mul_of_nonneg_left (rpow_tangent_le ha (norm_nonneg (X ω)) hρ.le) (hg0 ω)
    calc a ^ ρ * g ω + c * (g ω * ‖X ω‖) - c * a * g ω =
        g ω * (a ^ ρ + ρ * a ^ (ρ - 1) * (‖X ω‖ - a)) := by simp only [c]; ring
      _ ≤ _ := this
  have hint : ∫ ω, (a ^ ρ * g ω + c * (g ω * ‖X ω‖) - c * a * g ω) ∂μ ≤
      ∫ ω, g ω * ‖X ω‖ ^ ρ ∂μ :=
    integral_mono (((hgi.const_mul (a ^ ρ)).add (hy.const_mul c)).sub
      (hgi.const_mul (c * a))) hφ hpt
  have hA : Integrable (fun ω => a ^ ρ * g ω + c * (g ω * ‖X ω‖)) μ :=
    (hgi.const_mul _).add (hy.const_mul _)
  rw [integral_sub (f := fun ω => a ^ ρ * g ω + c * (g ω * ‖X ω‖)) (g := fun ω => c * a * g ω)
    hA (hgi.const_mul _), integral_add (f := fun ω => a ^ ρ * g ω)
    (g := fun ω => c * (g ω * ‖X ω‖)) (hgi.const_mul _) (hy.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul] at hint
  have hY : Y = a * Z := by simp only [a]; field_simp
  calc Z * a ^ ρ = a ^ ρ * Z + c * Y - c * a * Z := by rw [hY]; ring
    _ ≤ _ := hint

end BlockBand.DeterminantScore.RbarMoment
