module

public import BlockBand.Critical.Collar.Density.RegularBound

/-!
# Abstract two-sided expectation

Any measure space. `lintegral_two_sided_of_pointwise`: let `f ≥ 0` a.e., `Q ≥ 0` integrable and
`χ` measurable, `T` measurable with `μ T ≤ p_T`. If `|f - ρQ| ≤ k₁χQ + k₂Q` off `T` and `f ≤ GQ` on
`T`, then for all `l, l₁, l₂ > 0`, with `E Q² ≤ M₄` and `E χ² ≤ M_χ`,
`ρ E Q - (k₂ E Q + k₁(l M_χ + M₄/l)/2 + ρ(l₂ p_T + M₄/l₂)/2) ≤ E f` and
`E f ≤ ρ E Q + k₂ E Q + k₁(l M_χ + M₄/l)/2 + (l₁G²p_T + M₄/l₁)/2` (lintegral form).
The products `χQ`, `GQ 1_T`, `Q 1_T` are paid by `xy ≤ l x²/2 + y²/(2l)` with deterministic
weights, in place of Hölder (`mul_le_amgm`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory
open scoped ENNReal

theorem mul_le_amgm {x y l : ℝ} (hl : 0 < l) : x * y ≤ l * x ^ 2 / 2 + y ^ 2 / (2 * l) := by
  have h : 0 ≤ (l * x - y) ^ 2 / (2 * l) := by positivity
  have e : (l * x - y) ^ 2 / (2 * l) = l * x ^ 2 / 2 + y ^ 2 / (2 * l) - x * y := by
    field_simp; ring
  linarith

/-- **Abstract two-sided expectation** of a nonnegative `f` that is `ρQ` up to a relative error
`k₁χ + k₂` off a small exceptional set `T` and at most `GQ` on `T`; the products are paid by
`xy ≤ l x²/2 + y²/(2l)`. -/
theorem lintegral_two_sided_of_pointwise {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f Q χ : Ω → ℝ} {T : Set Ω} (hT : MeasurableSet T) (hQm : Measurable Q) (hχm : Measurable χ)
    (hQ0 : ∀ ω, 0 ≤ Q ω) (hQi : Integrable Q μ) {ρ k₁ k₂ G pT M₄ Mχ l l₁ l₂ : ℝ}
    (hρ : 0 ≤ ρ) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hpT : 0 ≤ pT) (hM₄ : 0 ≤ M₄) (hMχ : 0 ≤ Mχ)
    (hl : 0 < l) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (hgood : ∀ᵐ ω ∂μ, ω ∉ T → |f ω - ρ * Q ω| ≤ k₁ * χ ω * Q ω + k₂ * Q ω)
    (hbad : ∀ᵐ ω ∂μ, ω ∈ T → f ω ≤ G * Q ω) (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (hμT : μ T ≤ ENNReal.ofReal pT)
    (hQ2 : ∫⁻ ω, ENNReal.ofReal (Q ω ^ 2) ∂μ ≤ ENNReal.ofReal M₄)
    (hχ2 : ∫⁻ ω, ENNReal.ofReal (χ ω ^ 2) ∂μ ≤ ENNReal.ofReal Mχ) :
    ENNReal.ofReal (ρ * ∫ ω, Q ω ∂μ - (k₂ * ∫ ω, Q ω ∂μ + k₁ * (l * Mχ + M₄ / l) / 2 +
        ρ * (l₂ * pT + M₄ / l₂) / 2)) ≤ ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ∧
      ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal (ρ * ∫ ω, Q ω ∂μ + k₂ * ∫ ω, Q ω ∂μ +
        k₁ * (l * Mχ + M₄ / l) / 2 + (l₁ * G ^ 2 * pT + M₄ / l₁) / 2) := by
  set IQ := ∫ ω, Q ω ∂μ
  have hIQ : 0 ≤ IQ := integral_nonneg hQ0
  have hlQ : ∀ a : ℝ, 0 ≤ a → ∫⁻ ω, ENNReal.ofReal (a * Q ω) ∂μ = ENNReal.ofReal (a * IQ) := by
    intro a ha
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hQi.const_mul a)
      (Filter.Eventually.of_forall fun ω => mul_nonneg ha (hQ0 ω))]
  have hlQ2 : ∀ a : ℝ, 0 ≤ a → ∫⁻ ω, ENNReal.ofReal (a * Q ω ^ 2) ∂μ ≤
      ENNReal.ofReal (a * M₄) := by
    intro a ha
    have : ∀ ω, ENNReal.ofReal (a * Q ω ^ 2) = ENNReal.ofReal a * ENNReal.ofReal (Q ω ^ 2) :=
      fun ω => ENNReal.ofReal_mul ha
    simp_rw [this]
    rw [lintegral_const_mul _ (hQm.pow_const 2).ennreal_ofReal, ENNReal.ofReal_mul ha]
    gcongr
  have hlχ2 : ∀ a : ℝ, 0 ≤ a → ∫⁻ ω, ENNReal.ofReal (a * χ ω ^ 2) ∂μ ≤
      ENNReal.ofReal (a * Mχ) := by
    intro a ha
    have : ∀ ω, ENNReal.ofReal (a * χ ω ^ 2) = ENNReal.ofReal a * ENNReal.ofReal (χ ω ^ 2) :=
      fun ω => ENNReal.ofReal_mul ha
    simp_rw [this]
    rw [lintegral_const_mul _ (hχm.pow_const 2).ennreal_ofReal, ENNReal.ofReal_mul ha]
    gcongr
  have hlT : ∀ a : ℝ, 0 ≤ a → ∫⁻ ω, T.indicator (fun _ => ENNReal.ofReal a) ω ∂μ ≤
      ENNReal.ofReal (a * pT) := by
    intro a ha
    rw [lintegral_indicator_const hT, ENNReal.ofReal_mul ha]
    gcongr
  have mQ : ∀ a : ℝ, Measurable fun ω => ENNReal.ofReal (a * Q ω) := fun a =>
    (measurable_const.mul hQm).ennreal_ofReal
  have mQ2 : ∀ a : ℝ, Measurable fun ω => ENNReal.ofReal (a * Q ω ^ 2) := fun a =>
    (measurable_const.mul (hQm.pow_const 2)).ennreal_ofReal
  have mχ2 : ∀ a : ℝ, Measurable fun ω => ENNReal.ofReal (a * χ ω ^ 2) := fun a =>
    (measurable_const.mul (hχm.pow_const 2)).ennreal_ofReal
  have mT : ∀ a : ℝ, Measurable fun ω => T.indicator (fun _ => ENNReal.ofReal a) ω := fun a =>
    measurable_const.indicator hT
  -- the common error terms
  set E : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (k₂ * Q ω) + ENNReal.ofReal (k₁ * l / 2 * χ ω ^ 2) +
    ENNReal.ofReal (k₁ / (2 * l) * Q ω ^ 2) with hE
  have mE1 : Measurable fun ω => ENNReal.ofReal (k₂ * Q ω) +
      ENNReal.ofReal (k₁ * l / 2 * χ ω ^ 2) := (mQ _).add (mχ2 _)
  have mE : Measurable E := mE1.add (mQ2 _)
  have hgoodE : ∀ ω, |f ω - ρ * Q ω| ≤ k₁ * χ ω * Q ω + k₂ * Q ω →
      |f ω - ρ * Q ω| ≤ k₂ * Q ω + k₁ * l / 2 * χ ω ^ 2 + k₁ / (2 * l) * Q ω ^ 2 := by
    intro ω h
    have := mul_le_amgm (x := χ ω) (y := Q ω) hl
    have h2 : k₁ * (χ ω * Q ω) ≤ k₁ * (l * χ ω ^ 2 / 2 + Q ω ^ 2 / (2 * l)) :=
      mul_le_mul_of_nonneg_left this hk₁
    have e1 : k₁ * (l * χ ω ^ 2 / 2 + Q ω ^ 2 / (2 * l)) =
        k₁ * l / 2 * χ ω ^ 2 + k₁ / (2 * l) * Q ω ^ 2 := by ring
    nlinarith
  have hEsum : ∀ ω, ENNReal.ofReal (k₂ * Q ω + k₁ * l / 2 * χ ω ^ 2 + k₁ / (2 * l) * Q ω ^ 2) ≤
      E ω := fun ω => by
    refine (ENNReal.ofReal_add_le).trans ?_
    exact add_le_add_left ENNReal.ofReal_add_le _
  have hIE : ∫⁻ ω, E ω ∂μ ≤ ENNReal.ofReal (k₂ * IQ + k₁ * (l * Mχ + M₄ / l) / 2) := by
    simp only [hE]
    rw [lintegral_add_left mE1, lintegral_add_left (mQ _), hlQ _ hk₂]
    have h1 := hlχ2 (k₁ * l / 2) (by positivity)
    have h2 := hlQ2 (k₁ / (2 * l)) (by positivity)
    calc ENNReal.ofReal (k₂ * IQ) + ∫⁻ ω, ENNReal.ofReal (k₁ * l / 2 * χ ω ^ 2) ∂μ +
          ∫⁻ ω, ENNReal.ofReal (k₁ / (2 * l) * Q ω ^ 2) ∂μ
        ≤ ENNReal.ofReal (k₂ * IQ) + ENNReal.ofReal (k₁ * l / 2 * Mχ) +
            ENNReal.ofReal (k₁ / (2 * l) * M₄) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring
  constructor
  · -- lower bound
    set E' : Ω → ℝ≥0∞ := fun ω => E ω + T.indicator (fun _ => ENNReal.ofReal (ρ * l₂ / 2)) ω +
      ENNReal.ofReal (ρ / (2 * l₂) * Q ω ^ 2) with hE'
    have mE'1 : Measurable fun ω => E ω + T.indicator (fun _ => ENNReal.ofReal (ρ * l₂ / 2)) ω :=
      mE.add (mT _)
    have mE' : Measurable E' := mE'1.add (mQ2 _)
    have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal (ρ * Q ω) ≤ ENNReal.ofReal (f ω) + E' ω := by
      filter_upwards [hgood, hbad, hf0] with ω hg _ hf
      by_cases hω : ω ∈ T
      · have h1 : ρ * Q ω ≤ ρ * l₂ / 2 + ρ / (2 * l₂) * Q ω ^ 2 := by
          have := mul_le_amgm (x := 1) (y := Q ω) hl₂
          have h := mul_le_mul_of_nonneg_left this hρ
          have e1 : ρ * (l₂ * 1 ^ 2 / 2 + Q ω ^ 2 / (2 * l₂)) =
              ρ * l₂ / 2 + ρ / (2 * l₂) * Q ω ^ 2 := by ring
          nlinarith
        calc ENNReal.ofReal (ρ * Q ω) ≤ ENNReal.ofReal (ρ * l₂ / 2 + ρ / (2 * l₂) * Q ω ^ 2) :=
              ENNReal.ofReal_le_ofReal h1
          _ ≤ ENNReal.ofReal (ρ * l₂ / 2) + ENNReal.ofReal (ρ / (2 * l₂) * Q ω ^ 2) :=
              ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal (f ω) + E' ω := by
              simp only [hE']
              rw [Set.indicator_of_mem hω]
              calc ENNReal.ofReal (ρ * l₂ / 2) + ENNReal.ofReal (ρ / (2 * l₂) * Q ω ^ 2)
                  ≤ (ENNReal.ofReal (f ω) + E ω) + ENNReal.ofReal (ρ * l₂ / 2) +
                      ENNReal.ofReal (ρ / (2 * l₂) * Q ω ^ 2) := by
                    gcongr; exact le_add_self
                _ = _ := by ring
      · have h := hgoodE ω (hg hω)
        have h1 : ρ * Q ω ≤ f ω + (k₂ * Q ω + k₁ * l / 2 * χ ω ^ 2 + k₁ / (2 * l) * Q ω ^ 2) := by
          linarith [neg_abs_le (f ω - ρ * Q ω)]
        calc ENNReal.ofReal (ρ * Q ω) ≤ ENNReal.ofReal (f ω) +
              ENNReal.ofReal (k₂ * Q ω + k₁ * l / 2 * χ ω ^ 2 + k₁ / (2 * l) * Q ω ^ 2) :=
            (ENNReal.ofReal_le_ofReal h1).trans ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal (f ω) + E ω := by gcongr; exact hEsum ω
          _ ≤ _ := by
                gcongr
                simp only [hE']
                exact le_add_right le_self_add
    have hint := lintegral_mono_ae hpt
    rw [lintegral_add_right _ mE', hlQ _ hρ] at hint
    have hIE' : ∫⁻ ω, E' ω ∂μ ≤ ENNReal.ofReal (k₂ * IQ + k₁ * (l * Mχ + M₄ / l) / 2 +
        ρ * (l₂ * pT + M₄ / l₂) / 2) := by
      simp only [hE']
      rw [lintegral_add_left mE'1, lintegral_add_left mE]
      calc ∫⁻ ω, E ω ∂μ + ∫⁻ ω, T.indicator (fun _ => ENNReal.ofReal (ρ * l₂ / 2)) ω ∂μ +
            ∫⁻ ω, ENNReal.ofReal (ρ / (2 * l₂) * Q ω ^ 2) ∂μ
          ≤ ENNReal.ofReal (k₂ * IQ + k₁ * (l * Mχ + M₄ / l) / 2) +
              ENNReal.ofReal (ρ * l₂ / 2 * pT) + ENNReal.ofReal (ρ / (2 * l₂) * M₄) := by
            gcongr
            · exact hlT _ (by positivity)
            · exact hlQ2 _ (by positivity)
        _ = _ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            field_simp
            ring
    have h2 : ENNReal.ofReal (ρ * IQ) ≤ ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ +
        ENNReal.ofReal (k₂ * IQ + k₁ * (l * Mχ + M₄ / l) / 2 +
          ρ * (l₂ * pT + M₄ / l₂) / 2) := hint.trans (by gcongr)
    rw [ENNReal.ofReal_sub _ (by positivity)]
    exact tsub_le_iff_right.2 h2
  · -- upper bound
    set E' : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (ρ * Q ω) + E ω +
      T.indicator (fun _ => ENNReal.ofReal (l₁ * G ^ 2 / 2)) ω +
        ENNReal.ofReal (1 / (2 * l₁) * Q ω ^ 2) with hE'
    have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal (f ω) ≤ E' ω := by
      filter_upwards [hgood, hbad] with ω hg hb
      by_cases hω : ω ∈ T
      · have h1 : f ω ≤ l₁ * G ^ 2 / 2 + 1 / (2 * l₁) * Q ω ^ 2 := by
          have := mul_le_amgm (x := G) (y := Q ω) hl₁
          have e1 : Q ω ^ 2 / (2 * l₁) = 1 / (2 * l₁) * Q ω ^ 2 := by ring
          linarith [hb hω]
        calc ENNReal.ofReal (f ω) ≤ ENNReal.ofReal (l₁ * G ^ 2 / 2) +
              ENNReal.ofReal (1 / (2 * l₁) * Q ω ^ 2) :=
            (ENNReal.ofReal_le_ofReal h1).trans ENNReal.ofReal_add_le
          _ ≤ E' ω := by
              simp only [hE']
              rw [Set.indicator_of_mem hω]
              gcongr
              exact le_add_self
      · have h := hgoodE ω (hg hω)
        have h1 : f ω ≤ ρ * Q ω + (k₂ * Q ω + k₁ * l / 2 * χ ω ^ 2 + k₁ / (2 * l) * Q ω ^ 2) := by
          linarith [le_abs_self (f ω - ρ * Q ω)]
        calc ENNReal.ofReal (f ω) ≤ ENNReal.ofReal (ρ * Q ω) +
              ENNReal.ofReal (k₂ * Q ω + k₁ * l / 2 * χ ω ^ 2 + k₁ / (2 * l) * Q ω ^ 2) :=
            (ENNReal.ofReal_le_ofReal h1).trans ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal (ρ * Q ω) + E ω := by gcongr; exact hEsum ω
          _ ≤ E' ω := by
              simp only [hE']
              rw [add_assoc, add_assoc]
              gcongr
              exact le_self_add
    refine (lintegral_mono_ae hpt).trans ?_
    have m1 : Measurable fun ω => ENNReal.ofReal (ρ * Q ω) + E ω := (mQ _).add mE
    have m2 : Measurable fun ω => ENNReal.ofReal (ρ * Q ω) + E ω +
        T.indicator (fun _ => ENNReal.ofReal (l₁ * G ^ 2 / 2)) ω := m1.add (mT _)
    simp only [hE']
    rw [lintegral_add_left m2, lintegral_add_left m1, lintegral_add_left (mQ _), hlQ _ hρ]
    calc ENNReal.ofReal (ρ * IQ) + ∫⁻ ω, E ω ∂μ +
          ∫⁻ ω, T.indicator (fun _ => ENNReal.ofReal (l₁ * G ^ 2 / 2)) ω ∂μ +
          ∫⁻ ω, ENNReal.ofReal (1 / (2 * l₁) * Q ω ^ 2) ∂μ
        ≤ ENNReal.ofReal (ρ * IQ) + ENNReal.ofReal (k₂ * IQ + k₁ * (l * Mχ + M₄ / l) / 2) +
            ENNReal.ofReal (l₁ * G ^ 2 / 2 * pT) + ENNReal.ofReal (1 / (2 * l₁) * M₄) := by
          gcongr
          · exact hlT _ (by positivity)
          · exact hlQ2 _ (by positivity)
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
          ring

end BlockBand.Critical.Collar.Density
