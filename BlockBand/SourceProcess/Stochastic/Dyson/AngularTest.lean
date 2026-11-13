module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularOS
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Tools

/-!
# Martingale identities against bounded test functions (real and complex)

Generic tools for the conditional angular martingale problem clause of `DysonBrownianMotion`.

`TestMart Q 𝓕 X`: `X_t` integrable and `E[η X_t] = E[η X_r]` for `r ≤ t` and bounded
`𝓕_r`-strongly measurable real `η`; `TestMartC` is the complex analogue. Martingale
modifications give `TestMart` (`testMart_of_hasMM`); linear combinations and the passage
`X + i Y` to complex test functions are recorded (`testMartC_of_re_im`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- Real martingale identity against bounded test functions. -/
def TestMart (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t, Integrable (X t) Q) ∧ ∀ r t, r ≤ t → ∀ η : Ω → ℝ, StronglyMeasurable[𝓕 r] η →
    ∀ C, (∀ᵐ ω ∂Q, ‖η ω‖ ≤ C) → ∫ ω, η ω * X t ω ∂Q = ∫ ω, η ω * X r ω ∂Q

/-- Complex martingale identity against bounded test functions. -/
def TestMartC (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℂ) : Prop :=
  (∀ t, Integrable (X t) Q) ∧ ∀ r t, r ≤ t → ∀ ζ : Ω → ℂ, StronglyMeasurable[𝓕 r] ζ →
    ∀ C, (∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) → ∫ ω, ζ ω * X t ω ∂Q = ∫ ω, ζ ω * X r ω ∂Q

theorem testMart_of_hasMM {X : ℝ≥0 → Ω → ℝ} (h : HasMartingaleModification Q 𝓕 X) :
    TestMart Q 𝓕 X := by
  obtain ⟨M, hM, hMX⟩ := h
  refine ⟨fun t => (hM.integrable t).congr (hMX t), fun r t hrt η hη C hC => ?_⟩
  have := Semimartingale.martingale_integral_mul_sub_eq_zero hM hrt hη.aestronglyMeasurable hC
  have hi : ∀ s, Integrable (fun ω => η ω * M s ω) Q := fun s =>
    (hM.integrable s).bdd_mul (hη.mono (𝓕.le r)).aestronglyMeasurable hC
  simp_rw [mul_sub] at this
  rw [integral_sub (hi t) (hi r), sub_eq_zero] at this
  have h1 : ∀ s, ∫ ω, η ω * X s ω ∂Q = ∫ ω, η ω * M s ω ∂Q := fun s =>
    integral_congr_ae ((hMX s).mono fun ω h => by simp only; rw [h])
  rw [h1, h1]; exact this

omit [IsProbabilityMeasure Q] in
theorem TestMart.add {X Y : ℝ≥0 → Ω → ℝ} (hX : TestMart Q 𝓕 X) (hY : TestMart Q 𝓕 Y) :
    TestMart Q 𝓕 (fun t ω => X t ω + Y t ω) := by
  refine ⟨fun t => (hX.1 t).add (hY.1 t), fun r t hrt η hη C hC => ?_⟩
  have hi : ∀ (Z : ℝ≥0 → Ω → ℝ), TestMart Q 𝓕 Z → ∀ s,
      Integrable (fun ω => η ω * Z s ω) Q := fun Z hZ s =>
    (hZ.1 s).bdd_mul (hη.mono (𝓕.le r)).aestronglyMeasurable hC
  simp_rw [mul_add]
  rw [integral_add (hi X hX t) (hi Y hY t), integral_add (hi X hX r) (hi Y hY r),
    hX.2 r t hrt η hη C hC, hY.2 r t hrt η hη C hC]

theorem re_im_strongly {r : ℝ≥0} {ζ : Ω → ℂ} (hζ : StronglyMeasurable[𝓕 r] ζ) :
    StronglyMeasurable[𝓕 r] (fun ω => (ζ ω).re) ∧ StronglyMeasurable[𝓕 r] (fun ω => (ζ ω).im) :=
  ⟨Complex.continuous_re.comp_stronglyMeasurable hζ,
    Complex.continuous_im.comp_stronglyMeasurable hζ⟩

omit [IsProbabilityMeasure Q] in
theorem integral_ofReal_add_mul_I {u v : Ω → ℝ} (hu : Integrable u Q) (hv : Integrable v Q) :
    ∫ ω, ((u ω : ℂ) + (v ω : ℂ) * I) ∂Q = ((∫ ω, u ω ∂Q : ℝ) : ℂ) + ((∫ ω, v ω ∂Q : ℝ) : ℂ) * I := by
  have h1 : Integrable (fun ω => (u ω : ℂ)) Q := hu.ofReal
  have h2 : Integrable (fun ω => (v ω : ℂ) * I) Q := hv.ofReal.mul_const I
  rw [integral_add h1 h2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]

omit [IsProbabilityMeasure Q] in
/-- **From real and imaginary parts to complex test functions.** -/
theorem testMartC_of_re_im {X Y : ℝ≥0 → Ω → ℝ} (hX : TestMart Q 𝓕 X) (hY : TestMart Q 𝓕 Y) :
    TestMartC Q 𝓕 (fun t ω => (X t ω : ℂ) + (Y t ω : ℂ) * I) := by
  refine ⟨fun t => (hX.1 t).ofReal.add ((hY.1 t).ofReal.mul_const I),
    fun r t hrt ζ hζ C hC => ?_⟩
  obtain ⟨ha, hb⟩ := re_im_strongly hζ
  have hCa : ∀ᵐ ω ∂Q, ‖(ζ ω).re‖ ≤ C := hC.mono fun ω h =>
    (Complex.abs_re_le_norm _).trans h
  have hCb : ∀ᵐ ω ∂Q, ‖(ζ ω).im‖ ≤ C := hC.mono fun ω h =>
    (Complex.abs_im_le_norm _).trans h
  have hi : ∀ (Z : ℝ≥0 → Ω → ℝ), TestMart Q 𝓕 Z → ∀ s (g : Ω → ℝ),
      StronglyMeasurable[𝓕 r] g → (∀ᵐ ω ∂Q, ‖g ω‖ ≤ C) →
      Integrable (fun ω => g ω * Z s ω) Q := fun Z hZ s g hg hgC =>
    (hZ.1 s).bdd_mul (hg.mono (𝓕.le r)).aestronglyMeasurable hgC
  have e : ∀ s ω, ζ ω * ((X s ω : ℂ) + (Y s ω : ℂ) * I) =
      (((ζ ω).re * X s ω - (ζ ω).im * Y s ω : ℝ) : ℂ) +
        (((ζ ω).re * Y s ω + (ζ ω).im * X s ω : ℝ) : ℂ) * I := fun s ω => by
    conv_lhs => rw [← Complex.re_add_im (ζ ω)]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  simp_rw [e]
  have hu : ∀ s, Integrable (fun ω => (ζ ω).re * X s ω - (ζ ω).im * Y s ω) Q := fun s =>
    (hi X hX s _ ha hCa).sub (hi Y hY s _ hb hCb)
  have hv : ∀ s, Integrable (fun ω => (ζ ω).re * Y s ω + (ζ ω).im * X s ω) Q := fun s =>
    (hi Y hY s _ ha hCa).add (hi X hX s _ hb hCb)
  rw [integral_ofReal_add_mul_I (hu t) (hv t), integral_ofReal_add_mul_I (hu r) (hv r)]
  rw [integral_sub (hi X hX t _ ha hCa) (hi Y hY t _ hb hCb),
    integral_sub (hi X hX r _ ha hCa) (hi Y hY r _ hb hCb),
    integral_add (hi Y hY t _ ha hCa) (hi X hX t _ hb hCb),
    integral_add (hi Y hY r _ ha hCa) (hi X hX r _ hb hCb),
    hX.2 r t hrt _ ha C hCa, hX.2 r t hrt _ hb C hCb, hY.2 r t hrt _ ha C hCa,
    hY.2 r t hrt _ hb C hCb]

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
