module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Fubini
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# `L¹` estimates for the bracket term

Measure `ν_T = α ds ⊗ Q` on `(0,T] × Ω` (`Q` s-finite, `α ≥ 0` jointly measurable).

* `eLpNorm_sq_sub_sq_le`: `‖f₁² - f₂²‖_{L¹} ≤ ‖f₁ - f₂‖_{L²} ‖f₁ + f₂‖_{L²}` (any measure).
* `lintegral_enorm_partial_le`: `E|∫_{(0,t]} F α dr| ≤ ∫ |F| dν_T` for `t ≤ T`.
* `ae_integrableOn_sq`: `f ∈ L²(ν_T)` ⇒ a.s. `r ↦ f(r,ω)² α_r` is integrable on `(0,T]`.
* `bracketTerm_ae_eq_of_ae_eq`: the bracket term only depends on the `ν_T`-class.
* `lintegral_enorm_bracketTerm_sub_le`:
  `E|∫_0^t f₁² α - ∫_0^t f₂² α| ≤ ∫ |f₁² - f₂²| dν_T` for `f₁, f₂ ∈ L²(ν_T)`, `t ≤ T`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

theorem stronglyMeasurable_bracketTerm' {Ω : Type*} [MeasurableSpace Ω] {α : ℝ≥0 → Ω → ℝ}
    (hα : Measurable fun p : ℝ × Ω => α p.1.toNNReal p.2)
    {f : ℝ × Ω → ℝ} (hf : StronglyMeasurable f) (t : ℝ≥0) :
    StronglyMeasurable (bracketTerm α f t) :=
  ((hf.pow 2).mul hα.stronglyMeasurable).integral_prod_left'
    (μ := volume.restrict (Ioc (0 : ℝ) t))

theorem eLpNorm_sq_sub_sq_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {f₁ f₂ : X → ℝ}
    (h1 : AEStronglyMeasurable f₁ μ) (h2 : AEStronglyMeasurable f₂ μ) :
    eLpNorm (fun x => f₁ x ^ 2 - f₂ x ^ 2) 1 μ ≤
      eLpNorm (fun x => f₁ x - f₂ x) 2 μ * eLpNorm (fun x => f₁ x + f₂ x) 2 μ := by
  have := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) (h1.sub h2) (h1.add h2)
  convert this using 2
  funext x
  change f₁ x ^ 2 - f₂ x ^ 2 = (f₁ x - f₂ x) * (f₁ x + f₂ x)
  ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [SFinite Q]
  {α : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

theorem lintegral_enorm_partial_le (hα : Measurable fun p : ℝ × Ω => α p.1.toNNReal p.2)
    (hα0 : ∀ t ω, 0 ≤ α t ω) {F : ℝ × Ω → ℝ} (hF : StronglyMeasurable F) {t : ℝ≥0}
    (htT : t ≤ T) :
    ∫⁻ ω, ‖∫ r in Ioc (0 : ℝ) t, F (r, ω) * α r.toNNReal ω‖ₑ ∂Q ≤
      ∫⁻ p, ‖F p‖ₑ ∂bracketMeasure Q α T := by
  rw [lintegral_bracketMeasure hα hF.measurable.enorm]
  refine lintegral_mono fun ω => ?_
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine (lintegral_mono_set (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 htT))).trans ?_
  refine le_of_eq (lintegral_congr fun r => ?_)
  rw [enorm_mul, Real.enorm_of_nonneg (hα0 _ _), mul_comm]

theorem ae_integrableOn_sq (hα : Measurable fun p : ℝ × Ω => α p.1.toNNReal p.2)
    (hα0 : ∀ t ω, 0 ≤ α t ω) {f : ℝ × Ω → ℝ} (hf : StronglyMeasurable f)
    (hfin : ∫⁻ p, ‖f p‖ₑ ^ 2 ∂bracketMeasure Q α T ≠ ∞) :
    ∀ᵐ ω ∂Q, IntegrableOn (fun r : ℝ => f (r, ω) ^ 2 * α r.toNNReal ω) (Ioc 0 T) := by
  have hm : Measurable fun p : ℝ × Ω => ENNReal.ofReal (α p.1.toNNReal p.2) * ‖f p‖ₑ ^ 2 :=
    (ENNReal.measurable_ofReal.comp hα).mul (hf.measurable.enorm.pow_const 2)
  rw [lintegral_bracketMeasure hα (hf.measurable.enorm.pow_const 2)] at hfin
  have hae := ae_lt_top' (hm.lintegral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) T))).aemeasurable
    hfin
  filter_upwards [hae] with ω hω
  refine ⟨((hf.comp_measurable (measurable_id.prodMk measurable_const)).pow 2).mul
    (hα.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable
    |>.aestronglyMeasurable, ?_⟩
  change ∫⁻ r in Ioc (0 : ℝ) T, ‖f (r, ω) ^ 2 * α r.toNNReal ω‖ₑ < ∞
  convert hω using 2
  funext r
  rw [enorm_mul, Real.enorm_of_nonneg (hα0 _ _), enorm_pow, mul_comm]

theorem lintegral_enorm_bracketTerm_sub_le
    (hα : Measurable fun p : ℝ × Ω => α p.1.toNNReal p.2) (hα0 : ∀ t ω, 0 ≤ α t ω)
    {f₁ f₂ : ℝ × Ω → ℝ} (hf₁ : StronglyMeasurable f₁) (hf₂ : StronglyMeasurable f₂)
    (hfin₁ : ∫⁻ p, ‖f₁ p‖ₑ ^ 2 ∂bracketMeasure Q α T ≠ ∞)
    (hfin₂ : ∫⁻ p, ‖f₂ p‖ₑ ^ 2 ∂bracketMeasure Q α T ≠ ∞) {t : ℝ≥0} (htT : t ≤ T) :
    ∫⁻ ω, ‖bracketTerm α f₁ t ω - bracketTerm α f₂ t ω‖ₑ ∂Q ≤
      ∫⁻ p, ‖f₁ p ^ 2 - f₂ p ^ 2‖ₑ ∂bracketMeasure Q α T := by
  have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 T := Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 htT)
  calc _ = ∫⁻ ω, ‖∫ r in Ioc (0 : ℝ) t, (f₁ (r, ω) ^ 2 - f₂ (r, ω) ^ 2) * α r.toNNReal ω‖ₑ ∂Q := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_integrableOn_sq hα hα0 hf₁ hfin₁, ae_integrableOn_sq hα hα0 hf₂ hfin₂]
          with ω h1 h2
        rw [bracketTerm, bracketTerm, ← integral_sub (h1.mono_set hsub) (h2.mono_set hsub)]
        simp_rw [sub_mul]
    _ ≤ _ := lintegral_enorm_partial_le hα hα0 ((hf₁.pow 2).sub (hf₂.pow 2)) htT

theorem lintegral_enorm_bracketTerm_le
    (hα : Measurable fun p : ℝ × Ω => α p.1.toNNReal p.2) (hα0 : ∀ t ω, 0 ≤ α t ω)
    {f : ℝ × Ω → ℝ} (hf : StronglyMeasurable f) {t : ℝ≥0} (htT : t ≤ T) :
    ∫⁻ ω, ‖bracketTerm α f t ω‖ₑ ∂Q ≤ ∫⁻ p, ‖f p‖ₑ ^ 2 ∂bracketMeasure Q α T := by
  refine (lintegral_enorm_partial_le hα hα0 (hf.pow 2) htT).trans (le_of_eq ?_)
  exact lintegral_congr fun p => enorm_pow _ _

/-- The bracket term depends only on the `ν_T`-class of the integrand (up to `Q`-null sets). -/
theorem bracketTerm_ae_eq_of_ae_eq (hα : Measurable fun p : ℝ × Ω => α p.1.toNNReal p.2)
    (hα0 : ∀ t ω, 0 ≤ α t ω) {f₁ f₂ : ℝ × Ω → ℝ} (hf₁ : StronglyMeasurable f₁)
    (hf₂ : StronglyMeasurable f₂) (hfin₁ : ∫⁻ p, ‖f₁ p‖ₑ ^ 2 ∂bracketMeasure Q α T ≠ ∞)
    (hfin₂ : ∫⁻ p, ‖f₂ p‖ₑ ^ 2 ∂bracketMeasure Q α T ≠ ∞)
    (hfg : f₁ =ᵐ[bracketMeasure Q α T] f₂) {t : ℝ≥0} (htT : t ≤ T) :
    bracketTerm α f₁ t =ᵐ[Q] bracketTerm α f₂ t := by
  have h0 : ∫⁻ p, ‖f₁ p ^ 2 - f₂ p ^ 2‖ₑ ∂bracketMeasure Q α T = 0 := by
    have : (fun p => ‖f₁ p ^ 2 - f₂ p ^ 2‖ₑ) =ᵐ[bracketMeasure Q α T] fun _ => 0 :=
      hfg.mono fun p hp => by simp only [hp, sub_self, enorm_zero]
    rw [lintegral_congr_ae this, lintegral_zero]
  have h1 : ∫⁻ ω, ‖bracketTerm α f₁ t ω - bracketTerm α f₂ t ω‖ₑ ∂Q = 0 :=
    le_antisymm ((lintegral_enorm_bracketTerm_sub_le hα hα0 hf₁ hf₂ hfin₁ hfin₂ htT).trans
      h0.le) zero_le
  have hm : Measurable fun ω => ‖bracketTerm α f₁ t ω - bracketTerm α f₂ t ω‖ₑ :=
    ((stronglyMeasurable_bracketTerm' hα hf₁ t).sub
      (stronglyMeasurable_bracketTerm' hα hf₂ t)).measurable.enorm
  filter_upwards [(lintegral_eq_zero_iff hm).1 h1] with ω hω
  simpa [sub_eq_zero] using hω

theorem stronglyMeasurable_bracketTerm (hα : Measurable fun p : ℝ × Ω => α p.1.toNNReal p.2)
    {f : ℝ × Ω → ℝ} (hf : StronglyMeasurable f) (t : ℝ≥0) :
    StronglyMeasurable (bracketTerm α f t) :=
  stronglyMeasurable_bracketTerm' hα hf t

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
