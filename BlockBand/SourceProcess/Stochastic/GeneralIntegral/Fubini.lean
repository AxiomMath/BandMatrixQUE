module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Isometry
public import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Fubini for the bracket measure; simple integrands as functions

Measure `ν_T = bracketMeasure Q α T = (dt|_{(0,T]} ⊗ Q).withDensity α` on `ℝ × Ω`.

* `lintegral_bracketMeasure`, `integral_bracketMeasure`: `∫ F dν_T = ∫_Ω ∫_{(0,T]} α F dr dQ`
  (Tonelli for measurable `F ≥ 0`; Fubini for `ν_T`-integrable `F`).
* `elemFun x = ∑ c_r 1_{(s_r,t_r] × A_r}` (pointwise representative of a simple integrand),
  `integrandLin_ae`: it represents `integrandLin h T x` `ν_T`-a.e.;
  `elemFun_restrict`: restriction to `(q₁,q₂] × C` multiplies by `1_{(q₁,q₂] × C}`.
* `bracketTerm α g t ω = ∫_{(0,t]} g(r,ω)² α_r(ω) dr`, the bracket `∫_0^t H² d⟨N⟩`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [SFinite Q]
  {α : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- The bracket `∫_{(0,t]} g(r,ω)² α_r(ω) dr`. -/
def bracketTerm (α : ℝ≥0 → Ω → ℝ) (g : ℝ × Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in Ioc (0 : ℝ) t, g (r, ω) ^ 2 * α r.toNNReal ω

/-- **Tonelli for `ν_T`.** -/
theorem lintegral_bracketMeasure (hα : Measurable fun p : ℝ × Ω => α p.1.toNNReal p.2)
    {F : ℝ × Ω → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂bracketMeasure Q α T =
      ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) T, ENNReal.ofReal (α r.toNNReal ω) * F (r, ω)) ∂Q := by
  have hm : Measurable fun p : ℝ × Ω => ENNReal.ofReal (α p.1.toNNReal p.2) :=
    ENNReal.measurable_ofReal.comp hα
  rw [bracketMeasure, lintegral_withDensity_eq_lintegral_mul _ hm hF, timeProbMeasure,
    lintegral_prod_symm _ (hm.mul hF).aemeasurable]
  rfl

/-- **Fubini for `ν_T`.** -/
theorem integral_bracketMeasure (hα : Measurable fun p : ℝ × Ω => α p.1.toNNReal p.2)
    (hα0 : ∀ t ω, 0 ≤ α t ω) {F : ℝ × Ω → ℝ} (hF : Integrable F (bracketMeasure Q α T)) :
    ∫ p, F p ∂bracketMeasure Q α T =
      ∫ ω, (∫ r in Ioc (0 : ℝ) T, α r.toNNReal ω * F (r, ω)) ∂Q := by
  have hm : Measurable fun p : ℝ × Ω => ENNReal.ofReal (α p.1.toNNReal p.2) :=
    ENNReal.measurable_ofReal.comp hα
  have hlt : ∀ᵐ p ∂timeProbMeasure T Q, ENNReal.ofReal (α p.1.toNNReal p.2) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hF' := (integrable_withDensity_iff_integrable_smul' hm hlt).1 hF
  rw [bracketMeasure, integral_withDensity_eq_integral_toReal_smul hm hlt]
  simp only [ENNReal.toReal_ofReal (hα0 _ _), smul_eq_mul] at hF' ⊢
  rw [timeProbMeasure, integral_prod_symm _ hF']

variable {𝓖 : Filtration ℝ≥0 mΩ}

/-- Pointwise representative `∑ c_r 1_r` of a simple integrand. -/
def elemFun : (Rect 𝓖 T →₀ ℝ) →ₗ[ℝ] (ℝ × Ω → ℝ) :=
  Finsupp.linearCombination ℝ fun r => r.set.indicator 1

@[simp] theorem elemFun_single (r : Rect 𝓖 T) (c : ℝ) :
    elemFun (Finsupp.single r c) = c • r.set.indicator 1 := by
  simp [elemFun]

theorem measurable_elemFun (x : Rect 𝓖 T →₀ ℝ) : Measurable (elemFun x) := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact measurable_const
  | add x y hx hy => rw [map_add]; exact hx.add hy
  | single r c => rw [elemFun_single]; exact (measurable_one.indicator r.measurableSet).const_smul c

theorem elemFun_bound (x : Rect 𝓖 T →₀ ℝ) : ∃ C, ∀ p, |elemFun x p| ≤ C := by
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨0, fun p => by simp⟩
  | add x y hx hy =>
      obtain ⟨C, hC⟩ := hx
      obtain ⟨D, hD⟩ := hy
      exact ⟨C + D, fun p => by simpa using (abs_add_le _ _).trans (add_le_add (hC p) (hD p))⟩
  | single r c =>
      refine ⟨|c|, fun p => ?_⟩
      by_cases hp : p ∈ r.set <;> simp [hp]

theorem integrandLin_ae {N : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure Q] (h : IsL2Integrator Q 𝓖 N α)
    (x : Rect 𝓖 T →₀ ℝ) :
    ((h.integrandLin T x : PredL2 𝓖 (bracketMeasure Q α T)) : ℝ × Ω → ℝ) =ᵐ[bracketMeasure Q α T]
      elemFun x := by
  have := h.isFiniteMeasure_bracketMeasure T
  induction x using Finsupp.induction_linear with
  | zero => simpa using Lp.coeFn_zero ℝ 2 (bracketMeasure Q α T)
  | add x y hx hy =>
      simp only [map_add]
      exact (Lp.coeFn_add _ _).trans (hx.add hy)
  | single r c =>
      simp only [IsL2Integrator.integrandLin, Finsupp.linearCombination_single, elemFun_single]
      refine (Lp.coeFn_smul _ _).trans (EventuallyEq.const_smul ?_ c)
      exact indicatorConstLp_coeFn (hs := r.measurableSet) (hμs := measure_ne_top _ _)

theorem elemFun_restrict {q₁ q₂ : ℝ≥0} (hq : q₁ ≤ q₂) (hqT : q₂ ≤ T) {C : Set Ω}
    (hC : MeasurableSet[𝓖 q₁] C) (x : Rect 𝓖 T →₀ ℝ) (p : ℝ × Ω) :
    elemFun (restrictLin hq hqT hC x) p =
      (Ioc (q₁ : ℝ) q₂ ×ˢ C).indicator 1 p * elemFun x p := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, mul_add]
  | single r c =>
      simp only [restrictLin, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        elemFun_single, Pi.smul_apply, smul_eq_mul, Rect.restrict_set]
      by_cases h1 : p ∈ r.set <;> by_cases h2 : p ∈ Ioc (q₁ : ℝ) q₂ ×ˢ C <;>
        simp [h1, h2, indicator_of_mem, indicator_of_notMem]

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
