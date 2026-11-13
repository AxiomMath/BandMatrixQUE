module

public import BlockBand.Critical.Herglotz.Kernel
public import BlockBand.Critical.Herglotz.Atomic
public import BlockBand.Critical.Collar.DilationVariance.CauchyPoissonBounded
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Bounded analytic means of `exp(i t v^*F v)` and the Cauchy characteristic function

* `integrable_standardCauchyWeight` — the standard Cauchy density is Lebesgue integrable.
* `integral_standardCauchyWeight_smul_affine_eq_of_analyticAt` — for `G : ℂ → E` analytic and
  bounded on the open upper half-plane and continuous at a.e. real point (here: off a finite set),
  `∫ (1/(π(1+u²))) G(Re z + Im z · u) du = G z` for `Im z > 0`.
* `integral_standardCauchyWeight_smul_cexp_seval` — **Poisson representation of the bounded
  analytic exponential** of a scalar finite atomic Herglotz function `q` (`q = v^*F_N v`,
  `AtomicHerglotz.quadForm_eq_seval`): for `t ≥ 0` and `Im z > 0`,
  `e^{itq(z)} = ∫ (1/(π(1+u²))) e^{itq(Re z + Im z · u)} du`. Boundary values are taken at real
  points; the finitely many poles form a Lebesgue-null set, so the convention there is
  irrelevant.
* `integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul_scale` — the Mathlib law
  `cauchyMeasure x₀ γ` (density `γ/(π((x-x₀)²+γ²))`) is the image of the standard one under
  `u ↦ x₀ + γu`.
* `integral_cexp_cauchyMeasure` and `charFun_cauchyMeasure` — the characteristic function of the
  real Cauchy law of center `0` and scale `γ`: `E e^{itX} = e^{-γ|t|}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Complex MeasureTheory Filter
open scoped Topology NNReal

namespace BlockBand.Critical.Herglotz

open CoareaNative.BlockBand (standardCauchyWeight integral_standardCauchyWeight)
open BlockBand.Critical.Collar (integral_standardCauchyWeight_smul_eq_of_analyticAt)

theorem standardCauchyWeight_eq (u : ℝ) :
    standardCauchyWeight u = Real.pi⁻¹ * (1 + u ^ 2)⁻¹ := by
  unfold standardCauchyWeight
  rw [one_div, mul_inv]

theorem standardCauchyWeight_nonneg (u : ℝ) : 0 ≤ standardCauchyWeight u := by
  rw [standardCauchyWeight_eq]; positivity

/-- The standard Cauchy density is Lebesgue integrable. -/
theorem integrable_standardCauchyWeight : Integrable standardCauchyWeight := by
  have : standardCauchyWeight = fun u : ℝ => Real.pi⁻¹ * (1 + u ^ 2)⁻¹ := by
    funext u; exact standardCauchyWeight_eq u
  rw [this]
  exact integrable_inv_one_add_sq.const_mul _

theorem continuous_standardCauchyWeight : Continuous standardCauchyWeight := by
  have : standardCauchyWeight = fun u : ℝ => Real.pi⁻¹ * (1 + u ^ 2)⁻¹ := by
    funext u; exact standardCauchyWeight_eq u
  rw [this]
  have hc : Continuous fun u : ℝ => 1 + u ^ 2 := by fun_prop
  exact continuous_const.mul (hc.inv₀ fun u => ne_of_gt (by positivity))

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Cauchy–Poisson formula at a general point, with boundary values a.e.** Domain:
`G : ℂ → E` (complex Banach space) analytic at every point of the open upper half-plane,
bounded there by `M`, and continuous within the closed upper half-plane at every real point
outside a finite set `S`. For `Im z > 0`,
`∫ u, (1/(π(1+u²))) • G(Re z + Im z · u) = G z`.
In Poisson form: integration of the boundary values against the Cauchy law of center `Re z` and
scale `Im z`. -/
theorem integral_standardCauchyWeight_smul_affine_eq_of_analyticAt (G : ℂ → E)
    (hG : ∀ w : ℂ, 0 < w.im → AnalyticAt ℂ G w) (M : ℝ) (hM : ∀ w : ℂ, 0 < w.im → ‖G w‖ ≤ M)
    (S : Finset ℝ)
    (hbd : ∀ x : ℝ, x ∉ S → Tendsto G (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ)) (𝓝 (G x)))
    {z : ℂ} (hz : 0 < z.im) :
    (∫ u : ℝ, standardCauchyWeight u • G ((z.re + z.im * u : ℝ) : ℂ)) = G z := by
  -- shifted functions `G_ε(w) = G(Re z + Im z · w + iε)`, analytic on the closed half-plane
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let A : ℕ → ℂ → ℂ := fun n w => (z.re : ℂ) + (z.im : ℂ) * w + (ε n : ℂ) * I
  have hAim : ∀ n w, 0 ≤ w.im → 0 < (A n w).im := by
    intro n w hw
    simp only [A, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, zero_add,
      mul_one, add_zero]
    have := hε n
    nlinarith
  have hmean : ∀ n, (∫ u : ℝ, standardCauchyWeight u • G (A n u)) = G (A n I) := by
    intro n
    refine integral_standardCauchyWeight_smul_eq_of_analyticAt (fun w => G (A n w)) ?_ M ?_
    · intro w hw
      have hA : AnalyticAt ℂ (A n) w := by
        simp only [A]
        fun_prop
      exact (hG _ (hAim n w hw)).comp hA
    · intro w hw
      exact hM _ (hAim n w hw)
  -- left side: dominated convergence
  have hleft : Tendsto (fun n => ∫ u : ℝ, standardCauchyWeight u • G (A n u)) atTop
      (𝓝 (∫ u : ℝ, standardCauchyWeight u • G ((z.re + z.im * u : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence (fun u => standardCauchyWeight u * M)
      ?_ ?_ ?_ ?_
    · intro n
      have hc : Continuous fun u : ℝ => G (A n u) := by
        have : ∀ u : ℝ, ContinuousAt (fun u : ℝ => G (A n u)) u := by
          intro u
          have hu : 0 < (A n u).im := hAim n u (by simp)
          have h1 : ContinuousAt G (A n u) := (hG _ hu).continuousAt
          have h2 : Continuous fun u : ℝ => A n u := by simp only [A]; fun_prop
          exact h1.comp_of_eq h2.continuousAt rfl
        exact continuous_iff_continuousAt.mpr this
      exact (continuous_standardCauchyWeight.smul hc).aestronglyMeasurable
    · exact integrable_standardCauchyWeight.mul_const M
    · intro n
      refine Eventually.of_forall fun u => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (standardCauchyWeight_nonneg u)]
      exact mul_le_mul_of_nonneg_left (hM _ (hAim n u (by simp)))
        (standardCauchyWeight_nonneg u)
    · -- bad set: the finitely many `u` with `Re z + Im z · u ∈ S`
      have hae : ∀ᵐ u : ℝ, ∀ x ∈ S, u ≠ (x - z.re) / z.im := by
        rw [Filter.eventually_all_finset]
        intro x _
        exact Measure.ae_ne volume _
      filter_upwards [hae] with u hu
      have hxS : (z.re + z.im * u) ∉ S := by
        intro hmem
        apply hu _ hmem
        field_simp
        ring
      have hlim := hbd _ hxS
      refine Tendsto.const_smul (hlim.comp ?_) _
      -- `A n u → Re z + Im z · u` inside the open upper half-plane
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => hAim n u (by simp)⟩
      have : (fun n => A n u) = fun n => (((z.re + z.im * u : ℝ) : ℂ)) + (ε n : ℂ) * I := by
        funext n; simp [A]
      rw [this]
      have h0 : Tendsto (fun n => (((z.re + z.im * u : ℝ) : ℂ)) + (ε n : ℂ) * I) atTop
          (𝓝 ((((z.re + z.im * u : ℝ) : ℂ)) + ((0 : ℝ) : ℂ) * I)) := by
        refine tendsto_const_nhds.add (Tendsto.mul_const _ ?_)
        exact (continuous_ofReal.tendsto 0).comp hε0
      simpa using h0
  -- right side: continuity of `G` at `z`
  have hright : Tendsto (fun n => G (A n I)) atTop (𝓝 (G z)) := by
    have hcont : ContinuousAt G z := (hG z hz).continuousAt
    refine hcont.tendsto.comp ?_
    have : (fun n => A n I) = fun n => z + (ε n : ℂ) * I := by
      funext n; apply Complex.ext <;> simp [A]
    rw [this]
    have h0 : Tendsto (fun n => z + (ε n : ℂ) * I) atTop (𝓝 (z + ((0 : ℝ) : ℂ) * I)) := by
      refine tendsto_const_nhds.add (Tendsto.mul_const _ ?_)
      exact (continuous_ofReal.tendsto 0).comp hε0
    simpa using h0
  have := hleft.congr (fun n => hmean n)
  exact tendsto_nhds_unique this hright

end Affine

/-- **Poisson representation of the bounded analytic exponential.** For a scalar finite atomic Herglotz function `q`, `t ≥ 0` and `Im z > 0`:
`e^{itq(z)} = ∫ (1/(π(1+u²))) e^{itq(Re z + Im z · u)} du`. The boundary values are those of
`ScalarAtomicHerglotz.seval` at real points. They are defined off the finitely many poles, which
form a Lebesgue-null set in `u`. -/
theorem integral_standardCauchyWeight_smul_cexp_seval (q : ScalarAtomicHerglotz) {t : ℝ}
    (ht : 0 ≤ t) {z : ℂ} (hz : 0 < z.im) :
    (∫ u : ℝ, standardCauchyWeight u • cexp (I * t * q.seval ((z.re + z.im * u : ℝ) : ℂ))) =
      cexp (I * t * q.seval z) := by
  refine integral_standardCauchyWeight_smul_affine_eq_of_analyticAt
    (fun w => cexp (I * t * q.seval w)) ?_ 1 ?_ q.weight.support ?_ hz
  · intro w hw
    have := q.analyticAt_seval_of_im_ne hw.ne'
    fun_prop
  · intro w hw
    exact norm_cexp_I_mul_le_one ht (q.seval_im_nonneg hw.le)
  · intro x hx
    have hpole : ∀ y ∈ q.weight.support, (y : ℂ) ≠ (x : ℂ) := by
      intro y hy h
      exact hx (by rw [← Complex.ofReal_injective h]; exact hy)
    have hc : ContinuousAt (fun w => cexp (I * t * q.seval w)) (x : ℂ) := by
      have := q.continuousAt_seval hpole
      fun_prop
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

section CauchyLaw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Cauchy law `cauchyMeasure x₀ γ` (`γ ≠ 0`) is the image of the standard Cauchy density
under `u ↦ x₀ + γu` (totalized integrals; no integrability hypothesis). -/
theorem integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul_scale (x₀ : ℝ) {γ : ℝ≥0}
    (hγ : γ ≠ 0) (f : ℝ → E) :
    (∫ x, f x ∂ProbabilityTheory.cauchyMeasure x₀ γ) =
      ∫ u : ℝ, standardCauchyWeight u • f (x₀ + γ * u) := by
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero x₀ hγ,
    integral_withDensity_eq_integral_toReal_smul
      (ProbabilityTheory.measurable_cauchyPDF x₀ γ)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hγ0 : (0 : ℝ) < γ := lt_of_le_of_ne γ.2 (fun h => hγ (by exact_mod_cast h.symm))
  let g : ℝ → E := fun x => (ProbabilityTheory.cauchyPDF x₀ γ x).toReal • f x
  have hg : ∀ u : ℝ, standardCauchyWeight u • f (x₀ + γ * u) = (γ : ℝ) • g (x₀ + γ * u) := by
    intro u
    simp only [g, smul_smul]
    congr 1
    rw [ProbabilityTheory.cauchyPDF, ENNReal.toReal_ofReal
      (ProbabilityTheory.cauchyPDF_pos x₀ hγ _).le, ProbabilityTheory.cauchyPDFReal,
      standardCauchyWeight_eq]
    field_simp
    ring
  rw [show (∫ u : ℝ, standardCauchyWeight u • f (x₀ + γ * u)) =
      ∫ u : ℝ, (γ : ℝ) • g (x₀ + γ * u) from integral_congr_ae (Eventually.of_forall hg)]
  rw [integral_smul, Measure.integral_comp_mul_left (fun y => g (x₀ + y)) (γ : ℝ),
    integral_add_left_eq_self g x₀, smul_smul, abs_of_pos (inv_pos.mpr hγ0),
    mul_inv_cancel₀ hγ0.ne', one_smul]

/-- `E e^{itX} = e^{-γt}` for `t ≥ 0` and `X` real Cauchy of center `0` and scale `γ`
(Mathlib `cauchyMeasure 0 γ`). -/
theorem integral_cexp_cauchyMeasure {t : ℝ} (ht : 0 ≤ t) (γ : ℝ≥0) :
    (∫ x, cexp (I * t * x) ∂ProbabilityTheory.cauchyMeasure 0 γ) = Real.exp (-(γ * t)) := by
  by_cases hγ : γ = 0
  · subst hγ
    rw [ProbabilityTheory.cauchyMeasure_zero_scale, integral_dirac]
    simp
  rw [integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul_scale 0 hγ]
  have hγ0 : (0 : ℝ) ≤ γ := γ.2
  have h := integral_standardCauchyWeight_smul_eq_of_analyticAt
    (fun w : ℂ => cexp (I * t * ((γ : ℂ) * w))) (fun w _ => by fun_prop) 1 (fun w hw => by
      apply norm_cexp_I_mul_le_one ht
      simpa using mul_nonneg hγ0 hw)
  simp only [zero_add]
  have hrw : ∀ u : ℝ, cexp (I * t * (((γ : ℝ) * u : ℝ) : ℂ)) = cexp (I * t * ((γ : ℂ) * u)) := by
    intro u; push_cast; rfl
  simp_rw [hrw]
  rw [h]
  rw [show I * t * ((γ : ℂ) * I) = ((-(γ * t) : ℝ) : ℂ) by
    push_cast; ring_nf; rw [Complex.I_sq]; ring]
  rw [← Complex.ofReal_exp]

/-- **Characteristic function of the real Cauchy law** (center `0`, scale `γ`):
`charFun (cauchyMeasure 0 γ) t = e^{-γ|t|}` for every real `t`. -/
theorem charFun_cauchyMeasure (γ : ℝ≥0) (t : ℝ) :
    charFun (ProbabilityTheory.cauchyMeasure 0 γ) t = Real.exp (-(γ * |t|)) := by
  rw [charFun_apply_real]
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, ← integral_cexp_cauchyMeasure ht]
    congr 1; funext x; ring_nf
  · rw [abs_of_nonpos ht, ← integral_cexp_cauchyMeasure (neg_nonneg.mpr ht)]
    by_cases hγ : γ = 0
    · subst hγ
      rw [ProbabilityTheory.cauchyMeasure_zero_scale, integral_dirac, integral_dirac]
      simp
    rw [integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul_scale 0 hγ,
      integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul_scale 0 hγ]
    rw [← integral_neg_eq_self]
    congr 1; funext u
    rw [standardCauchyWeight_eq, standardCauchyWeight_eq]
    push_cast
    ring_nf

end CauchyLaw

end BlockBand.Critical.Herglotz
