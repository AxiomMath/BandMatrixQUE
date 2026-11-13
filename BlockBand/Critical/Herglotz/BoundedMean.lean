module

public import BlockBand.Critical.Herglotz.PoissonExp
public import BlockBand.Critical.Herglotz.Statement
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The bounded analytic mean

* `measurable_quadForm_affine` — joint measurability of `(ω, u) ↦ v^*F(ω)(a + bu)v` from the
  joint measurability of `(ω, z) ↦ F(ω)(z)` (field `measurable_eval` of `HerglotzTailHypotheses`).
* `integral_cexp_quadForm_eq` — for each `N`,
  `E e^{itq_N(z)} = ∫ (1/(π(1+u²))) E e^{it Re q_N(Re z + Im z · u)} du`: the pathwise Poisson
  representation (`integral_standardCauchyWeight_smul_cexp_seval`) and Fubini.
* `tendsto_integral_cexp_quadForm` — **the bounded analytic mean** with a general scale `γ`:
  if, at every real `x`, `Re v^*F_N(x)v` converges in law to `cauchyMeasure 0 γ`, then for `t ≥ 0`
  and `Im z > 0`, `E e^{itv^*F_N(z)v} → e^{-γt}`. With `γ = ‖v‖²` this is `E e^{itv^*F_N(z)v} → e^{-t‖v‖²}`.
* `HerglotzTailHypotheses.tendsto_integral_cexp_quadForm` — the same, read off from the lemma's
  hypotheses (only `measurable_eval` and hypothesis 3 are used).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Complex MeasureTheory Filter
open scoped Topology NNReal Matrix

namespace BlockBand.Critical.Herglotz

open CoareaNative.BlockBand (standardCauchyWeight integral_standardCauchyWeight)

variable {r : ℕ}

/-- Joint measurability of `(ω, u) ↦ v^* F(ω)(a + b u) v`. -/
theorem measurable_quadForm_affine {Ω : Type*} [MeasurableSpace Ω] {F : Ω → AtomicHerglotz r}
    (hmeas : ∀ i j : Fin r, Measurable fun p : Ω × ℂ => (F p.1).eval p.2 i j)
    (v : Fin r → ℂ) (a b : ℝ) :
    Measurable fun p : Ω × ℝ => (F p.1).quadForm v ((a + b * p.2 : ℝ) : ℂ) := by
  have hmap : Measurable fun p : Ω × ℝ => (p.1, ((a + b * p.2 : ℝ) : ℂ)) := by
    refine measurable_fst.prodMk ?_
    exact Complex.measurable_ofReal.comp (measurable_const.add (measurable_const.mul measurable_snd))
  unfold AtomicHerglotz.quadForm dotProduct Matrix.mulVec dotProduct
  refine Finset.measurable_sum _ fun i _ => ?_
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  exact ((hmeas i j).comp hmap).mul measurable_const

/-- Pathwise Poisson representation and Fubini: for `t ≥ 0`, `Im z > 0` and a jointly measurable
random atomic Herglotz function on a probability space,
`E e^{itq(z)} = ∫ (1/(π(1+u²))) E e^{it Re q(Re z + Im z · u)} du`, `q = v^*Fv`. -/
theorem integral_cexp_quadForm_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Ω → AtomicHerglotz r}
    (hmeas : ∀ i j : Fin r, Measurable fun p : Ω × ℂ => (F p.1).eval p.2 i j)
    (v : Fin r → ℂ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 0 < z.im) :
    (∫ ω, cexp (I * t * (F ω).quadForm v z) ∂P) =
      ∫ u : ℝ, standardCauchyWeight u •
        ∫ ω, cexp (I * t * (((F ω).quadForm v ((z.re + z.im * u : ℝ) : ℂ)).re : ℂ)) ∂P := by
  -- pathwise representation
  have hpath : ∀ ω, cexp (I * t * (F ω).quadForm v z) =
      ∫ u : ℝ, standardCauchyWeight u •
        cexp (I * t * (((F ω).quadForm v ((z.re + z.im * u : ℝ) : ℂ)).re : ℂ)) := by
    intro ω
    rw [AtomicHerglotz.quadForm_eq_seval, ←
      integral_standardCauchyWeight_smul_cexp_seval ((F ω).scalar v) ht hz]
    congr 1
    funext u
    congr 3
    rw [← AtomicHerglotz.quadForm_eq_seval]
    have him := AtomicHerglotz.quadForm_ofReal_im (F ω) v (z.re + z.im * u)
    apply Complex.ext
    · simp
    · simpa using him
  simp_rw [hpath]
  -- Fubini
  let f : Ω → ℝ → ℂ := fun ω u => standardCauchyWeight u •
    cexp (I * t * (((F ω).quadForm v ((z.re + z.im * u : ℝ) : ℂ)).re : ℂ))
  have hfm : Measurable (Function.uncurry f) := by
    have hq := measurable_quadForm_affine hmeas v z.re z.im
    have hw : Measurable fun p : Ω × ℝ => standardCauchyWeight p.2 :=
      (continuous_standardCauchyWeight.measurable).comp measurable_snd
    refine hw.smul ?_
    exact Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (Complex.measurable_re.comp hq)))
  have hint : Integrable (Function.uncurry f) (P.prod volume) := by
    have hdom : Integrable (fun p : Ω × ℝ => (1 : ℝ) * standardCauchyWeight p.2)
        (P.prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod integrable_standardCauchyWeight
    refine hdom.mono' hfm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, f, one_mul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (standardCauchyWeight_nonneg _)]
    refine mul_le_of_le_one_right (standardCauchyWeight_nonneg _) ?_
    apply norm_cexp_I_mul_le_one ht
    simp
  rw [integral_integral_swap hint]
  congr 1
  funext u
  exact integral_smul _ _

/-- **The bounded analytic mean**, scale `γ`. Law: random finite atomic
Herglotz functions `F N` on probability spaces `(Ω N, P N)`, jointly measurable in `(ω, z)`.
Hypothesis: at every real `x`, `Re v^*F_N(x)v` converges in law to `cauchyMeasure 0 γ`
(hypothesis 3 at the fixed vector `v`). Conclusion: for `t ≥ 0` and `Im z > 0`,
`E e^{itv^*F_N(z)v} → e^{-γt}` as `N → ∞`. No uniformity in `z` or `t` is claimed. -/
theorem tendsto_integral_cexp_quadForm {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)]
    {F : ∀ N, Ω N → AtomicHerglotz r}
    (hmeas : ∀ N (i j : Fin r), Measurable fun p : Ω N × ℂ => (F N p.1).eval p.2 i j)
    (v : Fin r → ℂ) (γ : ℝ≥0)
    (hbd : ∀ x : ℝ, TendstoInDistribution (fun N ω => ((F N ω).quadForm v x).re) atTop id P
      (ProbabilityTheory.cauchyMeasure 0 γ))
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun N => ∫ ω, cexp (I * t * (F N ω).quadForm v z) ∂P N) atTop
      (𝓝 ((Real.exp (-(γ * t)) : ℝ) : ℂ)) := by
  simp_rw [integral_cexp_quadForm_eq (hmeas _) v ht hz]
  set φ : ℕ → ℝ → ℂ := fun N u =>
    ∫ ω, cexp (I * t * (((F N ω).quadForm v ((z.re + z.im * u : ℝ) : ℂ)).re : ℂ)) ∂P N
    with hφ
  -- pointwise limit from hypothesis 3 via characteristic functions
  have hpt : ∀ u : ℝ, Tendsto (fun N => φ N u) atTop (𝓝 ((Real.exp (-(γ * t)) : ℝ) : ℂ)) := by
    intro u
    have h := (hbd (z.re + z.im * u)).tendsto_charFun t
    have hlim : charFun ((ProbabilityTheory.cauchyMeasure 0 γ).map id) t =
        ((Real.exp (-(γ * t)) : ℝ) : ℂ) := by
      rw [Measure.map_id, charFun_cauchyMeasure, abs_of_nonneg ht]
    rw [hlim] at h
    refine h.congr fun N => ?_
    rw [charFun_apply_real, integral_map ((hbd (z.re + z.im * u)).forall_aemeasurable N)
      (by fun_prop)]
    simp only [hφ]
    congr 1
    funext ω
    congr 1
    ring
  -- dominated convergence in `u`
  have hmeasφ : ∀ N, Measurable fun u : ℝ => φ N u := by
    intro N
    have hq := measurable_quadForm_affine (hmeas N) v z.re z.im
    have hg : Measurable fun p : ℝ × Ω N =>
        cexp (I * t * (((F N p.2).quadForm v ((z.re + z.im * p.1 : ℝ) : ℂ)).re : ℂ)) := by
      have hq' := hq.comp measurable_swap
      exact Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp (Complex.measurable_re.comp hq')))
    exact (hg.stronglyMeasurable.integral_prod_right' (ν := P N)).measurable
  have hbound : ∀ N u, ‖φ N u‖ ≤ 1 := by
    intro N u
    have := norm_integral_le_of_norm_le_const (μ := P N) (C := (1 : ℝ))
      (f := fun ω => cexp (I * t * (((F N ω).quadForm v ((z.re + z.im * u : ℝ) : ℂ)).re : ℂ)))
      (Eventually.of_forall fun ω => norm_cexp_I_mul_le_one ht (by simp))
    simp only [probReal_univ, mul_one] at this
    exact this
  have hDCT : Tendsto (fun N => ∫ u : ℝ, standardCauchyWeight u • φ N u) atTop
      (𝓝 (∫ u : ℝ, standardCauchyWeight u • ((Real.exp (-(γ * t)) : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence standardCauchyWeight
      (fun N => (continuous_standardCauchyWeight.measurable.smul
        (hmeasφ N)).aestronglyMeasurable)
      integrable_standardCauchyWeight (fun N => Eventually.of_forall fun u => ?_)
      (Eventually.of_forall fun u => (hpt u).const_smul _)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (standardCauchyWeight_nonneg u)]
    exact mul_le_of_le_one_right (standardCauchyWeight_nonneg u) (hbound N u)
  rwa [integral_smul_const, integral_standardCauchyWeight, one_smul] at hDCT

/-- The bounded analytic mean from the hypotheses of the Herglotz tail lemma: for every
deterministic `v`, `t ≥ 0` and `Im z > 0`, `E e^{itv^*F_N(z)v} → e^{-t‖v‖²}`. -/
theorem HerglotzTailHypotheses.tendsto_integral_cexp_quadForm {Ω : ℕ → Type*}
    [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)]
    {F : ∀ N, Ω N → AtomicHerglotz r} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    (h : HerglotzTailHypotheses r P F P' Ξ) (v : Fin r → ℂ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : 0 < z.im) :
    Tendsto (fun N => ∫ ω, cexp (I * t * (F N ω).quadForm v z) ∂P N) atTop
      (𝓝 ((Real.exp (-((euclidSqNorm v : ℝ) * t)) : ℝ) : ℂ)) :=
  BlockBand.Critical.Herglotz.tendsto_integral_cexp_quadForm h.measurable_eval v
    (euclidSqNorm v) (fun x => h.boundary x v) ht hz

end BlockBand.Critical.Herglotz
