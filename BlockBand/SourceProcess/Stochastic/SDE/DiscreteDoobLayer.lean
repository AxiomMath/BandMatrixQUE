module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.MeanInequalities

/-!
# Discrete Doob Lᵖ inequality, part 1: layer cake and Fubini

Running maximum `runMax f n = max_{k ≤ n} f_k`, the layer-cake bound obtained from
`MeasureTheory.maximal_ineq`, the untruncated Fubini swap and the Hölder step, for a
non-negative discrete-time submartingale `f : ℕ → Ω → ℝ` on a finite measure space
`(Ω, μ)` with a filtration `𝒢 : Filtration ℕ`.
-/

@[expose] public section

open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal

namespace BlockBand.SourceProcess.Stochastic.SDE.DoobLp
open MeasureTheory

variable {Ω : Type*}

/-- Internal abbreviation for the running maximum
`max {f 0 ω, f 1 ω, …, f n ω}` (private in the donor). The main theorem
states the bound in terms of the explicit `Finset.sup'` form to match
`MeasureTheory.maximal_ineq`. -/
def runMax (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k ↦ f k ω)

lemma runMax_nonneg {f : ℕ → Ω → ℝ} (hnonneg : ∀ n ω, 0 ≤ f n ω) (n : ℕ) (ω : Ω) :
    0 ≤ runMax f n ω :=
  le_trans (hnonneg 0 ω)
    (Finset.le_sup' (f := fun k ↦ f k ω) (Finset.mem_range.mpr (Nat.succ_pos n)))

variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}

lemma runMax_measurable {f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ m0}
    (hsub : Submartingale f 𝒢 μ) (n : ℕ) :
    Measurable (runMax f n) := by
  unfold runMax
  exact Finset.measurable_range_sup''
    (fun k _ ↦ ((hsub.stronglyMeasurable k).mono (𝒢.le k)).measurable)

/-- Pointwise (in `t > 0`) integrand bound. -/
lemma layer_integrand_bound
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω) (n : ℕ) {p : ℝ}
    {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ runMax f n ω} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal (t ^ (p - 2)) *
          ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ) := by
  have ht_pow_pos : (0 : ℝ) ≤ t ^ (p - 2) := Real.rpow_nonneg ht.le _
  have h_decomp : t ^ (p - 1) = t ^ (p - 2) * t := by
    rw [show (p - 1) = (p - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
  rw [h_decomp, ENNReal.ofReal_mul ht_pow_pos]
  rw [show μ {ω | t ≤ runMax f n ω} * (ENNReal.ofReal (t^(p-2)) * ENNReal.ofReal t)
        = ENNReal.ofReal (t^(p-2)) * (ENNReal.ofReal t * μ {ω | t ≤ runMax f n ω})
        by ring]
  gcongr
  -- Apply Doob's weak-type maximal inequality at level `t`.
  have key := MeasureTheory.maximal_ineq (μ := μ) (𝒢 := 𝒢)
    (f := f) hsub (fun k ω ↦ hnonneg k ω) (ε := t.toNNReal) n
  rw [show ({ω | t ≤ runMax f n ω}) = ({ω | (↑t.toNNReal : ℝ) ≤ runMax f n ω}) by
    rw [Real.coe_toNNReal _ ht.le]]
  exact key

/-- Combining steps: A ≤ ofReal p · ∫⁻ t in Ioi 0, ofReal(t^(p-2)) · ofReal(∫_{fstar ≥ t} f_n). -/
lemma A_le_layer_integral
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ
      ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi (0:ℝ),
            ENNReal.ofReal (t ^ (p - 2)) *
              ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul μ
        (ae_of_all _ (runMax_nonneg hnonneg n))
        (runMax_measurable hsub n).aemeasurable hp_pos]
  apply mul_le_mul_right _ (ENNReal.ofReal p)
  apply MeasureTheory.setLIntegral_mono_ae'
  · exact measurableSet_Ioi
  refine Filter.Eventually.of_forall (fun t ht ↦ ?_)
  exact layer_integrand_bound hsub hnonneg n ht

/-- Inner integral evaluation: `∫⁻ t in Ioc 0 f, ofReal(t^(p-2)) = ofReal(f^(p-1)/(p-1))`. -/
lemma lintegral_rpow_Ioc
    {f p : ℝ} (hf : 0 < f) (hp : 1 < p) :
    ∫⁻ t in Set.Ioc (0:ℝ) f, ENNReal.ofReal (t^(p-2)) =
      ENNReal.ofReal (f^(p-1)/(p-1)) := by
  have hpm1 : -1 < p - 2 := by linarith
  rw [show (f^(p-1)/(p-1) : ℝ) = ∫ t in Set.Ioc (0:ℝ) f, t^(p-2) from ?_]
  · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · apply MeasureTheory.IntegrableOn.integrable
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hf.le).mp
        (intervalIntegral.intervalIntegrable_rpow' hpm1)
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (ae_of_all _ (fun t ht ↦ Real.rpow_nonneg ht.1.le _))
  rw [← intervalIntegral.integral_of_le hf.le]
  rw [integral_rpow (Or.inl hpm1)]
  have hzp : (0:ℝ)^(p - 2 + 1) = 0 := Real.zero_rpow (by linarith : p - 2 + 1 ≠ 0)
  rw [hzp, show p - 2 + 1 = p - 1 by ring]
  ring

/-- Pointwise inner integral: for `fstar ≥ 0`, integrating `t^(p-2)` against
    the indicator `𝟙{0 < t ≤ fstar}` evaluates to `fstar^(p-1)/(p-1)`. -/
lemma inner_t_integral
    {fstar p : ℝ} (hfstar : 0 ≤ fstar) (hp : 1 < p) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t
      = ENNReal.ofReal (fstar ^ (p - 1) / (p - 1)) := by
  rcases hfstar.lt_or_eq with hpos | hzero
  · -- fstar > 0: rewrite indicator-restricted integral as setLIntegral on Ioc.
    have h_eq : Set.EqOn
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) *
            {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t)
        ((Set.Ioc 0 fstar).indicator (fun t ↦ ENNReal.ofReal (t ^ (p - 2))))
        (Set.Ioi (0:ℝ)) := by
      intro t ht
      simp only
      by_cases hle : t ≤ fstar
      · have hmem1 : t ∈ {t : ℝ | t ≤ fstar} := hle
        have hmem2 : t ∈ Set.Ioc (0:ℝ) fstar := ⟨ht, hle⟩
        rw [Set.indicator_of_mem hmem1, mul_one, Set.indicator_of_mem hmem2]
      · have hnmem1 : t ∉ {t : ℝ | t ≤ fstar} := hle
        have hnmem2 : t ∉ Set.Ioc (0:ℝ) fstar := fun h ↦ hle h.2
        rw [Set.indicator_of_notMem hnmem1, mul_zero, Set.indicator_of_notMem hnmem2]
    rw [setLIntegral_congr_fun measurableSet_Ioi h_eq]
    have hsubset : Set.Ioc (0:ℝ) fstar ⊆ Set.Ioi 0 :=
      fun _ ht ↦ ht.1
    have : ∫⁻ t in Set.Ioi (0:ℝ), (Set.Ioc 0 fstar).indicator
              (fun t ↦ ENNReal.ofReal (t ^ (p - 2))) t
            = ∫⁻ t in Set.Ioc (0:ℝ) fstar, ENNReal.ofReal (t ^ (p - 2)) := by
      rw [setLIntegral_indicator measurableSet_Ioc,
          Set.inter_eq_left.mpr hsubset]
    rw [this]
    exact lintegral_rpow_Ioc hpos hp
  · -- fstar = 0: both sides are 0.
    subst hzero
    have h_eq : Set.EqOn
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) *
            {t : ℝ | t ≤ (0:ℝ)}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t)
        (fun _ ↦ 0) (Set.Ioi (0:ℝ)) := by
      intro t ht
      simp only
      have hnot : t ∉ {t : ℝ | t ≤ (0:ℝ)} := by
        change ¬ t ≤ 0
        exact not_le.mpr ht
      rw [Set.indicator_of_notMem hnot, mul_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi h_eq, lintegral_zero]
    have hp10 : p - 1 ≠ 0 := by linarith
    simp [Real.zero_rpow hp10]

/-- Fubini swap stage (Tier A.2 Stage 1).

    For `p > 1`, a non-negative submartingale `f`, and a time `n`, the
    iterated integral
       `∫⁻ t in Ioi 0, ofReal(t^(p-2)) ⋅ ∫⁻_{fstar ≥ t} ofReal(f_n) dμ`
    equals
       `∫⁻ ω, ofReal(f_n ω) ⋅ ofReal((fstar ω)^(p-1) / (p-1)) dμ`.

    Proof: rewrite the inner set-integral as an indicator-weighted full
    integral; apply `MeasureTheory.lintegral_lintegral_swap` to swap the
    order of integration; then evaluate the inner `t`-integral pointwise
    via `inner_t_integral`. -/
lemma fubini_swap
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((runMax f n ω) ^ (p - 1) / (p - 1)) ∂μ := by
  -- Measurability of runMax f n and f n.
  have hRunMaxMeas : Measurable (runMax f n) := runMax_measurable hsub n
  have hsubM : Measurable (f n) :=
    ((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl
  -- Joint set {(t,ω) | t ≤ runMax f n ω} is product-measurable as the
  -- preimage of {(a,b) : ℝ×ℝ | a ≤ b} under (fst, runMax ∘ snd).
  have hJointSet : MeasurableSet {pr : ℝ × Ω | pr.1 ≤ runMax f n pr.2} := by
    have h1 : Measurable (fun pr : ℝ × Ω ↦ pr.1) := measurable_fst
    have h2 : Measurable (fun pr : ℝ × Ω ↦ runMax f n pr.2) :=
      hRunMaxMeas.comp measurable_snd
    exact measurableSet_le h1 h2
  -- Step 1: rewrite the inner setLIntegral as a full lintegral via indicator.
  have step1 : ∀ t,
      ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
        = ∫⁻ ω, {ω | t ≤ runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    rw [lintegral_indicator (measurableSet_le measurable_const hRunMaxMeas)]
  -- Step 2: pull the constant `ofReal(t^(p-2))` inside the inner lintegral.
  have step2 : ∀ t, ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ ω, {ω | t ≤ runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ
      = ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
              {ω | t ≤ runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    exact (lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp hsubM).indicator
            (measurableSet_le measurable_const hRunMaxMeas))).symm
  simp_rw [step1, step2]
  -- Joint measurability of the bivariate integrand.
  have hF_meas : Measurable (fun pr : ℝ × Ω ↦
      ENNReal.ofReal (pr.1 ^ (p - 2)) *
        {q : ℝ × Ω | q.1 ≤ runMax f n q.2}.indicator
          (fun q ↦ ENNReal.ofReal (f n q.2)) pr) := by
    refine Measurable.mul ?_ ?_
    · refine ENNReal.measurable_ofReal.comp ?_
      exact (measurable_fst : Measurable (fun pr : ℝ × Ω ↦ pr.1)).pow_const (p - 2)
    · refine Measurable.indicator ?_ hJointSet
      exact ENNReal.measurable_ofReal.comp (hsubM.comp measurable_snd)
  -- Rewrite the LHS with indicator on Ioi 0 (so it becomes a full lintegral
  -- over ℝ) and apply lintegral_lintegral_swap on ℝ × Ω.
  rw [← lintegral_indicator measurableSet_Ioi]
  -- LHS now is ∫⁻ t, (Ioi 0).indicator (fun t ↦ ∫⁻ ω, F(t,ω) ∂μ) t ∂volume
  -- Massage to ∫⁻ t, ∫⁻ ω, (Ioi 0).indicator (fun _ ↦ F(t,ω)) t ∂μ
  have lhs_rewrite : ∫⁻ a, (Set.Ioi (0:ℝ)).indicator
        (fun t ↦ ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
                {ω | t ≤ runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ) a
      = ∫⁻ t, ∫⁻ ω, (Set.Ioi (0:ℝ)).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                {ω | s ≤ runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t ∂μ := by
    apply lintegral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem ht]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, ← lintegral_zero (μ := μ)]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_notMem ht]
  rw [lhs_rewrite]
  -- Now apply lintegral_lintegral_swap.
  have hSwap_meas : AEMeasurable
      (Function.uncurry (fun t ω ↦ (Set.Ioi (0:ℝ)).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω | s ≤ runMax f n ω}.indicator
              (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t))
      (volume.prod μ) := by
    refine (Measurable.indicator ?_ ?_).aemeasurable
    · exact hF_meas
    · exact measurable_fst measurableSet_Ioi
  rw [lintegral_lintegral_swap hSwap_meas]
  -- Now have ∫⁻ ω, ∫⁻ t, indicator(Ioi 0) F(t,ω) ∂volume ∂μ.
  -- For each ω, the inner is the integral over Ioi 0 of
  --   ofReal(t^(p-2)) * 𝟙{t ≤ runMax f n ω} * ofReal(f n ω)
  -- = ofReal(f n ω) * (∫⁻ t in Ioi 0, ofReal(t^(p-2)) * 𝟙{t ≤ fstar ω})
  -- = ofReal(f n ω) * ofReal((runMax f n ω)^(p-1) / (p-1))  [inner_t_integral]
  apply lintegral_congr_ae
  filter_upwards with ω
  -- Reduce the inner integral.
  have h_inner_simp :
      ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω' | s ≤ runMax f n ω'}.indicator
              (fun ω' ↦ ENNReal.ofReal (f n ω')) ω) t
        = ENNReal.ofReal (f n ω) *
            ENNReal.ofReal ((runMax f n ω) ^ (p - 1) / (p - 1)) := by
    -- Rewrite the inner indicator
    have h_pointwise : ∀ t,
        (Set.Ioi (0:ℝ)).indicator
            (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
              {ω' | s ≤ runMax f n ω'}.indicator
                (fun ω' ↦ ENNReal.ofReal (f n ω')) ω) t
          = ENNReal.ofReal (f n ω) *
              ((Set.Ioi (0:ℝ)).indicator
                (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                  {s : ℝ | s ≤ runMax f n ω}.indicator
                    (fun _ ↦ (1 : ℝ≥0∞)) s)) t := by
      intro t
      by_cases ht : t ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        by_cases hle : t ≤ runMax f n ω
        · have hmem1 : ω ∈ {ω' | t ≤ runMax f n ω'} := hle
          have hmem2 : t ∈ {s : ℝ | s ≤ runMax f n ω} := hle
          rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, mul_one]
          ring
        · have hnmem1 : ω ∉ {ω' | t ≤ runMax f n ω'} := hle
          have hnmem2 : t ∉ {s : ℝ | s ≤ runMax f n ω} := hle
          rw [Set.indicator_of_notMem hnmem1, Set.indicator_of_notMem hnmem2,
              mul_zero, mul_zero]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
    simp_rw [h_pointwise]
    rw [lintegral_const_mul']
    · -- The inner lintegral matches inner_t_integral.
      have h_eq :
          ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                {s : ℝ | s ≤ runMax f n ω}.indicator
                  (fun _ ↦ (1 : ℝ≥0∞)) s) t
            = ∫⁻ t in Set.Ioi (0:ℝ),
                ENNReal.ofReal (t ^ (p - 2)) *
                  {s : ℝ | s ≤ runMax f n ω}.indicator
                    (fun _ ↦ (1 : ℝ≥0∞)) t := by
        rw [← lintegral_indicator measurableSet_Ioi]
      rw [h_eq, inner_t_integral (runMax_nonneg hnonneg n ω) hp]
    · exact ENNReal.ofReal_ne_top
  rw [h_inner_simp]

/-- Stage 2a: apply Hölder to the post-Fubini integral.

    For non-negative f, g and Hölder conjugates p, q (so 1/p + 1/q = 1):
       `∫⁻ ω, ofReal(f_n) ⋅ ofReal(fstar^(p-1)) ≤ (∫⁻ f_n^p)^(1/p) ⋅ (∫⁻ fstar^p)^(1/q)`.
    Wraps `ENNReal.lintegral_mul_le_Lp_mul_Lq` plus the rpow algebra
    `(x^(p-1))^q = x^p` (using `(p-1)*q = p`). -/
lemma holder_apply
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (f n ω) *
            ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) ∂μ)
      ≤ (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ) ^ ((p - 1) / p) := by
  set q := p / (p - 1) with hq_def
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  have hq_pos : 0 < q := by
    simp only [hq_def]
    positivity
  have hpm1_q_eq_p : (p - 1) * q = p := by
    simp only [hq_def]
    field_simp
  have hf_meas : AEMeasurable (fun ω ↦ ENNReal.ofReal (f n ω)) μ :=
    (ENNReal.measurable_ofReal.comp
      (((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl)).aemeasurable
  have hg_meas : AEMeasurable
      (fun ω ↦ ENNReal.ofReal ((runMax f n ω) ^ (p - 1))) μ :=
    (ENNReal.measurable_ofReal.comp
      ((runMax_measurable hsub n).pow_const (p - 1))).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf_meas hg_meas
  -- Rewrite (ofReal f_n)^p = ofReal(f_n^p) using nonneg.
  have h_f_pow : ∀ ω, (ENNReal.ofReal (f n ω)) ^ p = ENNReal.ofReal ((f n ω) ^ p) :=
    fun ω ↦ ENNReal.ofReal_rpow_of_nonneg (hnonneg n ω) hp_pos.le
  -- Rewrite (ofReal fstar^(p-1))^q = ofReal(fstar^p) using (p-1)*q = p.
  have h_g_pow : ∀ ω,
      (ENNReal.ofReal ((runMax f n ω) ^ (p - 1))) ^ q
        = ENNReal.ofReal ((runMax f n ω) ^ p) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg
          (Real.rpow_nonneg (runMax_nonneg hnonneg n ω) _) hq_pos.le,
        ← Real.rpow_mul (runMax_nonneg hnonneg n ω) (p - 1) q, hpm1_q_eq_p]
  simp_rw [h_f_pow, h_g_pow] at key
  -- The goal has 1/p and (p-1)/p; key has 1/q (= q⁻¹). Rewrite 1/q = (p-1)/p.
  have h_one_div_q : (1 / q : ℝ) = (p - 1) / p := by
    simp only [hq_def, one_div, inv_div]
  rw [h_one_div_q] at key
  exact key

end BlockBand.SourceProcess.Stochastic.SDE.DoobLp
