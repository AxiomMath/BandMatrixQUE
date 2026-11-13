module

public import BlockBand.SourceProcess.Stochastic.SDE.DiscreteDoobLayer

/-!
# Discrete Doob Lᵖ inequality, part 2: truncation

The truncated (`min f* K`) versions of the layer-cake, Fubini and Hölder steps, used to rule
out an infinite left-hand side a priori. Same setting as `DiscreteDoobLayer`.
-/

@[expose] public section

open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal

namespace BlockBand.SourceProcess.Stochastic.SDE.DoobLp
open MeasureTheory

variable {Ω : Type*}
variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}

/-- Truncated inner t-integral: for `fstar ≥ 0` and `K > 0`,
       `∫⁻ t in Ioi 0, t^(p-2) ⋅ 𝟙{0 < t ≤ K ∧ t ≤ fstar}
         = ofReal(min fstar K^(p-1) / (p-1))`.
    Identical to `inner_t_integral` but with an extra `t ≤ K` constraint,
    which makes the inner Ioc become `Ioc 0 (min fstar K)`. -/
lemma inner_t_integral_truncated
    {fstar K p : ℝ} (hfstar : 0 ≤ fstar) (hK : 0 < K) (hp : 1 < p) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) t *
         {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t)
      = ENNReal.ofReal ((min fstar K) ^ (p - 1) / (p - 1)) := by
  -- Reduce to the untruncated case via `t ≤ K ∧ t ≤ fstar ↔ t ≤ min fstar K`.
  have h_eq : ∀ t,
      (Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) t *
        {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t
      = {t : ℝ | t ≤ min fstar K}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t := fun t ↦ by
    by_cases hK' : t ≤ K
    · by_cases hfs : t ≤ fstar
      · rw [Set.indicator_of_mem (show t ∈ Set.Iic K from hK'),
            Set.indicator_of_mem (show t ∈ {t : ℝ | t ≤ fstar} from hfs),
            Set.indicator_of_mem (show t ∈ {t : ℝ | t ≤ min fstar K} from le_min hfs hK'),
            mul_one]
      · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | t ≤ fstar} from hfs),
            Set.indicator_of_notMem
              (show t ∉ {t : ℝ | t ≤ min fstar K} from
                fun h ↦ hfs (h.trans (min_le_left _ _))),
            mul_zero]
    · rw [Set.indicator_of_notMem (show t ∉ Set.Iic K from hK'),
          Set.indicator_of_notMem
            (show t ∉ {t : ℝ | t ≤ min fstar K} from
              fun h ↦ hK' (h.trans (min_le_right _ _))),
          zero_mul]
  simp_rw [h_eq]
  exact inner_t_integral (le_min hfstar hK.le) hp

/-- Truncated Fubini swap. Analog of `fubini_swap` but with the outer
    `t`-integral restricted to `Ioc 0 K`, producing
    `min (runMax f n) K` in the post-swap formula. -/
lemma fubini_swap_truncated
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    ∫⁻ t in Set.Ioc (0:ℝ) K,
        ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1) / (p - 1)) ∂μ := by
  -- Rewrite the LHS via an Ioi 0 outer integral with an Iic K indicator,
  -- so we can reuse the bivariate Fubini machinery.
  have hRunMaxMeas : Measurable (runMax f n) := runMax_measurable hsub n
  have hsubM : Measurable (f n) :=
    ((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl
  have hIocEqRestrict : Set.Ioc (0:ℝ) K = Set.Ioi 0 ∩ Set.Iic K := by
    ext t
    simp [Set.mem_Ioc, Set.mem_Ioi, Set.mem_Iic, and_comm]
  rw [hIocEqRestrict]
  rw [← MeasureTheory.lintegral_indicator (measurableSet_Ioi.inter measurableSet_Iic)]
  -- Step 1: rewrite the inner setLIntegral as a full lintegral via indicator.
  have step1 : ∀ t,
      ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
        = ∫⁻ ω, {ω | t ≤ runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    rw [lintegral_indicator (measurableSet_le measurable_const hRunMaxMeas)]
  -- Step 2: pull the constant ofReal(t^(p-2)) inside the inner lintegral.
  have step2 : ∀ t, ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ ω, {ω | t ≤ runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ
      = ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
              {ω | t ≤ runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    exact (lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp hsubM).indicator
            (measurableSet_le measurable_const hRunMaxMeas))).symm
  -- Joint measurability of the bivariate integrand (Ioi 0 ∩ Iic K is product-measurable).
  have hJointSet : MeasurableSet {pr : ℝ × Ω | pr.1 ≤ runMax f n pr.2} := by
    have h1 : Measurable (fun pr : ℝ × Ω ↦ pr.1) := measurable_fst
    have h2 : Measurable (fun pr : ℝ × Ω ↦ runMax f n pr.2) :=
      hRunMaxMeas.comp measurable_snd
    exact measurableSet_le h1 h2
  have hF_meas : Measurable (fun pr : ℝ × Ω ↦
      ENNReal.ofReal (pr.1 ^ (p - 2)) *
        {q : ℝ × Ω | q.1 ≤ runMax f n q.2}.indicator
          (fun q ↦ ENNReal.ofReal (f n q.2)) pr) := by
    refine Measurable.mul ?_ ?_
    · refine ENNReal.measurable_ofReal.comp ?_
      exact (measurable_fst : Measurable (fun pr : ℝ × Ω ↦ pr.1)).pow_const (p - 2)
    · refine Measurable.indicator ?_ hJointSet
      exact ENNReal.measurable_ofReal.comp (hsubM.comp measurable_snd)
  -- Rewrite outer indicator + push into bivariate integrand.
  have h_outer_eq : ∫⁻ a, (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) *
                ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ) a
      = ∫⁻ t, ∫⁻ ω, (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                {ω | s ≤ runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t ∂μ := by
    apply lintegral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Ioi (0:ℝ) ∩ Set.Iic K
    · rw [Set.indicator_of_mem ht, step1, step2]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, ← lintegral_zero (μ := μ)]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_notMem ht]
  rw [h_outer_eq]
  -- Apply Fubini.
  have hSwap_meas : AEMeasurable
      (Function.uncurry (fun t ω ↦ (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω | s ≤ runMax f n ω}.indicator
              (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t))
      (volume.prod μ) := by
    refine (Measurable.indicator ?_ ?_).aemeasurable
    · exact hF_meas
    · exact measurable_fst (measurableSet_Ioi.inter measurableSet_Iic)
  rw [lintegral_lintegral_swap hSwap_meas]
  apply lintegral_congr_ae
  filter_upwards with ω
  -- Pointwise: rewrite indicator product, pull out ofReal(f_n ω), use inner_t_integral_truncated.
  have h_pointwise : ∀ t,
      (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω' | s ≤ runMax f n ω'}.indicator
              (fun ω' ↦ ENNReal.ofReal (f n ω')) ω) t
        = ENNReal.ofReal (f n ω) *
            ((Set.Ioi (0:ℝ)).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) s *
                 {s : ℝ | s ≤ runMax f n ω}.indicator
                  (fun _ ↦ (1 : ℝ≥0∞)) s)) t) := by
    intro t
    by_cases ht_pos : t ∈ Set.Ioi (0:ℝ)
    · by_cases ht_K : t ∈ Set.Iic K
      · have ht_both : t ∈ Set.Ioi (0:ℝ) ∩ Set.Iic K := ⟨ht_pos, ht_K⟩
        rw [Set.indicator_of_mem ht_both, Set.indicator_of_mem ht_pos,
            Set.indicator_of_mem ht_K, one_mul]
        by_cases h_le : t ≤ runMax f n ω
        · have hmem1 : ω ∈ {ω' | t ≤ runMax f n ω'} := h_le
          have hmem2 : t ∈ {s : ℝ | s ≤ runMax f n ω} := h_le
          rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, mul_one]
          ring
        · have hnmem1 : ω ∉ {ω' | t ≤ runMax f n ω'} := h_le
          have hnmem2 : t ∉ {s : ℝ | s ≤ runMax f n ω} := h_le
          rw [Set.indicator_of_notMem hnmem1, Set.indicator_of_notMem hnmem2]
          ring
      · have ht_not_both : t ∉ Set.Ioi (0:ℝ) ∩ Set.Iic K := fun h ↦ ht_K h.2
        rw [Set.indicator_of_notMem ht_not_both, Set.indicator_of_mem ht_pos,
            Set.indicator_of_notMem ht_K, zero_mul, mul_zero, mul_zero]
    · have ht_not_both : t ∉ Set.Ioi (0:ℝ) ∩ Set.Iic K := fun h ↦ ht_pos h.1
      rw [Set.indicator_of_notMem ht_not_both,
          Set.indicator_of_notMem ht_pos, mul_zero]
  simp_rw [h_pointwise]
  rw [lintegral_const_mul']
  · -- Convert to setLIntegral on Ioi 0, then apply inner_t_integral_truncated.
    have h_unfold :
        ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
            (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
              ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) s *
               {s : ℝ | s ≤ runMax f n ω}.indicator
                (fun _ ↦ (1 : ℝ≥0∞)) s)) t
          = ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
              ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) t *
               {t : ℝ | t ≤ runMax f n ω}.indicator
                (fun _ ↦ (1 : ℝ≥0∞)) t) := by
      rw [← lintegral_indicator measurableSet_Ioi]
    rw [h_unfold]
    rw [inner_t_integral_truncated (runMax_nonneg hnonneg n ω) hK hp]
  · exact ENNReal.ofReal_ne_top

/-- Truncated layer-cake bound: for `Z_K = min (runMax f n) K`,
       `∫⁻ Z_K^p ≤ ofReal(p) * ∫⁻ t in Ioc 0 K, ofReal(t^(p-2)) * ofReal(∫_{fstar ≥ t} f_n)`. -/
lemma A_K_le_layer_integral
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    ∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ
      ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioc (0:ℝ) K,
            ENNReal.ofReal (t ^ (p - 2)) *
              ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  -- Apply layer cake to Z_K = min (runMax f n) K.
  have hZK_nn : ∀ ω, 0 ≤ min (runMax f n ω) K :=
    fun ω ↦ le_min (runMax_nonneg hnonneg n ω) hK.le
  have hZK_meas : Measurable (fun ω ↦ min (runMax f n ω) K) :=
    (runMax_measurable hsub n).min measurable_const
  have h_layer :=
    MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul μ
      (ae_of_all _ hZK_nn) hZK_meas.aemeasurable hp_pos
  rw [h_layer]
  -- The integrand `μ{Z_K ≥ t} * ofReal(t^(p-1))` equals
  -- `μ{runMax ≥ t} * ofReal(t^(p-1))` for t ∈ Ioc 0 K and 0 for t > K.
  have h_ZK_set : ∀ t > (0:ℝ),
      μ {ω | t ≤ min (runMax f n ω) K} =
        if t ≤ K then μ {ω | t ≤ runMax f n ω} else 0 := by
    intro t ht
    by_cases hle : t ≤ K
    · simp only [hle, ite_true]
      congr 1
      ext ω
      simp [hle]
    · simp only [hle, ite_false]
      rw [show {ω | t ≤ min (runMax f n ω) K} = ∅ by
        ext ω
        simp [hle]]
      simp
  -- Restrict the outer integral to Ioc 0 K.
  have h_split : ∫⁻ t in Set.Ioi (0:ℝ), μ {ω | t ≤ min (runMax f n ω) K} *
                  ENNReal.ofReal (t ^ (p - 1))
              = ∫⁻ t in Set.Ioc (0:ℝ) K, μ {ω | t ≤ runMax f n ω} *
                  ENNReal.ofReal (t ^ (p - 1)) := by
    have hIoiSplit : Set.Ioi (0:ℝ) = Set.Ioc 0 K ∪ Set.Ioi K := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h
        by_cases hle : t ≤ K
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr (not_le.mp hle)
      · rintro (⟨h1, _⟩ | h)
        · exact h1
        · exact lt_trans hK h
    rw [hIoiSplit, lintegral_union measurableSet_Ioi
        (by rw [Set.disjoint_iff]
            intro t ⟨h1, h2⟩
            simp only [Set.mem_Ioc, Set.mem_Ioi] at h1 h2
            linarith [h2, h1.2])]
    have h_zero_right : ∫⁻ t in Set.Ioi K, μ {ω | t ≤ min (runMax f n ω) K} *
                          ENNReal.ofReal (t ^ (p - 1)) = 0 := by
      apply setLIntegral_eq_zero measurableSet_Ioi
      intro t ht
      have ht_pos : 0 < t := lt_trans hK ht
      have h_eq_zero : μ {ω | t ≤ min (runMax f n ω) K} = 0 := by
        rw [h_ZK_set t ht_pos]
        have ht_gt : ¬ t ≤ K := not_le.mpr ht
        simp [ht_gt]
      change μ {ω | t ≤ min (runMax f n ω) K} * _ = 0
      rw [h_eq_zero, zero_mul]
    have h_left : ∫⁻ t in Set.Ioc (0:ℝ) K, μ {ω | t ≤ min (runMax f n ω) K} *
                    ENNReal.ofReal (t ^ (p - 1))
                = ∫⁻ t in Set.Ioc (0:ℝ) K, μ {ω | t ≤ runMax f n ω} *
                    ENNReal.ofReal (t ^ (p - 1)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change μ {ω | t ≤ min (runMax f n ω) K} * _ =
            μ {ω | t ≤ runMax f n ω} * _
      simp only [h_ZK_set t ht.1, ht.2, ite_true]
    rw [h_left, h_zero_right, add_zero]
  rw [h_split]
  -- Now apply layer_integrand_bound pointwise.
  apply mul_le_mul_right _ (ENNReal.ofReal p)
  apply setLIntegral_mono_ae'
  · exact measurableSet_Ioc
  refine Filter.Eventually.of_forall (fun t ht ↦ ?_)
  exact layer_integrand_bound hsub hnonneg n ht.1

/-- Truncated holder_step: master bound for `A_K = ∫⁻ (min fstar K)^p`. -/
lemma holder_step_truncated
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    (∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ)
      ≤ ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ) ^ ((p - 1) / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  -- Step 1: bound A_K via A_K_le_layer_integral.
  have hA := A_K_le_layer_integral hsub hnonneg hp n K hK
  -- Step 2: rewrite the inner Bochner integral as a setLIntegral of ofReal.
  have h_inner_rewrite : ∀ t,
      ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ)
        = ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ := fun _ ↦
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsub.integrable n).restrict
      (ae_of_all _ (hnonneg n))
  simp_rw [h_inner_rewrite] at hA
  -- Step 3: apply truncated Fubini swap.
  rw [fubini_swap_truncated hsub hnonneg hp n K hK] at hA
  -- Step 4: factor `ofReal((Z_K)^(p-1)/(p-1))` into `ofReal((Z_K)^(p-1)) * ofReal(1/(p-1))`.
  have h_factor : ∀ ω,
      ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1) / (p - 1))
        = ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) *
            ENNReal.ofReal (1 / (p - 1)) := by
    intro ω
    have hZK_nn : 0 ≤ min (runMax f n ω) K := le_min (runMax_nonneg hnonneg n ω) hK.le
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg hZK_nn _),
        show (p - 1)⁻¹ = 1 / (p - 1) by rw [one_div]]
  simp_rw [h_factor] at hA
  -- Step 5: pull constant ofReal(1/(p-1)) outside.
  have hsubM : Measurable (f n) :=
    ((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl
  have hZKmeas : Measurable (fun ω ↦ min (runMax f n ω) K) :=
    (runMax_measurable hsub n).min measurable_const
  have h_mul_const :
      ∫⁻ ω, ENNReal.ofReal (f n ω) *
        (ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) *
          ENNReal.ofReal (1 / (p - 1))) ∂μ
      = ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) ∂μ := by
    rw [← lintegral_const_mul]
    · congr 1
      funext ω
      ring
    · exact ((ENNReal.measurable_ofReal.comp hsubM).mul
        (ENNReal.measurable_ofReal.comp (hZKmeas.pow_const (p - 1))))
  rw [h_mul_const] at hA
  -- Step 6: combine ofReal(p) * ofReal(1/(p-1)) = ofReal(p/(p-1)).
  have h_const_combine :
      ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) = ENNReal.ofReal (p / (p - 1)) := by
    rw [← ENNReal.ofReal_mul hp_pos.le]
    congr 1
    field_simp
  rw [show ENNReal.ofReal p * (ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) ∂μ)
      = ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) ∂μ from by ring,
      h_const_combine] at hA
  -- Step 7: apply Hölder to bound the inner integral.
  refine hA.trans ?_
  rw [mul_assoc]
  gcongr
  -- Hölder: ∫⁻ ofReal(f n) * ofReal(Z_K^(p-1))
  --   ≤ (∫⁻ ofReal(f n^p))^(1/p) * (∫⁻ ofReal(Z_K^p))^((p-1)/p)
  set q := p / (p - 1) with hq_def
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq_pos : 0 < q := by
    simp only [hq_def]
    positivity
  have hpm1_q_eq_p : (p - 1) * q = p := by
    simp only [hq_def]
    field_simp
  have hf_meas : AEMeasurable (fun ω ↦ ENNReal.ofReal (f n ω)) μ :=
    (ENNReal.measurable_ofReal.comp hsubM).aemeasurable
  have hg_meas : AEMeasurable
      (fun ω ↦ ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1))) μ :=
    (ENNReal.measurable_ofReal.comp (hZKmeas.pow_const (p - 1))).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf_meas hg_meas
  have h_f_pow : ∀ ω, (ENNReal.ofReal (f n ω)) ^ p = ENNReal.ofReal ((f n ω) ^ p) :=
    fun ω ↦ ENNReal.ofReal_rpow_of_nonneg (hnonneg n ω) hp_pos.le
  have h_g_pow : ∀ ω,
      (ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1))) ^ q
        = ENNReal.ofReal ((min (runMax f n ω) K) ^ p) := by
    intro ω
    have hZK_nn : 0 ≤ min (runMax f n ω) K := le_min (runMax_nonneg hnonneg n ω) hK.le
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hZK_nn _) hq_pos.le,
        ← Real.rpow_mul hZK_nn (p - 1) q, hpm1_q_eq_p]
  simp_rw [h_f_pow, h_g_pow] at key
  have h_one_div_q : (1 / q : ℝ) = (p - 1) / p := by
    simp only [hq_def, one_div, inv_div]
  rw [h_one_div_q] at key
  have hlhs : ∫⁻ a : Ω, ((fun ω ↦ ENNReal.ofReal (f n ω)) *
              fun ω ↦ ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1))) a ∂μ
            = ∫⁻ ω, ENNReal.ofReal (f n ω) *
                    ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) ∂μ := by rfl
  rw [hlhs] at key
  exact key

end BlockBand.SourceProcess.Stochastic.SDE.DoobLp
