module

public import BlockBand.SourceProcess.Stochastic.SDE.DiscreteDoobTruncated

/-!
# Discrete Doob Lᵖ maximal inequality

For a non-negative submartingale `f : ℕ → Ω → ℝ` on a finite measure space and `p > 1`,
`‖max_{k ≤ n} f_k‖_{Lᵖ(μ)} ≤ (p/(p-1)) ‖f_n‖_{Lᵖ(μ)}` (`DoobLp.maximal_ineq_Lp`), and the
same for `‖f_k‖` of a Banach-valued martingale (`DoobLp.martingale_eLpNorm_runMax_norm_le`).
No integrability beyond the (sub)martingale property is assumed; the right side may be `⊤`.
-/

@[expose] public section

open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal

namespace BlockBand.SourceProcess.Stochastic.SDE.DoobLp
open MeasureTheory

variable {Ω : Type*}
variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}

/-- Stage 2 (Hölder + algebra): combining Fubini's output with Hölder
    yields the master bound on `∫⁻ fstar^p`. -/
lemma holder_step
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ)
      ≤ ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ) ^ ((p - 1) / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  have hpm1_inv_pos : 0 < 1 / (p - 1) := by positivity
  -- Step 1: bound A := ∫⁻ fstar^p via A_le_layer_integral.
  have hA := A_le_layer_integral hsub hnonneg hp n
  -- Step 2: rewrite the inner Bochner setIntegral as a setLIntegral.
  have h_inner_rewrite : ∀ t,
      ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ)
        = ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ := fun _ ↦
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsub.integrable n).restrict
      (ae_of_all _ (hnonneg n))
  simp_rw [h_inner_rewrite] at hA
  -- Step 3: apply Fubini swap.
  rw [fubini_swap hsub hnonneg hp n] at hA
  -- Step 4: factor `ofReal(fstar^(p-1)/(p-1))` as `ofReal(fstar^(p-1)) * ofReal(1/(p-1))`.
  have h_factor : ∀ ω,
      ENNReal.ofReal ((runMax f n ω) ^ (p - 1) / (p - 1))
        = ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) * ENNReal.ofReal (1 / (p - 1)) := by
    intro ω
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg (runMax_nonneg hnonneg n ω) _),
        show (p - 1)⁻¹ = 1 / (p - 1) by rw [one_div]]
  simp_rw [h_factor] at hA
  -- Step 5: pull constant ofReal(1/(p-1)) outside the inner integral.
  have h_mul_const :
      ∫⁻ ω, ENNReal.ofReal (f n ω) *
        (ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) * ENNReal.ofReal (1 / (p - 1))) ∂μ
      = ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) ∂μ := by
    rw [← lintegral_const_mul]
    · congr 1
      funext ω
      ring
    · exact ((ENNReal.measurable_ofReal.comp
          (((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl)).mul
        (ENNReal.measurable_ofReal.comp
          ((runMax_measurable hsub n).pow_const (p - 1))))
  rw [h_mul_const] at hA
  -- Step 6: combine ofReal(p) * ofReal(1/(p-1)) = ofReal(p/(p-1)).
  have h_const_combine :
      ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) = ENNReal.ofReal (p / (p - 1)) := by
    rw [← ENNReal.ofReal_mul hp_pos.le]
    congr 1
    field_simp
  rw [show ENNReal.ofReal p * (ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) ∂μ)
      = ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) ∂μ from by ring,
      h_const_combine] at hA
  -- Step 7: apply holder_apply to bound the post-Fubini integral.
  refine hA.trans ?_
  rw [mul_assoc]
  gcongr
  exact holder_apply hsub hnonneg hp n

/-- Conversion lemma: for a non-negative `f : Ω → ℝ` and `1 < p`,
    `eLpNorm f (ofReal p) μ = (∫⁻ ω, ofReal(f ω ^ p) ∂μ)^(1/p)`. -/
lemma eLpNorm_eq_lintegral_ofReal_pow
    {f : Ω → ℝ} (hf_nn : ∀ ω, 0 ≤ f ω) (hf_meas : AEStronglyMeasurable f μ)
    {p : ℝ} (hp : 1 < p) :
    eLpNorm f (ENNReal.ofReal p) μ
      = (∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ) ^ (1 / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_ne_zero : (ENNReal.ofReal p) ≠ 0 := by
    simp [hp_pos]
  have hp_ne_top : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top hf_meas]
  rw [ENNReal.toReal_ofReal hp_pos.le]
  congr 1
  apply lintegral_congr_ae
  filter_upwards with ω
  have : ‖f ω‖ₑ = ENNReal.ofReal (f ω) := by
    rw [Real.enorm_eq_ofReal (hf_nn ω)]
  rw [this, ENNReal.ofReal_rpow_of_nonneg (hf_nn ω) hp_pos.le]

/-- Auxiliary finiteness lemma: if `∫⁻ (f n)^p ∂μ < ∞` for a non-negative submartingale
`f`, then `∫⁻ (max_{k ≤ n} f_k)^p ∂μ < ∞` as well. Derived from the truncated Hölder
bound by taking the monotone supremum over the truncation level. -/
lemma runMax_pow_lintegral_lt_top
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω) (hp : 1 < p) (n : ℕ)
    (hB_lt_top : ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ < ⊤) :
    ∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ < ⊤ := by
  set A : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ with hA_def
  set B : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ with hB_def
  set C : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1)) with hC_def
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  have hp_inv_pos : 0 < 1 / p := by positivity
  have hpm1_p_pos : 0 < (p - 1) / p := div_pos hpm1_pos hp_pos
  have hp_ne_zero : p ≠ 0 := hp_pos.ne'
  have h_sum_inv : (1 : ℝ) / p + (p - 1) / p = 1 := by
    rw [← add_div, show (1 : ℝ) + (p - 1) = p by ring, div_self hp_ne_zero]
  have h_prod_p : (1 : ℝ) / p * p = 1 := by field_simp
  have hC_lt_top : C < ⊤ := by
    rw [hC_def]
    exact ENNReal.ofReal_lt_top
  have hRHS_lt_top : C * B ^ (1 / p) < ⊤ :=
    ENNReal.mul_lt_top hC_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hp_inv_pos.le hB_lt_top.ne)
  have hRHS_p_lt_top : (C * B ^ (1 / p)) ^ p < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg hp_pos.le hRHS_lt_top.ne
  -- For each K > 0: ∫ (min M* K)^p ≤ (C · B^{1/p})^p, finite and independent of K.
  have h_AK_bounded : ∀ (K : ℝ), 0 < K →
      (∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ)
        ≤ (C * B ^ (1 / p)) ^ p := by
    intro K hK
    have hAK_bound := holder_step_truncated hsub hnonneg hp n K hK
    set A_K : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ
        with hAK_def
    have hA_K_lt_top : A_K < ⊤ := by
      rw [hAK_def]
      calc ∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ
          ≤ ∫⁻ _ : Ω, ENNReal.ofReal (K ^ p) ∂μ :=
            lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal
              (Real.rpow_le_rpow (le_min (runMax_nonneg hnonneg n ω) hK.le)
                (min_le_right _ _) hp_pos.le)
        _ = ENNReal.ofReal (K ^ p) * μ Set.univ := lintegral_const _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ)
    have h_inv_bound : A_K ^ (1 / p) ≤ C * B ^ (1 / p) := by
      by_cases hA_K_zero : A_K = 0
      · rw [hA_K_zero, ENNReal.zero_rpow_of_pos hp_inv_pos]
        exact bot_le
      have hAKpm1_ne_zero : A_K ^ ((p - 1) / p) ≠ 0 :=
        fun h ↦ hA_K_zero (ENNReal.rpow_eq_zero_iff_of_pos hpm1_p_pos |>.mp h)
      have hAKpm1_ne_top : A_K ^ ((p - 1) / p) ≠ ⊤ := fun h ↦
        hA_K_lt_top.ne ((ENNReal.rpow_eq_top_iff_of_pos hpm1_p_pos).mp h)
      have h_split : A_K ^ (1 / p) = A_K / A_K ^ ((p - 1) / p) := by
        rw [eq_div_iff hAKpm1_ne_zero hAKpm1_ne_top, mul_comm,
            ← ENNReal.rpow_add_of_nonneg (1/p) ((p-1)/p) hp_inv_pos.le hpm1_p_pos.le,
            h_sum_inv, ENNReal.rpow_one]
      rw [h_split, ENNReal.div_le_iff hAKpm1_ne_zero hAKpm1_ne_top]
      exact hAK_bound
    calc A_K = A_K ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ = (A_K ^ (1 / p)) ^ p := by rw [← ENNReal.rpow_mul, h_prod_p]
      _ ≤ (C * B ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow h_inv_bound hp_pos.le
  -- A = ⨆_K A_K (monotone convergence; min(M*, K+1) ↑ M* as K → ∞).
  have h_iSup : (⨆ K : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) ((K : ℝ) + 1)) ^ p) ∂μ) = A := by
    rw [hA_def, ← lintegral_iSup]
    · refine lintegral_congr_ae (Filter.Eventually.of_forall fun ω ↦ le_antisymm ?_ ?_)
      · refine iSup_le fun K ↦ ENNReal.ofReal_le_ofReal ?_
        exact Real.rpow_le_rpow (le_min (runMax_nonneg hnonneg n ω) (by positivity))
          (min_le_left _ _) hp_pos.le
      · obtain ⟨K₀, hK₀⟩ := exists_nat_gt (runMax f n ω)
        refine le_iSup_of_le K₀ (ENNReal.ofReal_le_ofReal ?_)
        refine Real.rpow_le_rpow (runMax_nonneg hnonneg n ω) ?_ hp_pos.le
        exact le_min le_rfl (by linarith)
    · intro K
      exact (((runMax_measurable hsub n).min measurable_const).pow_const p).ennreal_ofReal
    · intro a b hab ω
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
        (le_min (runMax_nonneg hnonneg n ω) (by positivity)) ?_ hp_pos.le)
      refine min_le_min le_rfl ?_
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
  -- A ≤ (C · B^{1/p})^p < ⊤.
  have h_A_le : A ≤ (C * B ^ (1 / p)) ^ p :=
    h_iSup ▸ iSup_le fun K ↦ h_AK_bounded ((K : ℝ) + 1) (by positivity)
  exact lt_of_le_of_lt h_A_le hRHS_p_lt_top

/-- Doob's L^p maximal inequality for discrete-time non-negative submartingales.

For a non-negative submartingale `f : ℕ → Ω → ℝ` and `1 < p`, the L^p norm
of the running maximum `f*_n(ω) = max_{k ≤ n} f_k(ω)` is bounded by
`(p / (p - 1))` times the L^p norm of `f_n`:

  `‖f*_n‖_{L^p} ≤ (p / (p - 1)) · ‖f_n‖_{L^p}`.

This is the strong-type companion to `MeasureTheory.maximal_ineq`. The proof
combines a layer-cake decomposition, the weak-type maximal inequality, Fubini,
Hölder's inequality, and a truncation argument to handle the case where the
left-hand side could a priori be infinite. -/
theorem maximal_ineq_Lp
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ f k ω)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) *
          eLpNorm (f n) (ENNReal.ofReal p) μ := by
  -- `Finset.sup'` is definitionally `runMax f n`.
  change eLpNorm (runMax f n) (ENNReal.ofReal p) μ ≤ _
  rw [eLpNorm_eq_lintegral_ofReal_pow (runMax_nonneg hnonneg n)
        (runMax_measurable hsub n).aestronglyMeasurable hp,
      eLpNorm_eq_lintegral_ofReal_pow (hnonneg n)
        (((hsub.stronglyMeasurable n).mono (𝒢.le n)).aestronglyMeasurable) hp]
  set A : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ
  set B : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ
  set C : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1)) with hC_def
  have hbound : A ≤ C * B ^ (1 / p) * A ^ ((p - 1) / p) := holder_step hsub hnonneg hp n
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_inv_pos : 0 < 1 / p := by positivity
  have hpm1_p_pos : 0 < (p - 1) / p := div_pos (by linarith) hp_pos
  -- Degenerate cases first.
  by_cases hA0 : A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos hp_inv_pos]
    exact bot_le
  by_cases hAtop : A = ⊤
  · by_cases hBtop : B = ⊤
    · -- Both sides `⊤` since `C ≠ 0`.
      have hC_ne_zero : C ≠ 0 := by
        rw [hC_def]
        exact (ENNReal.ofReal_pos.mpr (div_pos hp_pos (by linarith))).ne'
      rw [hAtop, hBtop, ENNReal.top_rpow_of_pos hp_inv_pos, ENNReal.mul_top hC_ne_zero]
    · -- `A = ⊤` while `B < ⊤` contradicts the finiteness lemma.
      exact absurd hAtop (runMax_pow_lintegral_lt_top hsub hnonneg hp n
        (lt_of_le_of_ne le_top hBtop)).ne
  -- Main case `0 < A < ⊤`: divide `hbound` by `A^{(p-1)/p}`.
  have hApm1_ne_zero : A ^ ((p - 1) / p) ≠ 0 :=
    fun h ↦ hA0 (ENNReal.rpow_eq_zero_iff_of_pos hpm1_p_pos |>.mp h)
  have hApm1_ne_top : A ^ ((p - 1) / p) ≠ ⊤ :=
    fun h ↦ hAtop ((ENNReal.rpow_eq_top_iff_of_pos hpm1_p_pos).mp h)
  have h_sum : (1 : ℝ) / p + (p - 1) / p = 1 := by
    rw [← add_div, show (1 : ℝ) + (p - 1) = p by ring, div_self hp_pos.ne']
  have h_split : A ^ (1 / p) = A / A ^ ((p - 1) / p) := by
    rw [eq_div_iff hApm1_ne_zero hApm1_ne_top, mul_comm,
        ← ENNReal.rpow_add_of_nonneg (1/p) ((p-1)/p) hp_inv_pos.le hpm1_p_pos.le,
        h_sum, ENNReal.rpow_one]
  rw [h_split, ENNReal.div_le_iff hApm1_ne_zero hApm1_ne_top]
  exact hbound

/-- The norm process of a Banach-valued martingale is a non-negative submartingale.
Internal lemma used to derive the Banach version of Doob's L^p inequality from the
real-valued case via Jensen (`MeasureTheory.norm_condExp_le`). -/
lemma martingale_norm_submartingale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → E} (hf : Martingale f 𝒢 μ) :
    Submartingale (fun n ω ↦ ‖f n ω‖) 𝒢 μ := by
  refine ⟨fun n ↦ continuous_norm.comp_stronglyMeasurable (hf.stronglyAdapted n),
          fun i j hij ↦ ?_, fun n ↦ (hf.integrable n).norm⟩
  have hcondExp : f i =ᵐ[μ] μ[f j | (𝒢 i : MeasurableSpace Ω)] := (hf.condExp_ae_eq hij).symm
  filter_upwards [hcondExp,
    norm_condExp_le (f := f j) (m := (𝒢 i : MeasurableSpace Ω)) (μ := μ)]
    with ω hω hjensen
  calc ‖f i ω‖ = ‖(μ[f j | (𝒢 i : MeasurableSpace Ω)]) ω‖ := by rw [hω]
    _ ≤ _ := hjensen

/-- Doob's L^p maximal inequality, Banach-valued martingale form.

For a Banach-valued martingale `f : ℕ → Ω → E` and `1 < p`,
`‖max_{k ≤ n} ‖f_k‖‖_{L^p} ≤ (p / (p - 1)) · ‖f_n‖_{L^p}`.

Derived from `MeasureTheory.maximal_ineq_Lp` by applying it to the non-negative
real-valued submartingale `‖f‖`. -/
theorem martingale_eLpNorm_runMax_norm_le
    [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → E} {p : ℝ}
    (hf : Martingale f 𝒢 μ) (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ ‖f k ω‖)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) * eLpNorm (f n) (ENNReal.ofReal p) μ := by
  have hsub := martingale_norm_submartingale hf
  have hbound := maximal_ineq_Lp hsub (fun _ _ ↦ norm_nonneg _) hp n
  rwa [eLpNorm_norm (f n)
    (((hf.stronglyMeasurable n).mono (𝒢.le n)).aestronglyMeasurable)] at hbound
end BlockBand.SourceProcess.Stochastic.SDE.DoobLp
