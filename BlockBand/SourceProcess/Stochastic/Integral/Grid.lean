module
public import BlockBand.SourceProcess.Stochastic.Integral.Family
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Stopping at grid-valued augmented stopping times

Measure `driverLaw μ`, augmented filtration `F_t ∨ N`, integrand space `PredictableFamily T`.
Let `ρ` be a finite random time with values in the grid `h ℕ` such that every
`{ρ ≤ N h}` is an augmented `F_{N h}` event. For an integrand `g` with draft continuous
representative `X = nativeAdaptedLimit μ T g`, and every `N`, the stopped integrand
`g · 1{s ≤ ρ ∧ N h}` is a.e. the representative of a predictable family whose terminal
integral is `X_{ρ ∧ N h}` a.s. Induction on `N`: the new layer is the adapted rectangle
`(N h, (N+1) h] × {ρ > N h}`, handled by `fullNativeIntegral_indicator_rectangle` after
replacing the augmented event by a raw one (`exists_raw_ae_eq`).
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

/-- A grid value strictly above `N h` is at least `(N+1) h`. -/
theorem grid_succ_le {h y : ℝ≥0} {m N : ℕ} (hy : y = m * h) (hlt : ¬ y ≤ N * h) :
    ((N + 1 : ℕ) : ℝ≥0) * h ≤ y := by
  have hNm : N < m := by
    have h1 : (N : ℝ≥0) * h < m * h := by rw [← hy]; exact lt_of_not_ge hlt
    exact_mod_cast lt_of_mul_lt_mul_right h1 (zero_le : (0 : ℝ≥0) ≤ h)
  rw [hy]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hNm) (zero_le : (0 : ℝ≥0) ≤ h)

variable [DecidableEq κ]

/-- **Grid stopping identity** (induction on the number of grid steps). -/
theorem stopped_grid_identity {g : κ → ℝ × DriverSample S κ → ℝ} (hg : NativeIntegrand μ T g)
    {h : ℝ≥0} {ρ : DriverSample S κ → ℝ≥0} (hgrid : ∀ x, ∃ m : ℕ, ρ x = m * h)
    (hρ : ∀ N : ℕ, MeasurableSet[driverAugmented (κ := κ) μ (N * h)] {x | ρ x ≤ N * h})
    (N : ℕ) :
    ∃ F : PredictableFamily (S := S) (κ := κ) (μ := μ) T,
      (∀ a, (((F a : ScalarPredictable (κ := κ) μ T) :
        Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ)
          =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)]
          stopFn (fun x => min (ρ x) (N * h)) g a) ∧
      (fullNativeIntegral (κ := κ) μ T F : DriverSample S κ → ℝ) =ᵐ[driverLaw (κ := κ) μ]
        fun x => nativeAdaptedLimit μ T hg.family (min (ρ x) (N * h)) x := by
  induction N with
  | zero =>
    refine ⟨0, fun a => ?_, ?_⟩
    · filter_upwards [Lp.coeFn_zero ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)),
        timeProbMeasure_horizon (κ := κ) μ T] with p h0 hp
      change ((0 : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) :
        ℝ × DriverSample S κ → ℝ) p = _
      rw [h0]
      have hn : ¬ p.1.toNNReal ≤ min (ρ p.2) ((0 : ℕ) * h) := by
        rw [Nat.cast_zero, zero_mul, min_eq_right zero_le, Real.toNNReal_le_iff_le_coe]
        exact not_le.2 hp.1
      simp only [stopFn, hn, ite_false, Pi.zero_apply]
    · rw [map_zero]
      filter_upwards [Lp.coeFn_zero ℝ 2 (driverLaw (κ := κ) μ)] with x hx
      rw [hx, Nat.cast_zero, zero_mul, min_eq_right zero_le,
        nativeAdaptedLimit_initial]
  | succ N ih =>
    obtain ⟨F, hF, hI⟩ := ih
    have hab : (N : ℝ≥0) * h ≤ ((N + 1 : ℕ) : ℝ≥0) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast N.le_succ) (zero_le : (0 : ℝ≥0) ≤ h)
    obtain ⟨B, hB, hBae⟩ := exists_raw_ae_eq μ (hρ N).compl
    have hBx : ∀ᵐ x ∂driverLaw (κ := κ) μ, (x ∈ B ↔ ¬ ρ x ≤ N * h) := by
      filter_upwards [hBae] with x hx
      rw [← hx]
      rfl
    have hR := measurableSet_predictableRectangle enlargedPredictableFiltration
      (t := ((N + 1 : ℕ) : ℝ≥0) * h) hB
    refine ⟨F + indicatorFamily _ hR hg.family, fun c => ?_, ?_⟩
    · have hsum : (((F + indicatorFamily _ hR hg.family) c : ScalarPredictable (κ := κ) μ T) :
          Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) =
          ((F c : ScalarPredictable (κ := κ) μ T) :
            Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) +
          ((indicatorScalar _ hR (hg.family c) : ScalarPredictable (κ := κ) μ T) :
            Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) := rfl
      rw [hsum]
      filter_upwards [Lp.coeFn_add ((F c : ScalarPredictable (κ := κ) μ T) :
          Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)))
          ((indicatorScalar _ hR (hg.family c) : ScalarPredictable (κ := κ) μ T) :
            Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))),
        hF c, indicatorScalar_coeFn _ hR (hg.family c), nativeIntegrand_family_coeFn hg c,
        timeProbMeasure_horizon (κ := κ) μ T, ae_timeProb_of_ae (T := T) hBx]
        with p h1 h2 h3 h4 _ h6
      rw [h1, Pi.add_apply, h2, h3]
      obtain ⟨m, hm⟩ := hgrid p.2
      by_cases hy : ρ p.2 ≤ N * h
      · have hpR : p ∉ Set.Ioc ((N * h : ℝ≥0) : ℝ) ((((N + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) : ℝ) ×ˢ B :=
          fun hp => (h6.1 hp.2) hy
        rw [Set.indicator_of_notMem hpR, add_zero]
        simp only [stopFn, min_eq_left hy, min_eq_left (hy.trans hab)]
      · have hb := grid_succ_le hm hy
        have hpB : p.2 ∈ B := h6.2 hy
        simp only [stopFn, min_eq_right (le_of_not_ge hy), min_eq_right hb,
          Real.toNNReal_le_iff_le_coe]
        by_cases hra : p.1 ≤ ((N * h : ℝ≥0) : ℝ)
        · have hrb : p.1 ≤ ((((N + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) : ℝ) :=
            hra.trans (by exact_mod_cast hab)
          have hpR : p ∉ Set.Ioc ((N * h : ℝ≥0) : ℝ)
              ((((N + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) : ℝ) ×ˢ B :=
            fun hp => not_lt_of_ge hra hp.1.1
          rw [Set.indicator_of_notMem hpR, ite_eq_left hra, ite_eq_left hrb, add_zero]
        · rw [ite_eq_right hra, zero_add]
          by_cases hrb : p.1 ≤ ((((N + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) : ℝ)
          · have hpR : p ∈ Set.Ioc ((N * h : ℝ≥0) : ℝ)
                ((((N + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) : ℝ) ×ˢ B :=
              ⟨⟨lt_of_not_ge hra, hrb⟩, hpB⟩
            rw [Set.indicator_of_mem hpR, ite_eq_left hrb, h4]
          · have hpR : p ∉ Set.Ioc ((N * h : ℝ≥0) : ℝ)
                ((((N + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) : ℝ) ×ˢ B :=
              fun hp => hrb hp.1.2
            rw [Set.indicator_of_notMem hpR, ite_eq_right hrb]
    · rw [map_add]
      filter_upwards [Lp.coeFn_add (fullNativeIntegral (κ := κ) μ T F)
          (fullNativeIntegral (κ := κ) μ T (indicatorFamily _ hR hg.family)), hI,
        fullNativeIntegral_indicator_rectangle μ T hg.family hab hB, hBx] with x h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, h3]
      obtain ⟨m, hm⟩ := hgrid x
      by_cases hy : ρ x ≤ N * h
      · rw [Set.indicator_of_notMem (fun hx => h4.1 hx hy), add_zero, min_eq_left hy,
          min_eq_left (hy.trans hab)]
      · rw [Set.indicator_of_mem (h4.2 hy), min_eq_right (le_of_not_ge hy),
          min_eq_right (grid_succ_le hm hy)]
        ring

end BlockBand.SourceProcess.Stochastic.Integral
