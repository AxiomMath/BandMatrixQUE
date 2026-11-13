module

public import BlockBand.Critical.JointRecovery.ExtractionMeasurable

/-!
# Weak convergence passes to the extracted Laplace functional

`tendsto_extractorLaplace`: if laws `μ_j` of random entire functions carried by `goodEntire`
converge weakly to a law `μ` carried by `goodEntire`, and `t_j → τ > 0`, then the integrals of the
extraction integrand `extractionValue E t_j f` converge to `extractorLaplace E τ μ f`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set MeasureTheory
open BlockBand.Critical.Entire BlockBand.Critical.Entire.EntireFunction
open BlockBand.Internal.Contracts.CriticalEntire

variable {m : ℕ}

/-- **Convergence of the extracted Laplace functional.** -/
theorem tendsto_extractorLaplace {E τ : ℝ} (hρ : 0 < Parameters.semicircleDensity E)
    (hτ : 0 < τ) (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ)
    (hf : ∀ z, 0 ≤ f z) {μs : ℕ → RandomEntire (m + 1)} {μ : RandomEntire (m + 1)}
    {ts : ℕ → ℝ} (hμ : Tendsto μs atTop (𝓝 μ)) (hts : Tendsto ts atTop (𝓝 τ))
    (hts0 : ∀ j, 0 < ts j) (hgood : ∀ j, (μs j : Measure (EntireFunction (m + 1)))
      (goodEntire m)ᶜ = 0)
    (hlim : ∀ᵐ F ∂(μ : Measure (EntireFunction (m + 1))), F ∈ goodEntire m) :
    Tendsto (fun j => ∫ F, extractionValue E (ts j) f F ∂(μs j : Measure (EntireFunction (m + 1))))
      atTop (𝓝 (extractorLaplace E τ μ f)) := by
  have hprod := tendsto_diracProba_prod hts hμ
  have hmeas := measurable_extractionTest (m := m) hρ f
  have hS : ∀ j, (((diracProba (ts j)).prod (μs j) : ProbabilityMeasure _) :
      Measure (ℝ × EntireFunction (m + 1))) (goodPairs m)ᶜ = 0 := by
    intro j
    refine diracProba_prod_compl_eq_zero (ts j) (μs j) measurableSet_goodPairs ?_
    refine measure_mono_null (fun F hF => ?_) (hgood j)
    exact fun hg => hF ⟨hts0 j, hg⟩
  have hcont : ∀ᵐ p ∂(((diracProba τ).prod μ : ProbabilityMeasure _) :
      Measure (ℝ × EntireFunction (m + 1))), ContinuousWithinAt (extractionTest E f)
        (goodPairs m) p := by
    have hB : MeasurableSet (goodPairs m) := measurableSet_goodPairs
    have hnull : (((diracProba τ).prod μ : ProbabilityMeasure _) :
        Measure (ℝ × EntireFunction (m + 1))) (goodPairs m)ᶜ = 0 := by
      refine diracProba_prod_compl_eq_zero τ μ hB ?_
      have : {F : EntireFunction (m + 1) | (τ, F) ∉ goodPairs m} ⊆ {F | F ∉ goodEntire m} :=
        fun F hF hg => hF ⟨hτ, hg⟩
      exact measure_mono_null this (ae_iff.mp hlim)
    filter_upwards [compl_mem_ae_iff.mpr hnull] with p hp
    rw [compl_compl] at hp
    exact continuousWithinAt_extractionTest hρ f ⟨hp.1, hp.2.1.1, hp.2.2⟩
  have key := tendsto_integral_of_continuousWithinAt hprod hmeas
    (abs_extractionTest_le_one hf) hS hcont
  have hj : ∀ j, ∫ p, extractionTest E f p ∂(((diracProba (ts j)).prod (μs j) :
      ProbabilityMeasure _) : Measure (ℝ × EntireFunction (m + 1))) =
      ∫ F, extractionValue E (ts j) f F ∂(μs j : Measure (EntireFunction (m + 1))) := by
    intro j
    rw [integral_diracProba_prod (ts j) (μs j) hmeas]
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (hgood j)] with F hF
    rw [compl_compl] at hF
    exact extractionTest_of_mem ⟨hts0 j, hF⟩
  have h0 : ∫ p, extractionTest E f p ∂(((diracProba τ).prod μ :
      ProbabilityMeasure _) : Measure (ℝ × EntireFunction (m + 1))) =
      extractorLaplace E τ μ f := by
    rw [integral_diracProba_prod τ μ hmeas, extractorLaplace_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hlim] with F hF
    exact extractionTest_of_mem ⟨hτ, hF⟩
  simpa only [hj, h0] using key

end BlockBand.Critical.JointRecovery
