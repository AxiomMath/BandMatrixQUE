module

public import BlockBand.Critical.RelativeVectors.Statement

/-!
# Removing a bad event conditionally on the path

* `exists_good_of_condExp_markov` (general): for a probability measure `μ`, a sub-σ-algebra
  `m`, a measurable event `A` with `μ(Aᶜ) ≤ ε²`, there is an `m`-measurable `𝒢` with
  `μ(𝒢ᶜ) ≤ ε` such that every `m`-measurable `B ⊆ 𝒢` has `μ(B ∩ Aᶜ) ≤ ε μ(B)`; this is the
  statement "`P(Aᶜ | m) ≤ ε` on `𝒢`" in the integrated form used by the main clause
  (`𝒢 = {μ[1_{Aᶜ} | m] ≤ ε}`, Markov for the conditional expectation).
* `step1_goodPaths`: the case `μ = flowLaw N a`, `m = pathSigma F a a c` (`𝓛`), `ε = N^{-D}`:
  an event of probability `≥ 1 - N^{-2D}` fails conditionally with probability `≤ N^{-D}` on
  `𝓛`-measurable good paths of probability `≥ 1 - N^{-D}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.MomentFlow

/-- **Conditional Markov removal of a bad event.** For a probability measure `μ`, a
sub-σ-algebra `m ≤ m₀`, a measurable `A` and `ε > 0` with `μ(Aᶜ) ≤ ε²`, there is an
`m`-measurable `𝒢` with `μ(𝒢ᶜ) ≤ ε` and `μ(B ∩ Aᶜ) ≤ ε μ(B)` for every `m`-measurable
`B ⊆ 𝒢`. -/
theorem exists_good_of_condExp_markov {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ m₀) {A : Set Ω} (hA : MeasurableSet A) {ε : ℝ}
    (hε : 0 < ε) (hAc : μ.real Aᶜ ≤ ε ^ 2) :
    ∃ 𝒢 : Set Ω, MeasurableSet[m] 𝒢 ∧ μ.real 𝒢ᶜ ≤ ε ∧
      ∀ B : Set Ω, MeasurableSet[m] B → B ⊆ 𝒢 → μ.real (B ∩ Aᶜ) ≤ ε * μ.real B := by
  have : SigmaFinite (μ.trim hm) := by
    have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  set f : Ω → ℝ := Aᶜ.indicator 1 with hfdef
  have hf : Integrable f μ := (integrable_const (1 : ℝ)).indicator hA.compl
  have hf0 : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun ω => by
    simp only [hfdef]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  set h := μ[f | m] with hhdef
  have hhm : Measurable[m] h := stronglyMeasurable_condExp.measurable
  have hh0 : 0 ≤ᵐ[μ] h := condExp_nonneg hf0
  have hhi : Integrable h μ := integrable_condExp
  have hsetf : ∀ B : Set Ω, MeasurableSet B → ∫ x in B, f x ∂μ = μ.real (B ∩ Aᶜ) := by
    intro B hB
    rw [hfdef, setIntegral_indicator hA.compl]
    simp [measureReal_def]
  refine ⟨h ⁻¹' Set.Iic ε, hhm measurableSet_Iic, ?_, ?_⟩
  · have hM := mul_meas_ge_le_integral_of_nonneg hh0 hhi ε
    rw [integral_condExp hm, ← setIntegral_univ, hsetf Set.univ MeasurableSet.univ,
      Set.univ_inter] at hM
    have hsub : (h ⁻¹' Set.Iic ε)ᶜ ⊆ {x | ε ≤ h x} := fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iic, not_le] at hx
      exact hx.le
    refine (measureReal_mono hsub).trans ?_
    have h2 : ε * μ.real {x | ε ≤ h x} ≤ ε * ε := hM.trans (by nlinarith)
    exact le_of_mul_le_mul_left h2 hε
  · intro B hB hBG
    rw [← hsetf B (hm B hB), ← setIntegral_condExp hm hf hB]
    have hle : ∫ x in B, h x ∂μ ≤ ∫ _x in B, ε ∂μ :=
      setIntegral_mono_on hhi.integrableOn (integrable_const ε).integrableOn (hm B hB)
        fun x hx => hBG hx
    rw [setIntegral_const, smul_eq_mul, mul_comm] at hle
    exact hle

/-- **Good eigenvalue paths.** Under `flowLaw N a`, with `𝓛 = pathSigma F a a c`: if a measurable
event `𝒜` (e.g. the interval and distant-label bounds throughout `[a, c]`) has `P(𝒜ᶜ) ≤ N^{-2D}`,
then there are `𝓛`-measurable good paths `𝒢` with `P(𝒢ᶜ) ≤ N^{-D}` such that
`P(B ∩ 𝒜ᶜ) ≤ N^{-D} P(B)` for every `𝓛`-measurable `B ⊆ 𝒢` (conditional failure of `𝒜` at most
`N^{-D}` on `𝒢`). `N ≥ 1`, any real `a, c, D`. -/
theorem step1_goodPaths {N : ℕ} (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) (a c D : ℝ)
    {𝒜 : Set (FlowSample N)} (h𝒜 : MeasurableSet 𝒜)
    (h𝒜c : (flowLaw N a).real 𝒜ᶜ ≤ (N : ℝ) ^ (-(2 * D))) :
    ∃ 𝒢 : Set (FlowSample N), MeasurableSet[pathSigma F a a c] 𝒢 ∧
      (flowLaw N a).real 𝒢ᶜ ≤ (N : ℝ) ^ (-D) ∧
      ∀ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B → B ⊆ 𝒢 →
        (flowLaw N a).real (B ∩ 𝒜ᶜ) ≤ (N : ℝ) ^ (-D) * (flowLaw N a).real B := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : ((N : ℝ) ^ (-D)) ^ 2 = (N : ℝ) ^ (-(2 * D)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]; congr 1; push_cast; ring
  exact exists_good_of_condExp_markov (pathSigma_le F a a c) h𝒜 (Real.rpow_pos_of_pos hNr _)
    (by rw [hsq]; exact h𝒜c)

end BlockBand.Critical.RelativeVectors
