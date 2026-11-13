module

public import BlockBand.Palm.MomentFlow.BridgeLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Disintegrating a good event over the path σ-algebra

*Measure:* any probability measure for the first result, `flowLaw N a` for the second.

* `condExp_indicator_compl_small` (any probability space, sub-σ-algebra `m`, measurable `A`,
  `t > 0`): the `m`-measurable set `B = {t ≤ E[1_{Aᶜ} | m]}` has `P(B) ≤ P(Aᶜ)/t`, and off `B`,
  `E[1_{Aᶜ} | m] < t` (for the canonical version `condExp`).
* `pathSigma_disintegrate`: the same along the flow with `m = pathSigma F a s c`, in the form
  "`P(Aᶜ) ≤ N^{-2D}` gives an `𝓛`-set of probability `≤ N^{-D}` off which `P(Aᶜ|𝓛) < N^{-D}`".
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem condExp_indicator_compl_small {Ω : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hm : m ≤ m0) {A : Set Ω} (hA : MeasurableSet A)
    {t : ℝ} (ht : 0 < t) :
    ∃ B : Set Ω, MeasurableSet[m] B ∧ μ.real B ≤ μ.real Aᶜ / t ∧
      ∀ ω ∉ B, (μ[Aᶜ.indicator (fun _ => (1 : ℝ)) | m]) ω < t := by
  set f := μ[Aᶜ.indicator (fun _ => (1 : ℝ)) | m]
  have hfm : Measurable[m] f := stronglyMeasurable_condExp.measurable
  refine ⟨{ω | t ≤ f ω}, measurableSet_le measurable_const hfm, ?_, fun ω hω => not_le.1 hω⟩
  have hint : Integrable (Aᶜ.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hA.compl
  have hnn : 0 ≤ᵐ[μ] f := condExp_nonneg (Filter.Eventually.of_forall fun ω => by
    by_cases h : ω ∈ Aᶜ <;> simp [h])
  have hmk := mul_meas_ge_le_integral_of_nonneg hnn integrable_condExp t
  rw [integral_condExp hm] at hmk
  have hi : ∫ ω, Aᶜ.indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real Aᶜ := by
    rw [integral_indicator hA.compl]; simp
  rw [hi] at hmk
  rw [le_div_iff₀ ht, mul_comm]
  exact hmk

/-- **Disintegration along the flow.** If `P(Aᶜ) ≤ N^{-2D}`, there is an `𝓛`-measurable `B` with
`P(B) ≤ N^{-D}` and `P(Aᶜ | 𝓛) < N^{-D}` off `B`. -/
theorem pathSigma_disintegrate (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (hN : 0 < N) (D : ℝ)
    {A : Set (FlowSample N)} (hA : MeasurableSet A)
    (hAc : (flowLaw N a).real Aᶜ ≤ (N : ℝ) ^ (-(2 * D))) :
    ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a s c] B ∧
      (flowLaw N a).real B ≤ (N : ℝ) ^ (-D) ∧
      ∀ ω ∉ B, ((flowLaw N a)[Aᶜ.indicator (fun _ => (1 : ℝ)) | pathSigma F a s c]) ω <
        (N : ℝ) ^ (-D) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
  obtain ⟨B, hB, hμB, hoff⟩ := condExp_indicator_compl_small (μ := flowLaw N a)
    (pathSigma_le F a s c) hA ht
  refine ⟨B, hB, hμB.trans ?_, hoff⟩
  rw [div_le_iff₀ ht, ← Real.rpow_add hNp]
  convert hAc using 2; ring

end BlockBand.Palm.MomentFlow
