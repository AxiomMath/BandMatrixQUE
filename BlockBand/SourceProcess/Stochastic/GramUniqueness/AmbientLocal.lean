module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.MartingaleTools
public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblemConverse
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Step 9 bridge, part 2: re-stopping a localized martingale under domination

`hasMartingaleModification_stopped_of_localized`: if `X^{τ_n}` has a martingale modification
for a localizing sequence `τ_n → ⊤`, `X` has a.s. continuous paths, `ρ` is a stopping time and
`X^ρ` is a.s. bounded on bounded time intervals, then `X^ρ` has a martingale modification
(optional stopping `exists_martingale_stoppedProcess`, then
`hasMartingaleModification_of_localized`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem hasMartingaleModification_stopped_of_localized {X : ℝ≥0 → Ω → ℝ}
    {τ : ℕ → Ω → WithTop ℝ≥0} {ρ : Ω → WithTop ℝ≥0}
    (hτ : ∀ᵐ ω ∂Q, Tendsto (fun n => τ n ω) atTop (𝓝 ⊤))
    (hloc : ∀ n, HasMartingaleModification Q 𝓖 (stoppedProcess X (τ n)))
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω) (hρ : IsStoppingTime 𝓖 ρ)
    (hbd : ∀ t, ∃ C, ∀ᵐ ω ∂Q, ∀ s ≤ t, |stoppedProcess X ρ s ω| ≤ C) :
    HasMartingaleModification Q 𝓖 (stoppedProcess X ρ) := by
  refine BlockBand.SourceProcess.Stochastic.Bridges.hasMartingaleModification_of_localized hτ
    (fun n => ?_) hbd
  obtain ⟨M, hM, hMX⟩ := hloc n
  have hcn : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess X (τ n) t ω := by
    filter_upwards [hc] with ω h
    exact h.comp (continuous_stopTime _)
  obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM hMX hcn hρ
  refine ⟨M', hM', fun t => ?_⟩
  rw [stoppedProcess_stoppedProcess, inf_comm, ← stoppedProcess_stoppedProcess]
  exact hM'X t

end BlockBand.SourceProcess.Stochastic.GramUniqueness
