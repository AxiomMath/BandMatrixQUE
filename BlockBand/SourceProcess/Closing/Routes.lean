module

public import BlockBand.SourceProcess.Closing.Defs

/-!
# Two further hypotheses toward `ClosingLeakage`

* `ClosedReflection`: for the path closed at time `s`, the omitted block satisfies `N^n → 0`
  almost surely for all large `W` (proved as `closedReflection_holds`).
* `SmallChannelLeakage`: the expected source trace leaked into the omitted far inputs is small for
  small cutoffs, for all large `W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Closing

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath

/-- **`‖r‖ < 1` for the finite path**, in the form used by
`ae_phaseAvg_physClosingDefect`: for all large `W`, almost surely the omitted block
`N = Π𝕊A` of the path closed at time `s` has `N^n → 0`. -/
def ClosedReflection : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T h : ℝ, 0 < s → s < T →
    0 < h → h < 1 → ∀ᶠ W in atTop, ∀ᵐ ω ∂growthPathLaw W b,
      Tendsto (fun n => closingN (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)
        (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
        (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)) ^ n) atTop (𝓝 0)

/-- **Small-channel leakage**: the expected final source trace leaked
into the omitted far inputs, `E Tr(Q(q)(T) A_-)`, is small for small cutoffs, for all large `W`
(`lim_{cutoff} limsup_W E Tr(Q(T)A_-) = 0`). -/
def SmallChannelLeakage : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ q : ℝ → ℝ, IsSourceTest s T q → ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᶠ W in atTop,
      ∫ ω, (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
        intervalSource b E W ⌊(W : ℝ) * T⌋₊ q ω).trace.re ∂growthPathLaw W b ≤ ε

end BlockBand.SourceProcess.Closing
