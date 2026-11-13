module

public import BlockBand.SourceProcess.Closing.Defs
public import BlockBand.SourceProcess.SourcePins.Freq

/-!
# Splitting `PhysicalApproximationFreq` into closing and identification

* `ClosingLeakage`: the small-channel leakage bound and the Gaussian closing error remove the
  physical closing error as `h ↓ 0`; at fixed `M`, eventually as `h ↓ 0`, eventually in `W`, the
  physical sampled transform is within `ε` of the closed one.
* `ClosedIdentification` (including the cap removal at the physical level): at fixed `M`,
  frequently as `h ↓ 0` (avoiding the countably many `h` with an entrance atom at `h²`) and
  frequently in the cap `K`, every finite-model value is eventually within `ε` of the closed
  transform.
* `physicalApproximationFreq_of_split`: the two together imply `PhysicalApproximationFreq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Closing

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw

/-- **Closing and leakage.** For each fixed
sample size `M` and `ε > 0`: for all small cutoffs `h > 0`, for all large `W`, closing the omitted
channels `t_i ≤ h²` at time `s` with a uniform phase changes the sampled physical transform by at
most `ε`. (The physical current carrier, the source leakage recursion and the small-channel
leakage bound control the expected leaked source trace `E Tr(Q(T)A_-)`; the Gaussian closing error
and the Lipschitz bound for `v ↦ e^{-‖v‖²}` convert it.) -/
def ClosingLeakage : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ M : ℕ, 0 < M → ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᶠ W in atTop,
      |sampledPhysTransform b E T q a M W - closedSampledTransform b E s T h q a M W| ≤ ε

/-- **Identification at fixed `M`**: at fixed `h, M` and a finite cap on the number of retained
modes, close the omitted channels and identify the physical finite-coordinate martingales with the
unique finite Gram law, then remove the cap. For each fixed `M` and `ε > 0`,
frequently as `h ↓ 0` and then frequently as the cap `K → ∞`, every model value at `(h, K, M)` with
the entrance `μ(s)` is, for all large `W`, within `ε` of the closed sampled transform. -/
def ClosedIdentification : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ M : ℕ, 0 < M → ∀ ε : ℝ, 0 < ε → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop, ∀ v : ℝ,
      FiniteSourceModelValue b E s T q h K M (entranceLaw P μ s) a v →
      ∀ᶠ W in atTop, |closedSampledTransform b E s T h q a M W - v| ≤ ε

/-- **`ClosingLeakage` and `ClosedIdentification` give `PhysicalApproximationFreq`.** -/
theorem physicalApproximationFreq_of_split (ha : ClosingLeakage) (hb : ClosedIdentification) :
    SourcePins.PhysicalApproximationFreq := by
  intro b hb0 hb1 E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha0 M hM ε hε
  have hA := ha b hb0 hb1 E hE1 hE2 s T hs hsT p q hq J a ha0 M hM (ε / 2) (by linarith)
  have hB := hb b hb0 hb1 E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha0 M hM (ε / 2)
    (by linarith)
  refine (hA.and_frequently hB).mono fun h ⟨hAh, hBh⟩ => hBh.mono fun K hK v hv => ?_
  filter_upwards [hAh, hK v hv] with W h1 h2
  calc |sampledPhysTransform b E T q a M W - v|
      ≤ |sampledPhysTransform b E T q a M W - closedSampledTransform b E s T h q a M W| +
        |closedSampledTransform b E s T h q a M W - v| := abs_sub_le _ _ _
    _ ≤ ε := by linarith

end BlockBand.SourceProcess.Closing
