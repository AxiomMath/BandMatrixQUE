module

public import BlockBand.SourceProcess.ContractingWords.SummedPins

/-!
# The per-word step bounds with early tag births

The generalized forms drop the hypothesis `∀ a, εW ≤ k_a` of `OrdinaryDriftStep`,
`OrdinaryCovStep` and `SummedStep`: tags may be born
at any index, including before `εW`. The window `εW ≤ j`, `j ≠ k_a`, `j + 1 ≤ TW` is kept.
All definitions involved make sense for early births: `alive` (the trace stop starts at `εW` and
reads `traceLoad`, which includes the tags born before `εW`), `restartIndex ε W k j =
max(⌈εW⌉, max{k_a + 1 : k_a < j})`, which is `⌈εW⌉` when every birth precedes it, and the word
values (`tagResponse W j (k a)` for any `k a`). This is the form needed by
`FullSourceGenerator.EarlySummed`.

The forms with `εW ≤ k_a` follow by specialization (`ordinaryDriftStep_of_all`,
`ordinaryCovStep_of_all`, `summedStep_of_all`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- **The first conditional increment of one ordinary word, any tag births.** -/
def OrdinaryDriftStepAll : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K : ℝ), 0 < ε → ε < T →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ,
      ∀ j : ℕ, ε * W ≤ j → (∀ a, j ≠ k a) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
      ∀ w : TraceWord nT nI, IsOrdinaryWord w → w.length ≤ d →
        eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
            (growthPathLaw W b)[(alive b E k q K ε W j).indicator (wordInc b E k q W j w) |
              growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordDrift (transportD0 b E) w +
              MvPolynomial.C (wordInjection b q (stepTime W j) w)))
          2 (growthPathLaw W b) ≤ ENNReal.ofReal (stepErr C ρ ε W k j)

/-- **The second conditional increment of a pair of ordinary words, any births.** -/
def OrdinaryCovStepAll : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K : ℝ), 0 < ε → ε < T →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ,
      ∀ j : ℕ, ε * W ≤ j → (∀ a, j ≠ k a) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
      ∀ w v : TraceWord nT nI, IsOrdinaryWord w → IsOrdinaryWord v → w.length ≤ d →
        v.length ≤ d →
        eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
            (growthPathLaw W b)[(alive b E k q K ε W j).indicator
              (fun ω => wordInc b E k q W j w ω * wordInc b E k q W j v ω) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCov (transportD0 b E) w v))
          2 (growthPathLaw W b) ≤ ENNReal.ofReal (stepErr C ρ ε W k j)

/-- The size of one increment, any births (proved in `ordinaryIncrementAll_holds`). -/
def OrdinaryIncrementAll : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ,
      ∀ j : ℕ, ε * W ≤ j → (∀ a, j ≠ k a) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
      ∀ w : TraceWord nT nI, IsOrdinaryWord w → w.length ≤ d →
        eLpNorm ((alive b E k q K ε W j).indicator (wordInc b E k q W j w)) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal (C / Real.sqrt W)

/-- **`SummedStep` with any tag births** (proved in `summedStepAll_of`). -/
def SummedStepAll : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ → ∀ ε T K : ℝ, 0 < ε → ε < T →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ,
      ∀ j : ℕ, ε * W ≤ j → (∀ a, j ≠ k a) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
      let μ := growthPathLaw W b
      let A := alive b E k q K ε W j
      let F : ℕ → GrowthPath W → ℂ := fun i ω => polyValue b E k q W i ω Φ
      let err : ℝ := C / W * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W)
      ∫⁻ ω, ‖A.indicator (fun ω =>
          μ[A.indicator (fun ω => F (j + 1) ω - F j ω) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω
              (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)) ω‖ₑ ∂μ ≤ ENNReal.ofReal err ∧
      ∫⁻ ω, ‖A.indicator (fun ω =>
          μ[A.indicator (fun ω => (F (j + 1) ω - F j ω) ^ 2) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Φ)) ω‖ₑ ∂μ ≤ ENNReal.ofReal err

/-- `OrdinaryDriftStep` is the specialization to `εW ≤ k_a`. -/
theorem ordinaryDriftStep_of_all (h : OrdinaryDriftStepAll) : OrdinaryDriftStep := by
  intro b hb0 hb κI hκ nT nI q hq d ε T K hε hεT
  obtain ⟨C, ρ, W₀, hC, hρ, hρ1, h'⟩ := h b hb0 hb κI hκ nT nI q hq d ε T K hε hεT
  exact ⟨C, ρ, W₀, hC, hρ, hρ1, fun W hW E hE k _ => h' W hW E hE k⟩

/-- `OrdinaryCovStep` is the specialization to `εW ≤ k_a`. -/
theorem ordinaryCovStep_of_all (h : OrdinaryCovStepAll) : OrdinaryCovStep := by
  intro b hb0 hb κI hκ nT nI q hq d ε T K hε hεT
  obtain ⟨C, ρ, W₀, hC, hρ, hρ1, h'⟩ := h b hb0 hb κI hκ nT nI q hq d ε T K hε hεT
  exact ⟨C, ρ, W₀, hC, hρ, hρ1, fun W hW E hE k _ => h' W hW E hE k⟩

/-- `SummedStep` is the specialization to `εW ≤ k_a`. -/
theorem summedStep_of_all (h : SummedStepAll) : SummedStep := by
  intro b hb0 hb κI hκ nT nI q hq Φ hΦ ε T K hε hεT
  obtain ⟨C, ρ, W₀, hC, hρ, hρ1, h'⟩ := h b hb0 hb κI hκ nT nI q hq Φ hΦ ε T K hε hεT
  exact ⟨C, ρ, W₀, hC, hρ, hρ1, fun W hW E hE k _ => h' W hW E hE k⟩

end BlockBand.SourceProcess.ContractingWords
