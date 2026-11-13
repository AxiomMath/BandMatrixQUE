module

public import BlockBand.SourceProcess.ContractingWords.PathStepAll
public import BlockBand.SourceProcess.ContractingWords.SummedPath
public import BlockBand.SourceProcess.ContractingWords.SummedPins
public import BlockBand.SourceProcess.ContractingWords.Alive

/-!
# Conditional increments of words as one-layer integrals

The conditional increment of a word on the survival event is an integral over the fresh layer.

At a step `j → j+1` with `1 ≤ j` and no birth at `j`, with `A = {j < σ_K}` and `F_j = growthSigma W j`:
* `incΨ u`: the increment `Δ_u = Tr u(j+1) - Tr u(j)` as a measurable function of
  (past, fresh layer); `ae_wordInc_eq`: `Δ_u = incΨ u (past, fresh)` a.s., for all words `u`;
* `incΨ_past`: at the past of `ω`, `incΨ u (past ω, y) = newWord(state of ω, y) - Tr u(j)(ω)`;
* `condExp_alive_eq`: `E[1_A f | F_j] = 1_A ∫ Ψ(past ω, y) dy` a.s. whenever `f = Ψ(past, fresh)`
  a.s. with `Ψ` measurable and `f` integrable (`condExp_past_fresh` and the pull-out of
  the past indicator).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar

variable {W nT nI : ℕ}

/-- The increment of a word as a function of (past, fresh layer). -/
def incΨ (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ) (u : TraceWord nT nI)
    (z : PastSample W j × LayerSample W .oneBlockOnePort) : ℂ :=
  stateΨ b E k q W j [u] z - productValue b E k q W j (extPast W j z.1) [u]

theorem measurable_incΨ (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (u : TraceWord nT nI) : Measurable (incΨ b E k q W j u) :=
  (measurable_stateΨ b E k q j [u]).sub
    ((measurable_productValue b E k q j [u]).comp ((measurable_extPast j).comp measurable_fst))

theorem productValue_extPast (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (ω : GrowthPath W) (Zs : List (TraceWord nT nI)) :
    productValue b E k q W j (extPast W j (pastCoords W j ω)) Zs = productValue b E k q W j ω Zs := by
  unfold productValue
  rw [List.map_congr_left fun u _ => wordValue_congr b E k q j (pathAt_extPast_le le_rfl ω) u]

theorem incΨ_past (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ) (u : TraceWord nT nI)
    (ω : GrowthPath W) (y : LayerSample W .oneBlockOnePort) :
    incΨ b E k q W j u (pastCoords W j ω, y) =
      stateZ b E k q W j [u] ω y - productValue b E k q W j ω [u] := by
  simp only [incΨ, stateΨ, stateZ_extPast, productValue_extPast]

theorem ae_wordInc_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j)
    (hk : ∀ a, j ≠ k a) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ u : TraceWord nT nI,
      wordInc b E k q W j u ω = incΨ b E k q W j u (pastCoords W j ω, freshSample W j ω) := by
  filter_upwards [ae_step_state' hb0 hb hE1 hE2 hW k q] with ω h u
  rw [incΨ, ← (h j hj hk [u]).1, productValue_extPast]
  simp [productValue, wordInc]

/-- **The conditional mean on the survival event** as a fresh-layer integral. -/
theorem condExp_alive_eq (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (j : ℕ)
    {f : GrowthPath W → ℂ} (hf : Integrable f (growthPathLaw W b))
    {Ψ : PastSample W j × LayerSample W .oneBlockOnePort → ℂ} (hΨ : Measurable Ψ)
    (hfΨ : f =ᵐ[growthPathLaw W b] fun ω => Ψ (pastCoords W j ω, freshSample W j ω)) :
    (growthPathLaw W b)[(alive b E k q K ε W j).indicator f | growthSigma W j] =ᵐ[
      growthPathLaw W b] (alive b E k q K ε W j).indicator
        fun ω => ∫ y, Ψ (pastCoords W j ω, y) ∂freshLaw W b := by
  have h1 := condExp_indicator (m := growthSigma W j) hf (measurableSet_alive b E k q K ε j)
  have h2 := (condExp_congr_ae (m := growthSigma W j) hfΨ).trans
    (condExp_past_fresh b j hΨ (hf.congr hfΨ))
  refine h1.trans ?_
  filter_upwards [h2] with ω hω
  by_cases hA : ω ∈ alive b E k q K ε W j
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA, hω]
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]

end BlockBand.SourceProcess.ContractingWords
