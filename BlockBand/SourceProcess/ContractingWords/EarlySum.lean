module

public import BlockBand.SourceProcess.ContractingWords.EarlyPins
public import BlockBand.SourceProcess.ContractingWords.SummedField
public import BlockBand.SourceProcess.ContractingWords.Main
public import BlockBand.SourceProcess.FullSourceGenerator.Interface

/-!
# `FullSourceGenerator.EarlySummed` from `SummedStepAll`

**`earlySummed_of (hS : SummedStepAll) : EarlySummed`.** Fix `b`, `-2 < E < 2` and take the
bulk margin `κI = min(E + 2, 2 - E)` (`mem_bulk_self`), so that `E ∈ bulkInterval κI`; every
constant of `SummedStepAll` is chosen from `κI`, before `W`. For a window start `j₀ ≥ εW` with all
births `k_a < j₀`, every step `j₀ ≤ j < ⌊TW⌋` has `εW ≤ j`, `j ≠ k_a` and `j + 1 ≤ TW`, so the
per-step errors `CW⁻¹(ρ^{j-r_j} + W^{-1/2})` apply. The lemma `sum_err_le` sums
them: `≤ (C(n_T+1)/(1-ρ) + CT)(W^{-1/2} + W⁻¹)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- **`EarlySummed`** from the per-step bound with any births. -/
theorem earlySummed_of (hS : SummedStepAll) : FullSourceGenerator.EarlySummed := by
  intro b hb0 hb E hE1 hE2 nT nI q hq Φ hΦ ε T K hε hεT
  obtain ⟨hκ, hEκ⟩ := mem_bulk_self hE1 hE2
  obtain ⟨C, ρ, W₀, hC, hρ0, hρ1, hstep⟩ :=
    hS b hb0 hb (min (E + 2) (2 - E)) hκ nT nI q hq Φ hΦ ε T K hε hεT
  have hT : 0 < T := lt_trans hε hεT
  refine ⟨C * (nT + 1) / (1 - ρ) + C * T, max W₀ 1, fun W hW k j₀ hj₀ hkj₀ => ?_⟩
  intro μ A F steps
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hTW : 0 ≤ T * W := by positivity
  have hmem : ∀ j ∈ steps, ε * W ≤ (j : ℝ) ∧ (∀ a, j ≠ k a) ∧ ((j + 1 : ℕ) : ℝ) ≤ T * W := by
    intro j hj
    obtain ⟨hjr, h1⟩ := Finset.mem_filter.mp hj
    refine ⟨hj₀.trans (by exact_mod_cast h1), fun a => ?_, le_trans ?_ (Nat.floor_le hTW)⟩
    · have := hkj₀ a; omega
    · exact_mod_cast Finset.mem_range.mp hjr
  have hceil : ∀ j ∈ steps, ⌈ε * W⌉₊ ≤ j := fun j hj => Nat.ceil_le.mpr (hmem j hj).1
  have hcard : (steps.card : ℝ) ≤ T * W := by
    have h1 : steps.card ≤ ⌊T * W⌋₊ :=
      (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le hTW)
  have hsum := sum_err_le hC hρ0 hρ1 hT hW1 k steps hceil hcard
  have herr0 : ∀ j ∈ steps, 0 ≤ C / W * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W) :=
    fun j _ => by positivity
  have hfin : ∑ j ∈ steps,
      ENNReal.ofReal (C / W * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W)) ≤
        ENNReal.ofReal ((C * (nT + 1) / (1 - ρ) + C * T) * (1 / Real.sqrt W + 1 / W)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg herr0]; exact ENNReal.ofReal_le_ofReal hsum
  refine ⟨le_trans (Finset.sum_le_sum fun j hj => ?_) hfin,
    le_trans (Finset.sum_le_sum fun j hj => ?_) hfin⟩
  · obtain ⟨h1, h2, h3⟩ := hmem j hj
    exact (hstep W (le_of_max_le_left hW) E hEκ k j h1 h2 h3).1
  · obtain ⟨h1, h2, h3⟩ := hmem j hj
    exact (hstep W (le_of_max_le_left hW) E hEκ k j h1 h2 h3).2

end BlockBand.SourceProcess.ContractingWords
