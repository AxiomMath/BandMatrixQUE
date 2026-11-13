module

public import BlockBand.Endpoints.Clock.DetClockStatement

/-!
# The open-inputs and deterministic-clock statements on compact parameter sets

The fixed-energy statements `OpenInputsMoments` and `DetClockEvolutionD` fix `(b, E)` before their
constants. The hypothesis `h1` of the Robin entrance lemma (`RobinEntrance.OpenClockLawUniformInitial`)
needs one `ε` for all `b ∈ [β, 1/2-β]` and `E ∈ bulkInterval κ`, and bounds along moving energies.
This file states the two compact-set forms and proves that each implies its fixed-energy version:
* `OpenInputsMomentsBulk`: the input moments of the open-inputs lemma. `ε` depends only on
  `(β, κ, T, q, p)`; `C, W₀` depend on `b` and are uniform in `E ∈ bulkInterval κ` and in
  Hermitian `‖D‖ ≤ ε`.
* `DetClockEvolutionDBulk`: the deterministic-clock lemma, uniform in Hermitian `X₀ = D` with
  `‖D‖ ≤ ε`, as in `DetClockEvolutionD`. `ε` depends only on `(β, κ, T, q)`; the majorants
  `δ_{W,j}` depend on `b` and `K` and are uniform in `E ∈ bulkInterval κ` and in `D`.

The conclusions are those of the fixed-energy statements; the parameters `β, κ` come first and
`E ∈ bulkInterval κ` comes after the constants.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

namespace MovingEnergy

/-- `b`-uniform `ε`, see the module
docstring)**.
`β, κ, T, q, p` first; then `ε > 0`; for each `b ∈ [β, 1/2-β]` there are `C, W₀`
such that for `W ≥ W₀`, every `E ∈ bulkInterval κ` and every Hermitian initial `X₀ = D` with
`‖D‖ ≤ ε` (operator norm;
-/
def OpenInputsMomentsBulk : Prop :=
  ∀ β κ : ℝ, 0 < β → β < 1 / 4 → 0 < κ → ∀ (T : ℝ) (q : ℝ → ℝ), IsClockWeight q →
    ∀ p : ℝ, 1 ≤ p → ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
          (∀ s : ℂ, IsStationaryJet b E s → ∀ j : ℕ, openEntranceTime W ≤ j →
              (j : ℝ) ≤ T * W →
              eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal p)
                  (oneEndedLaw W b j) +
                eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal p)
                  (oneEndedLaw W b j) ≤ ENNReal.ofReal (C / W)) ∧
          ∀ j : ℕ, (j : ℝ) ≤ T * W →
            eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) ≤
              ENNReal.ofReal (C * ((j : ℝ) + 1) / W)

/-- `β, κ, T, q` first; then `ε > 0`; for each `b ∈ [β, 1/2-β]` and `K ≥ 1` there are `δ_{W,j}` with
`|r^D_{W,j}(a)| ≤ δ_{W,j}` for every `E ∈ bulkInterval κ`, every Hermitian `‖D‖ ≤ ε`,
`j₀ ≤ j ≤ TW` and `a ∈ [K⁻¹, K]`, and with `Σ_{j=j₀}^{⌊TW⌋} δ_{W,j} → 0`.
The remainder
`detClockRemainderD` is the one of `DetClockEvolutionD`, at the energy `E`.
-/
def DetClockEvolutionDBulk : Prop :=
  ∀ β κ : ℝ, 0 < β → β < 1 / 4 → 0 < κ → ∀ (T : ℝ) (q : ℝ → ℝ), IsClockWeight q →
    ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ K : ℝ, 1 ≤ K → ∃ δ : ℕ → ℕ → ℝ,
      (∀ W j, ∀ E ∈ bulkInterval κ, ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
        openEntranceTime W ≤ j → (j : ℝ) ≤ T * W → ∀ a ∈ Icc K⁻¹ K,
          |detClockRemainderD W b E q D j a| ≤ δ W j) ∧
      Tendsto (fun W => ∑ j ∈ Finset.Icc (openEntranceTime W) ⌊T * W⌋₊, δ W j) atTop (𝓝 0)

/-- A fixed `0 < b < 1/2` lies in `[β, 1/2-β]` for `β = min b (1/2-b) / 2 < 1/4`. -/
theorem exists_beta {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) :
    ∃ β : ℝ, 0 < β ∧ β < 1 / 4 ∧ b ∈ Set.Icc β (1 / 2 - β) := by
  have hm : 0 < min b (1 / 2 - b) := lt_min hb0 (by linarith)
  refine ⟨min b (1 / 2 - b) / 2, by positivity, ?_, ?_, ?_⟩
  · have h1 := min_le_left b (1 / 2 - b)
    have h2 := min_le_right b (1 / 2 - b)
    linarith
  · have := min_le_left b (1 / 2 - b)
    have := lt_min hb0 (by linarith : (0 : ℝ) < 1 / 2 - b)
    linarith
  · have := min_le_right b (1 / 2 - b)
    have := lt_min hb0 (by linarith : (0 : ℝ) < 1 / 2 - b)
    linarith

/-- A fixed `-2 < E < 2` lies in `bulkInterval κ` for `κ = min (E+2) (2-E) > 0`. -/
theorem exists_kappa {E : ℝ} (hE0 : -2 < E) (hE1 : E < 2) :
    ∃ κ : ℝ, 0 < κ ∧ E ∈ bulkInterval κ := by
  refine ⟨min (E + 2) (2 - E), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left (E + 2) (2 - E); linarith
  · have := min_le_right (E + 2) (2 - E); linarith

/-- `OpenInputsMomentsBulk` implies the fixed-energy statement `OpenInputsMoments`. -/
theorem openInputsMoments_of_bulk (h : OpenInputsMomentsBulk) : OpenInputsMoments := by
  intro b hb0 hb1 E hE0 hE1 T q hq p hp
  obtain ⟨β, hβ, hβ4, hb⟩ := exists_beta hb0 hb1
  obtain ⟨κ, hκ, hE⟩ := exists_kappa hE0 hE1
  obtain ⟨ε, hε, hbε⟩ := h β κ hβ hβ4 hκ T q hq p hp
  obtain ⟨C, W₀, hC⟩ := hbε b hb
  exact ⟨ε, C, W₀, hε, fun W hW D hD hDε => hC W hW E hE D hD hDε⟩

/-- `DetClockEvolutionDBulk` implies the fixed-energy statement `DetClockEvolutionD`. -/
theorem detClockEvolutionD_of_bulk (h : DetClockEvolutionDBulk) : DetClockEvolutionD := by
  intro b hb0 hb1 E hE0 hE1 T q hq
  obtain ⟨β, hβ, hβ4, hb⟩ := exists_beta hb0 hb1
  obtain ⟨κ, hκ, hE⟩ := exists_kappa hE0 hE1
  obtain ⟨ε, hε, hbε⟩ := h β κ hβ hβ4 hκ T q hq
  refine ⟨ε, hε, fun K hK => ?_⟩
  obtain ⟨δ, hδ, hsum⟩ := hbε b hb K hK
  exact ⟨δ, fun W j D hD hDε hj hjT a ha => hδ W j E hE D hD hDε hj hjT a ha, hsum⟩

end MovingEnergy

end BlockBand.Endpoints.Clock
