module

public import BlockBand.SourceProcess.BornUnique.Pin

/-!
# One inter-birth segment

`bornCont j β G = G - J` is the continuous part of a born solution (`J = birthSum j β`).
`BornSegmentStep` states: between two `𝓖₀`-measurable times `α ≤ α'` (functions of the birth
times) with no birth in the open interval `(α, α')`, the joint law of `(β, (G - J)(α))`
determines that of `(β, (G - J)(α'))`. On `[α, α')` the jump process is the constant `J(α)`, so
`G` solves the birth-free Gram martingale problem from `G(α)` up to the `𝓖₀`-measurable horizon
`α'`. The statement is thus the restart of `G` at `α` (optional sampling at a `𝓖₀`-measurable
time) followed by stopped uniqueness of the Gram martingale problem up to `α'`, jointly with the
`𝓖₀`-data `β`. `bornGramLawUnique_of_segmentStep` derives `BornGramLawUnique` from it by
concatenation over the births.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornUnique

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

/-- The continuous part `G - J` of a born solution with jump process `J = birthSum j β`. -/
def bornCont {Ω c F : Type*} [Fintype F] (j : F → GramState c) (β : Ω → F → ℝ)
    (G : ℝ≥0 → Ω → GramState c) (t : ℝ≥0) (ω : Ω) : GramState c :=
  G t ω - birthSum j (β ω) (t : ℝ)

/-- **One inter-birth segment.** For `D₀ > 0`, a signature `𝖣`, jumps `j`, and
measurable times `α ≤ α'` of the birth vector such that no birth lies in `(α(x), α'(x))`: for
two born Gram solutions on arbitrary filtered probability spaces with `𝓖₀`-measurable birth
times `β`, equal joint laws of `(β, (G - J)(α(β)))` give equal joint laws of
`(β, (G - J)(α'(β)))`. This is stated as a hypothesis. -/
def BornSegmentStep : Prop :=
  ∀ (c F : Type) [Fintype c] [DecidableEq c] [Fintype F] (D0 : ℝ) (D : Matrix c c ℂ),
    0 < D0 → IsSignature D → ∀ (j : F → GramState c) (α α' : (F → ℝ) → ℝ≥0),
    Measurable α → Measurable α' → (∀ x, α x ≤ α' x) →
    (∀ x f, x f ≤ α x ∨ (α' x : ℝ) ≤ x f) →
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
    (β : Ω → F → ℝ) (G : ℝ≥0 → Ω → GramState c),
    IsProbabilityMeasure Q → Measurable[𝓖 0] β →
    IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G →
  ∀ (Ω' : Type) (m' : MeasurableSpace Ω') (𝓖' : Filtration ℝ≥0 m') (Q' : Measure Ω')
    (β' : Ω' → F → ℝ) (G' : ℝ≥0 → Ω' → GramState c),
    IsProbabilityMeasure Q' → Measurable[𝓖' 0] β' →
    IsBornGramSolution Q' 𝓖' D0 D (fun t ω => birthSum j (β' ω) (t : ℝ)) G' →
    Q.map (fun ω => (β ω, bornCont j β G (α (β ω)) ω)) =
      Q'.map (fun ω => (β' ω, bornCont j β' G' (α (β' ω)) ω)) →
    Q.map (fun ω => (β ω, bornCont j β G (α' (β ω)) ω)) =
      Q'.map (fun ω => (β' ω, bornCont j β' G' (α' (β' ω)) ω))

end BlockBand.SourceProcess.BornUnique
