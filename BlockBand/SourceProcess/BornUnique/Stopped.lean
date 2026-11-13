module

public import BlockBand.SourceProcess.BornUnique.Segment

/-!
# Stopped law from time `0` and restart at a `𝓖₀`-measurable time

* `BornStoppedLaw` (stopped uniqueness, no restart). Births are functions `b(z)` of
  `𝓖₀`-measurable side data `z` (any measurable space), none in `(0, α'(z))`. Then the joint law
  of `(z, (G - J)(0))` determines the joint law of `(z, (G - J)(α'(z)))`. On `[0, α')` the jump
  process is constant, so `G` solves the birth-free Gram martingale problem up to the
  `𝓖₀`-measurable horizon `α'`, and `(G - J)(α')` is the left limit `G(α'-) - J(0)`.
* `BornRestart` (optional sampling). The process restarted at a `𝓖₀`-measurable time `α(β)` is
  a.s. equal, at all times at once, to a born solution for some filtration `𝓗` with
  `β` `𝓗₀`-measurable and births shifted to `β - α(β)`. The natural choice is
  `𝓗_u = 𝓖_{(α+u)+}` with the right-continuous version of `G(α + u)`; the filtration is not
  assumed complete, so the restarted process is asked to agree with `G(α + ·)` only a.s.

Both are stated as hypotheses; `bornSegmentStep_of` derives `BornSegmentStep` from them.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornUnique

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

/-- **Stopped law up to the first later birth, from time `0`.** -/
def BornStoppedLaw : Prop :=
  ∀ (c F Z : Type) [Fintype c] [DecidableEq c] [Fintype F] [MeasurableSpace Z] (D0 : ℝ)
    (D : Matrix c c ℂ), 0 < D0 → IsSignature D →
  ∀ (j : F → GramState c) (b : Z → F → ℝ) (α' : Z → ℝ≥0), Measurable b → Measurable α' →
    (∀ z f, b z f ≤ 0 ∨ (α' z : ℝ) ≤ b z f) →
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
    (z : Ω → Z) (G : ℝ≥0 → Ω → GramState c),
    IsProbabilityMeasure Q → Measurable[𝓖 0] z →
    IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (b (z ω)) (t : ℝ)) G →
  ∀ (Ω' : Type) (m' : MeasurableSpace Ω') (𝓖' : Filtration ℝ≥0 m') (Q' : Measure Ω')
    (z' : Ω' → Z) (G' : ℝ≥0 → Ω' → GramState c),
    IsProbabilityMeasure Q' → Measurable[𝓖' 0] z' →
    IsBornGramSolution Q' 𝓖' D0 D (fun t ω => birthSum j (b (z' ω)) (t : ℝ)) G' →
    Q.map (fun ω => (z ω, bornCont j (fun ω => b (z ω)) G 0 ω)) =
      Q'.map (fun ω => (z' ω, bornCont j (fun ω => b (z' ω)) G' 0 ω)) →
    Q.map (fun ω => (z ω, bornCont j (fun ω => b (z ω)) G (α' (z ω)) ω)) =
      Q'.map (fun ω => (z' ω, bornCont j (fun ω => b (z' ω)) G' (α' (z' ω)) ω))

/-- **Restart at a `𝓖₀`-measurable time.** -/
def BornRestart : Prop :=
  ∀ (c F : Type) [Fintype c] [DecidableEq c] [Fintype F] (D0 : ℝ) (D : Matrix c c ℂ)
    (j : F → GramState c) (α : (F → ℝ) → ℝ≥0), Measurable α →
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
    (β : Ω → F → ℝ) (G : ℝ≥0 → Ω → GramState c),
    IsProbabilityMeasure Q → Measurable[𝓖 0] β →
    IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G →
  ∃ (𝓗 : Filtration ℝ≥0 m) (H : ℝ≥0 → Ω → GramState c), Measurable[𝓗 0] β ∧
    IsBornGramSolution Q 𝓗 D0 D
      (fun u ω => birthSum j (fun f => β ω f - α (β ω)) (u : ℝ)) H ∧
    ∀ᵐ ω ∂Q, ∀ u, H u ω = G (α (β ω) + u) ω

end BlockBand.SourceProcess.BornUnique
