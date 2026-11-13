module

public import BlockBand.SourceProcess.Stochastic.FiniteSource

/-!
# Uniqueness of the Gram law up to a deterministic horizon

`IsGramHorizonSolution Q 𝓖 D₀ 𝖣 r G` is the birth-free Gram martingale problem
(`IsGramMartingaleSolution`) asked only up to the deterministic horizon `r`: `G` is adapted and
a.s. continuous, feasible at all times `t ≤ r`, and for every trace level `K` the compensated
coordinates and compensated products, stopped at `σ_K ∧ r`, have `𝓖`-martingale modifications.

`GramHorizonLaw` states that two such solutions (`D₀ > 0`, signature `𝖣`) with equal initial laws
have equal laws at time `r`. It is the finite-horizon form of global Gram-law uniqueness
(`GramUniqueness.gramLaw_eq_of_initial`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornStopped

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic
open scoped NNReal

/-- The Gram martingale problem up to the deterministic horizon `r` (clauses stopped at
`σ_K ∧ r`, feasibility on `[0, r]`). -/
structure IsGramHorizonSolution {Ω c : Type*} [MeasurableSpace Ω] [Fintype c] [DecidableEq c]
    (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ)
    (D : Matrix c c ℂ) (r : ℝ≥0) (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) : Prop where
  adapted : ∀ t, StronglyMeasurable[𝓖 t] (G t)
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => G t ω
  feasible : ∀ᵐ ω ∂Q, ∀ t ≤ r, GramFeasible D (G t ω)
  drift : ∀ (K : ℝ) (e : Fin 2 × c × c), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (gramCompensated D0 D G e)
      (fun ω => min (gramTraceStop G K ω) (r : WithTop ℝ≥0)) t
  bracket : ∀ (K : ℝ) (e e' : Fin 2 × c × c), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (fun t ω => gramCompensated D0 D G e t ω *
        gramCompensated D0 D G e' t ω -
        ∫ s in Set.Ioc (0 : ℝ) t, gramCovEntry D0 D e e' (G s.toNNReal ω))
      (fun ω => min (gramTraceStop G K ω) (r : WithTop ℝ≥0)) t

/-- **Gram-law uniqueness up to a deterministic horizon.** This is stated as a hypothesis. -/
def GramHorizonLaw : Prop :=
  ∀ (c : Type) [Fintype c] [DecidableEq c] (D0 : ℝ) (D : Matrix c c ℂ), 0 < D0 → IsSignature D →
  ∀ r : ℝ≥0,
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
    (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ),
    IsProbabilityMeasure Q → IsGramHorizonSolution Q 𝓖 D0 D r G →
  ∀ (Ω' : Type) (m' : MeasurableSpace Ω') (𝓖' : Filtration ℝ≥0 m') (Q' : Measure Ω')
    (G' : ℝ≥0 → Ω' → Matrix c c ℂ × Matrix c c ℂ),
    IsProbabilityMeasure Q' → IsGramHorizonSolution Q' 𝓖' D0 D r G' →
    Q.map (G 0) = Q'.map (G' 0) → Q.map (G r) = Q'.map (G' r)

end BlockBand.SourceProcess.BornStopped
