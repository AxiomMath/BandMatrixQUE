module

public import BlockBand.Internal.Contracts.Clocks

/-!
# The vanishing block-atom statement

`VanishingBlockAtom` states `E Σ_α |w(u_α)| Σ_k p_{αk}² → 0` along every critical sequence, a step
in the proof of the physical lead-profile theorem (it follows from the small-critical theorem,
nonatomic marks of every critical marked subsequence, and the count moments). The quantifiers are
those of `Clocks.PhysicalLeadProfileContract`: `b ∈ (0,1/2)`, bulk `E`, a smooth compactly
supported weight `w`, `τ > 0`, every critical sequence and every sequence of realizations. The
measure is the exact physical law; `p_{αk}` are the canonical block masses and `λ_α` the canonical
eigenvalues.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.Clocks

/-- `E Σ_α |w(u_α)| Σ_k p_{αk}²` under the exact physical law. -/
def blockAtomStatistic {p : Parameters} (R : FiniteRealization p) (E : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∫ H, ∑ α : Fin p.N, |w (microCoord p E (physicalOrderedEigenvalue p H α))| *
      ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k ^ 2
    ∂(R.model.law : Measure p.SiteMatrix)

/-- **Vanishing block atom**: `E Σ_α |w(u_α)| Σ_k p_{αk}² → 0` along every critical sequence. -/
def VanishingBlockAtom : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ w : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w → HasCompactSupport w →
    ∀ (τ : ℝ), 0 < τ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
      Tendsto (fun j => blockAtomStatistic (R j) E w) atTop (𝓝 0)

end BlockBand.Endpoints.Normalization
