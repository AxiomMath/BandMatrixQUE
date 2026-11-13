module

public import BlockBand.Coarea.Native.BlockBand.Counting.PaperCountingLimitConcrete

/-!
# Concrete paper-facing counting theorem

This module is the final wrapper around the block-band counting argument.  It
combines physical multi-block transport, PSSS finite-volume estimates,
Prokhorov extraction in the vague rational-window state, the a.e.-continuous
mapping theorem for restriction counts, exponential uniform integrability,
and smoothed open close-pair events.

The only hypothesis left supplies, for every vague subsequential limit, a
`ConcretePaperCountingLimitInput`.  Its fields are not generic probability or
topology facts: they are the model identities that a concrete model must
supply—boundary avoidance, identification of the finite and
limit intensities, the quantitative exponential and close-pair estimates for
the chosen restrictions, and closed validity of the mark constraint.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

/-- Irreducible model-specific completion data for every vague subsequential
limit.  Scalar law convergence, uniform integrability, openness of close-pair
events, and collision containment are deliberately absent: they are derived
by `ConcretePaperCountingLimitInput.toPaperCountingLimitCompletionInput`. -/
structure ConcretePaperCountingTheoremInput
    (input : PSSSInput.{0}) (seq : PSSSRationalWindowSequence input)
    [OpensMeasurableSpace VagueRationalWindowState] where
  complete : ∀ (μ : ProbabilityMeasure VagueRationalWindowState)
    (φ : ℕ → ℕ), StrictMono φ →
    Tendsto (seq.vagueLaw ∘ φ) atTop (𝓝 μ) →
    ConcretePaperCountingLimitInput input seq μ φ

/-- **Concrete form of the counting theorem of the paper.**

The conclusion contains, with the paper's exact constants:

* all physical falling-factorial bounds;
* the physical unfolded exponential bound;
* all normalized PSSS factorial and exponential bounds;
* the explicit compact-tail schedule and a weak vague subsequence;
* almost-sure support on a consistent integer local point state;
* limiting close-pair estimates and almost-sure collision exclusion; and
* preservation of the closed mark-validity condition.

The input contains no scalar count-law convergence, count uniform integrability,
close-pair openness or collision containment hypothesis. -/
theorem paperCountingTheorem_concrete
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    [OpensMeasurableSpace RationalWindowPointState]
    [T2Space VagueRationalWindowState]
    [FirstCountableTopology (ProbabilityMeasure VagueRationalWindowState)]
    [HasOuterApproxClosed VagueRationalWindowState]
    (input : PSSSInput.{0})
    (seq : PSSSRationalWindowSequence input)
    {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μphys : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μphys] [IsProbabilityMeasure ν]
    (p : Params)
    (G : BlockGUE.Law.{0} (GaussianRing.physicalBlockSizes p)
      (GaussianRing.physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix
      (BlockGUE.Index (GaussianRing.physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ)
    (transport : GaussianRing.PhysicalMultiBlockCountTransport
      μphys ν p G A₀ N)
    (e L ρ : ℝ) (hL : 0 < L) (hρ : 0 < ρ)
    (hdim : (p.n * p.W : ℝ) ≤ L)
    (model : ConcretePaperCountingTheoremInput input seq) :
    PaperCountingTheoremConclusion input seq μphys ν p G A₀ N transport e L ρ := by
  apply paperCountingTheorem input seq μphys ν p G A₀ N transport
    e L ρ hL hρ hdim
  intro μ φ hφ hlim
  exact (model.complete μ φ hφ hlim).toPaperCountingLimitCompletionInput
    input seq μ φ

end CoareaNative.BlockBand
