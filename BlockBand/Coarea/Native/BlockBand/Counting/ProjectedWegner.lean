module

public import BlockBand.Coarea.Native.BlockBand.External.PSSS.Interface
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The finite-block step in the projected Wegner estimate

The analytic heart of the projected Wegner lemma is a one-block conditional
spectral-averaging estimate (PSSS Lemma 3.1 followed by the one-block counting
bound).  This file isolates the step after that input:
a projected trace over a union of blocks is the sum of its block traces, and
finite additivity of expectation gives the exact factor `|B|`.

`SingleBlockAveraging` is an explicit argument; it is not asserted here.  It is
constructed elsewhere from the Schur complement, absorber positivity, and the
PSSS interface.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory
open scoped BigOperators

universe u v

/-- Output of the one-block conditional averaging calculation: each `g j` is integrable,
a.e. nonnegative and has mean at most `π K W`. Here `g j` is the nonnegative imaginary trace
contributed by block `j`. -/
structure SingleBlockAveraging
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type v} [Fintype β] [DecidableEq β]
    (g : β → Ω → ℝ) (K W : ℝ) where
  integrable : ∀ j, Integrable (g j) μ
  nonneg : ∀ j, 0 ≤ᵐ[μ] g j
  oneBlock : ∀ j, ∫ ω, g j ω ∂μ ≤ Real.pi * K * W

/-- A projected quantity together with its exact decomposition
into single-block imaginary traces. -/
structure ProjectedTraceDecomposition
    {Ω : Type u} {β : Type v} [Fintype β] [DecidableEq β]
    (g : β → Ω → ℝ) (B : Finset β) where
  projectedTrace : Ω → ℝ
  eq_sum : projectedTrace = fun ω => ∑ j ∈ B, g j ω

/-- Projected Wegner lemma, finite-block summation step: if every retained
block satisfies the PSSS one-block bound, then every union of blocks satisfies
the bound with the exact cardinality factor. -/
theorem projectedWegner_of_singleBlock
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type v} [Fintype β] [DecidableEq β]
    (g : β → Ω → ℝ) (K W : ℝ)
    (havg : SingleBlockAveraging μ g K W)
    (B : Finset β) (hproj : ProjectedTraceDecomposition g B) :
    ∫ ω, hproj.projectedTrace ω ∂μ ≤
      Real.pi * K * W * (B.card : ℝ) := by
  rw [hproj.eq_sum, integral_finsetSum]
  · calc
      ∑ j ∈ B, ∫ ω, g j ω ∂μ ≤
          ∑ _j ∈ B, Real.pi * K * W := by
            exact Finset.sum_le_sum fun j _hj => havg.oneBlock j
      _ = Real.pi * K * W * (B.card : ℝ) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
  · intro j _hj
    exact havg.integrable j

/-- The projected trace supplied by a decomposition is integrable. -/
theorem ProjectedTraceDecomposition.integrable
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type v} [Fintype β] [DecidableEq β]
    {g : β → Ω → ℝ} {K W : ℝ}
    (havg : SingleBlockAveraging μ g K W)
    {B : Finset β} (hproj : ProjectedTraceDecomposition g B) :
    Integrable hproj.projectedTrace μ := by
  rw [hproj.eq_sum]
  exact integrable_finsetSum B fun j _hj => havg.integrable j

end CoareaNative.BlockBand
