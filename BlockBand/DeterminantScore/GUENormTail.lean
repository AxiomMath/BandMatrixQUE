module

public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Exponential operator-norm tail of `GUE` (statement)

The Gaussian operator-norm tail used in the proof of the determinant-score theorem (the pair law
has every fixed Gaussian norm moment bounded) and in the proof of the physical angular theorem
(Gaussian norm tails). It is a standard fact about the Gaussian ensemble, not an estimate of the
paper (ε-net of the unit sphere, `u*Gu ~ N(0, t)`, Chernoff, union bound).

`GUENormTailStatement`: there are `C, c > 0` with
`GUE_ι(t){‖G‖ > C √(t |ι|)} ≤ e^{-c|ι|}` for every finite `ι` and `t ≥ 0`, for the Euclidean
operator norm (`Matrix.Norms.L2Operator`) and `gueMeasure` of `CoareaPalm` (`E|G_ab|² = t`, so
`‖G‖ ≈ 2√(t|ι|)`; at `GUE_{2W}(s/2W)` the threshold is `C√s`).

Definition only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.GUENormTail

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-- **Exponential `GUE` operator-norm tail.** -/
def GUENormTailStatement : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : ℝ≥0),
      gueMeasure ι t {G | C * Real.sqrt ((t : ℝ) * (Fintype.card ι : ℝ)) < ‖G‖} ≤
        ENNReal.ofReal (Real.exp (-(c * (Fintype.card ι : ℝ))))

end BlockBand.DeterminantScore.GUENormTail
