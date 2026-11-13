module

public import BlockBand.Coarea.Native.BlockBand.Analysis.PositiveResolvent
public import BlockBand.Coarea.Native.BlockBand.Counting.ProjectedWegner

/-!
# Projected traces of absorbed resolvents

This file connects the matrix positivity statement for an absorbed resolvent
to the blockwise real quantities summed in the projected Wegner estimate.  It
uses the unnormalized diagonal-block trace: no normalized trace or hidden block-size
factor is introduced.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix
open scoped BigOperators ComplexOrder

/-- Negative imaginary trace of the diagonal block indexed by `j`.

The ambient coordinates are pairs `(j,i)`.  This is the paper's quantity
`-Im Tr P_j G`, with the ordinary (unnormalized) trace on the retained block. -/
def blockNegativeImaginaryTrace
    {β ι : Type*} [Fintype ι]
    (M : Matrix (β × ι) (β × ι) ℂ) (j : β) : ℝ :=
  ∑ i, -(M (j, i) (j, i)).im

/-- Pointwise diagonal form of the matrix imaginary-part convention. -/
theorem neg_matrixImaginaryPart_apply_self
    {n : Type*} (M : Matrix n n ℂ) (i : n) :
    (-matrixImaginaryPart M) i i = ((-(M i i).im : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [matrixImaginaryPart]
    ring
  · simp [matrixImaginaryPart]

/-- A positive-semidefinite negative matrix imaginary part makes every
projected block trace nonnegative. -/
theorem blockNegativeImaginaryTrace_nonneg
    {β ι : Type*} [Fintype ι]
    (M : Matrix (β × ι) (β × ι) ℂ)
    (hM : (-matrixImaginaryPart M).PosSemidef) (j : β) :
    0 ≤ blockNegativeImaginaryTrace M j := by
  unfold blockNegativeImaginaryTrace
  apply Finset.sum_nonneg
  intro i _hi
  have hdiag := hM.diag_nonneg (i := (j, i))
  rw [neg_matrixImaginaryPart_apply_self] at hdiag
  have hreal := (RCLike.nonneg_iff.mp hdiag).1
  simpa using hreal

/-- The absorbed-resolvent positivity identity implies nonnegativity of every
retained block trace.  This is the sign input used before Tonelli and Fatou in
the projected Wegner lemma. -/
theorem blockNegativeImaginaryTrace_absorbed_nonneg
    {β ι : Type*} [Fintype β] [Fintype ι]
    [DecidableEq β] [DecidableEq ι]
    (A Γ : Matrix (β × ι) (β × ι) ℂ)
    (hA : A.IsHermitian) (hΓ : Γ.IsHermitian) (hΓpos : Γ.PosSemidef)
    (hinv : IsUnit (A + Complex.I • Γ).det) (j : β) :
    0 ≤ blockNegativeImaginaryTrace (A + Complex.I • Γ)⁻¹ j := by
  apply blockNegativeImaginaryTrace_nonneg
  exact absorbedResolvent_negativeImaginary_posSemidef A Γ hA hΓ hΓpos hinv

/-- Canonical decomposition of a projected trace over a finite set of blocks
into its single-block contributions. -/
def projectedTraceDecomposition_of_blocks
    {Ω β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι]
    (M : Ω → Matrix (β × ι) (β × ι) ℂ) (B : Finset β) :
    ProjectedTraceDecomposition
      (fun j ω => blockNegativeImaginaryTrace (M ω) j) B where
  projectedTrace := fun ω => ∑ j ∈ B, blockNegativeImaginaryTrace (M ω) j
  eq_sum := rfl

end CoareaNative.BlockBand
