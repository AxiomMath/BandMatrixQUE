module

public import BlockBand.Native.CEH.ETH.BlockBand.Model.GaussianRing

/-!
# Variance bookkeeping for the coarea Gaussian split

This module isolates the numerical part of the pair splitting and of the remark on the coarea
parameters.  For a source
scale `s ≤ min(c,b)`, the fresh GUE variance `t=s/(2W)` can be removed from
both a diagonal-block entry of variance `c/W` and an internal bond entry of
variance `b/W`; the residual variances stay nonnegative.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

/-- The fresh GUE entry variance in the coarea split. -/
def coareaGUEVariance (p : Params) (s : ℝ) : ℝ :=
  s / (2 * (p.W : ℝ))

/-- Residual variance in a diagonal block after removing the fresh GUE part. -/
def coareaDiagonalResidualVariance (p : Params) (s : ℝ) : ℝ :=
  p.diagonalVariance - coareaGUEVariance p s

/-- Residual variance in the bond internal to the selected pair after removing
the fresh GUE part. -/
def coareaBondResidualVariance (p : Params) (s : ℝ) : ℝ :=
  p.bondVariance - coareaGUEVariance p s

/-- The fresh GUE variance is nonnegative for a nonnegative source scale. -/
theorem coareaGUEVariance_nonneg (p : Params) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ coareaGUEVariance p s := by
  unfold coareaGUEVariance
  positivity

/-- The selected scale bound leaves a nonnegative diagonal residual variance. -/
theorem coareaDiagonalResidualVariance_nonneg
    (p : Params) {s : ℝ} (hs : s ≤ p.c) :
    0 ≤ coareaDiagonalResidualVariance p s := by
  unfold coareaDiagonalResidualVariance coareaGUEVariance
  unfold Params.diagonalVariance Conventions.diagonalEntryVariance
  have hW : 0 < (p.W : ℝ) := by exact_mod_cast p.W_pos
  apply sub_nonneg.mpr
  rw [show s / (2 * (p.W : ℝ)) = (s / 2) / (p.W : ℝ) by ring]
  exact (div_le_div_iff_of_pos_right hW).2 (by linarith [p.c_pos])

/-- The selected scale bound leaves a nonnegative internal-bond residual variance. -/
theorem coareaBondResidualVariance_nonneg
    (p : Params) {s : ℝ} (hs : s ≤ p.b) :
    0 ≤ coareaBondResidualVariance p s := by
  unfold coareaBondResidualVariance coareaGUEVariance
  unfold Params.bondVariance Conventions.bondEntryVariance
  have hW : 0 < (p.W : ℝ) := by exact_mod_cast p.W_pos
  apply sub_nonneg.mpr
  rw [show s / (2 * (p.W : ℝ)) = (s / 2) / (p.W : ℝ) by ring]
  exact (div_le_div_iff_of_pos_right hW).2 (by linarith [p.b_pos])

/-- Exact recovery of the original diagonal variance from residual plus fresh noise. -/
theorem coareaDiagonalResidualVariance_add
    (p : Params) (s : ℝ) :
    coareaDiagonalResidualVariance p s + coareaGUEVariance p s =
      p.diagonalVariance := by
  simp [coareaDiagonalResidualVariance]

/-- Exact recovery of the original internal-bond variance from residual plus fresh noise. -/
theorem coareaBondResidualVariance_add
    (p : Params) (s : ℝ) :
    coareaBondResidualVariance p s + coareaGUEVariance p s =
      p.bondVariance := by
  simp [coareaBondResidualVariance]

end CEHNative.BlockBand
