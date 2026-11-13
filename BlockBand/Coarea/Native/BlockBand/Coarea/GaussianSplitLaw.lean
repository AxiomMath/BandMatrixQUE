module

public import BlockBand.Coarea.Native.BlockBand.Coarea.GaussianSplitVariance
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Scalar Gaussian law behind the coarea noise split

The variance bookkeeping of the pair splitting, combined with Mathlib's convolution theorem for
independent real Gaussians: coordinate by coordinate, residual noise plus the fresh GUE noise
has exactly the original diagonal-block or internal-bond law.  The assembly of all coordinates
into an independent Hermitian matrix is a separate finite-product construction.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Fresh GUE variance as a nonnegative real parameter. -/
def coareaGUEVarianceNNReal (p : Params) {s : ℝ} (hs : 0 ≤ s) : NNReal :=
  ⟨coareaGUEVariance p s, coareaGUEVariance_nonneg p hs⟩

/-- Nonnegative diagonal residual variance as an `NNReal`. -/
def coareaDiagonalResidualVarianceNNReal
    (p : Params) {s : ℝ} (hs : s ≤ p.c) : NNReal :=
  ⟨coareaDiagonalResidualVariance p s,
    coareaDiagonalResidualVariance_nonneg p hs⟩

/-- Nonnegative internal-bond residual variance as an `NNReal`. -/
def coareaBondResidualVarianceNNReal
    (p : Params) {s : ℝ} (hs : s ≤ p.b) : NNReal :=
  ⟨coareaBondResidualVariance p s,
    coareaBondResidualVariance_nonneg p hs⟩

/-- The diagonal residual and fresh variances add to the original variance. -/
theorem coareaDiagonalResidualVarianceNNReal_add
    (p : Params) {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c) :
    coareaDiagonalResidualVarianceNNReal p hsc +
        coareaGUEVarianceNNReal p hs0 =
      ⟨p.diagonalVariance, p.diagonalVariance_pos.le⟩ := by
  ext
  exact coareaDiagonalResidualVariance_add p s

/-- The internal-bond residual and fresh variances add to the original variance. -/
theorem coareaBondResidualVarianceNNReal_add
    (p : Params) {s : ℝ} (hs0 : 0 ≤ s) (hsb : s ≤ p.b) :
    coareaBondResidualVarianceNNReal p hsb +
        coareaGUEVarianceNNReal p hs0 =
      ⟨p.bondVariance, p.bondVariance_pos.le⟩ := by
  ext
  exact coareaBondResidualVariance_add p s

/-- Independent centered diagonal-residual and fresh coordinates recombine to
exactly the original diagonal-entry Gaussian law.  This is a scalar coordinate theorem; no
matrix independence or asymptotic uniformity is hidden in the statement. -/
theorem gaussianReal_add_coareaDiagonalResidual
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : Params) {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c)
    {X Y : Ω → ℝ}
    (hXY : IndepFun X Y P)
    (hX : HasLaw X
      (gaussianReal 0 (coareaDiagonalResidualVarianceNNReal p hsc)) P)
    (hY : HasLaw Y (gaussianReal 0 (coareaGUEVarianceNNReal p hs0)) P) :
    P.map (X + Y) =
      gaussianReal 0 ⟨p.diagonalVariance, p.diagonalVariance_pos.le⟩ := by
  simpa [coareaDiagonalResidualVarianceNNReal_add p hs0 hsc] using
    gaussianReal_add_gaussianReal_of_indepFun hXY hX hY

/-- Independent centered internal-bond residual and fresh coordinates recombine
to exactly the original internal-bond Gaussian law. -/
theorem gaussianReal_add_coareaBondResidual
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : Params) {s : ℝ} (hs0 : 0 ≤ s) (hsb : s ≤ p.b)
    {X Y : Ω → ℝ}
    (hXY : IndepFun X Y P)
    (hX : HasLaw X
      (gaussianReal 0 (coareaBondResidualVarianceNNReal p hsb)) P)
    (hY : HasLaw Y (gaussianReal 0 (coareaGUEVarianceNNReal p hs0)) P) :
    P.map (X + Y) =
      gaussianReal 0 ⟨p.bondVariance, p.bondVariance_pos.le⟩ := by
  simpa [coareaBondResidualVarianceNNReal_add p hs0 hsb] using
    gaussianReal_add_gaussianReal_of_indepFun hXY hX hY

end CoareaNative.BlockBand
