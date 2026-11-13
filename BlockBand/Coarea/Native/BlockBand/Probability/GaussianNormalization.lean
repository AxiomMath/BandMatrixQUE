module

public import BlockBand.Coarea.Native.BlockBand.Model.GaussianRing
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian normalization conventions

This file fixes the GUE normalizing constant and the circular-complex variance
convention.  It does not construct the matrix-valued density; `GaussianRing.Law`
is the probability law used downstream.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

/-- Normalizing constant for the GUE density
with diagonal variance `t` and total off-diagonal complex variance `t`. -/
def gueNormalizer (d : ℕ) (t : ℝ) : ℝ :=
  (2 * Real.pi * t) ^ ((d : ℝ) / 2) *
    (Real.pi * t) ^ (((d : ℝ) * ((d : ℝ) - 1)) / 2)

/-- The GUE normalizer is positive for positive variance. -/
theorem gueNormalizer_pos {d : ℕ} {t : ℝ} (ht : 0 < t) :
    0 < gueNormalizer d t := by
  unfold gueNormalizer
  apply mul_pos <;> apply Real.rpow_pos_of_pos <;> positivity

/-- A circular complex Gaussian of total variance `t` has two real component
variances `t/2`. -/
def circularComponentVariance (t : ℝ) : ℝ := t / 2

/-- The two circular component variances add back to the total variance. -/
theorem two_circularComponentVariance (t : ℝ) :
    circularComponentVariance t + circularComponentVariance t = t := by
  unfold circularComponentVariance
  ring

/-- The normalized `d × d` GUE variance parameter `1/d`. -/
def normalizedGUEVariance (d : ℕ) : ℝ := 1 / (d : ℝ)

/-- The diagonal blocks of the model have GUE variance `c/W`. -/
theorem model_diagonalVariance_eq (p : Params) :
    p.diagonalVariance = p.c * normalizedGUEVariance p.W := by
  unfold Params.diagonalVariance Conventions.diagonalEntryVariance
    normalizedGUEVariance Params.c Conventions.diagonalWeight
  field_simp

/-- The forward Ginibre bonds have total circular variance `b/W`. -/
theorem model_bondVariance_eq (p : Params) :
    p.bondVariance = p.b * normalizedGUEVariance p.W := by
  unfold Params.bondVariance Conventions.bondEntryVariance normalizedGUEVariance
  field_simp

end CoareaNative.BlockBand
