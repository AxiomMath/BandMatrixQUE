module

public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ResolventIdentities
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import BlockBand.Model.Construction.OrderedEigenvalues
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Normalized finite-dimensional Ornstein–Uhlenbeck infrastructure

This file contains the unconditional, finite-dimensional part of the
Ornstein–Uhlenbeck argument used in the CEH input.  The normalization is

`H_t = exp (-t/2) F + exp (-t/2) X + sqrt (1-exp (-t)) Y`.

Thus a centered variance-`1/N` Hermitian Gaussian coordinate stays at variance
`1/N`; the deterministic deformation is damped by `exp (-t/2)`.  We do not
state a local law or hide one in a structure.  The probability-specific input
needed to identify `X,Y` as independent GUE coordinates remains visible at the
point where it is used; the coefficient algebra, deterministic resolvent increments, stopping
wrappers, and finite
Cauchy estimates below are proved identities.  No equality-in-law or continuous-time
stochastic-calculus theorem is claimed here.

The resolvent expansion is a deterministic finite-increment identity, including
its cubic remainder.  It is not a continuous-time Itô formula or a martingale
estimate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand.CEH

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

/-- Drift coefficient for the normalized Hermitian OU flow. -/
def ouDecay (t : ℝ) : ℝ := Real.exp (-t / 2)

/-- Fresh-noise coefficient for the normalized Hermitian OU flow. -/
def ouNoise (t : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-t))

/-- The fresh-noise variance is nonnegative for forward time. -/
theorem ouNoise_rad_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-t) := by
  rw [sub_nonneg]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)

/-- The two coefficients split unit variance. -/
theorem ouDecay_sq_add_ouNoise_sq {t : ℝ} (ht : 0 ≤ t) :
    ouDecay t ^ 2 + ouNoise t ^ 2 = 1 := by
  rw [ouDecay, ouNoise, Real.sq_sqrt (ouNoise_rad_nonneg ht)]
  have he : Real.exp (-t / 2) * Real.exp (-t / 2) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [pow_two, he]
  ring

/-- Semigroup law for the drift coefficient. -/
theorem ouDecay_add (s t : ℝ) :
    ouDecay (s + t) = ouDecay s * ouDecay t := by
  simp only [ouDecay]
  rw [show -(s + t) / 2 = -s / 2 + -t / 2 by ring, Real.exp_add]

/-!
## Exact matrix Itô / resolvent increment formula
-/

/-!
## Affine comparison flow with fixed coefficients
-/

/-!
## Stopping-time measurability
-/

/-!
## Quadratic variation and finite-dimensional Cauchy bounds
-/

end ERNative.BlockBand.CEH
