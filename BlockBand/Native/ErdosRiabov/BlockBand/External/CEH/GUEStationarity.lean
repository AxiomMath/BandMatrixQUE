module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.CEH.OUFlow
public import BlockBand.Native.ErdosRiabov.BlockBand.Model.GaussianRing
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
public import Mathlib.Analysis.Complex.Basic
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
public import Mathlib.FieldTheory.Separable
public import Mathlib.Probability.Independence.Integration

/-!
# Concrete GUE stationarity for the CEH Ornstein–Uhlenbeck flow

This module constructs the probability law used at the stationarity boundary,
rather than packaging invariance as a field of an abstract certificate.  A
sample contains, at every finite Hermitian coordinate, an independent pair of
centered Gaussians of the variance of the paper.  Coordinatewise mixing by
`a x + b y`, with `a²+b²=1`, is proved to map this finite product exactly back
to the concrete GUE coordinate measure.

Diagonal coordinates have variance `t`; the real and imaginary parts of each
strict-upper entry have variance `t/2`.  The CEH adapter specializes
`t = s/N`, and the OU adapter specializes `a=e^{-u/2}` and
`b=sqrt(1-e^{-u})`.  All statements are finite-dimensional and exact.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand.CEH

open MeasureTheory ProbabilityTheory
open ERNative.BlockBand
open scoped NNReal

/-- Under a product of two centered scalar Gaussians, the coordinate
projections are independent. -/
theorem indepFun_guePairCoordinate (v : NNReal) :
    IndepFun (fun x : ℝ × ℝ => x.1) (fun x : ℝ × ℝ => x.2)
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
  exact indepFun_prod measurable_id measurable_id

/-- Scalar Gaussian rotation for arbitrary coefficients on the unit circle.
This is proved from Mathlib's scaling and convolution laws, not assumed. -/
theorem gaussianReal_pair_mix {v : NNReal} {a b : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) :
    Measure.map (fun x : ℝ × ℝ => a * x.1 + b * x.2)
        ((gaussianReal 0 v).prod (gaussianReal 0 v)) =
      gaussianReal 0 v := by
  let P := (gaussianReal 0 v).prod (gaussianReal 0 v)
  have hX : HasLaw (fun x : ℝ × ℝ => x.1) (gaussianReal 0 v) P := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    simp [P]
  have hY : HasLaw (fun x : ℝ × ℝ => x.2) (gaussianReal 0 v) P := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    simp [P]
  have hI : IndepFun (fun x : ℝ × ℝ => a * x.1)
      (fun x : ℝ × ℝ => b * x.2) P := by
    exact (indepFun_guePairCoordinate v).comp
      (measurable_const_mul a) (measurable_const_mul b)
  have hXa := gaussianReal_const_mul hX a
  have hYb := gaussianReal_const_mul hY b
  have hadd := gaussianReal_add_gaussianReal_of_indepFun hI hXa hYb
  have hv : NNReal.mk (a ^ 2) (sq_nonneg a) * v +
      NNReal.mk (b ^ 2) (sq_nonneg b) * v = v := by
    ext
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk]
    nlinarith [show 0 ≤ (v : ℝ) from v.coe_nonneg]
  have hfun :
      (fun x : ℝ × ℝ => a * x.1) + (fun x : ℝ × ℝ => b * x.2) =
        (fun x : ℝ × ℝ => a * x.1 + b * x.2) := by
    funext x
    rfl
  rw [hfun] at hadd
  simpa [P, hv] using hadd

end ERNative.BlockBand.CEH
