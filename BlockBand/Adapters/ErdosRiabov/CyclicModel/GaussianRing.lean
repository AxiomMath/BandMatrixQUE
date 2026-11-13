module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Indices
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib

/-!
# The variance profile of the Gaussian block-band ring

The block weight `c 1_{l=k} + b 1_{l=k±1}` on `ZMod n`, the entry variance profile
`S_xy = w(x₁, y₁)/W` on the sites, and the site order used to select the independent
upper-triangular coordinates. For an off-diagonal circular entry of total variance `s`,
the real and imaginary parts each have variance `s/2`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace GaussianRing

/-- Block-level variance weight
`c 1_{l=k} + b 1_{l=k+1} + b 1_{l=k-1}`.  The additive presentation
follows the formula of the model and makes row normalization independent
of any case split. -/
def blockWeight (p : Params) (k l : ZMod p.n) : ℝ :=
  (if l = k then p.c else 0) +
    (if l = k + 1 then p.b else 0) +
    (if l = k - 1 then p.b else 0)

/-- Total complex entry variance on the site space. -/
def varianceProfile (p : Params) (x y : Site p.n p.W) : ℝ :=
  blockWeight p x.1 y.1 / (p.W : ℝ)

/-- Canonical ordering on sites, used only to select the independent
upper-triangular coordinates. -/
def siteLE (p : Params) (x y : Site p.n p.W) : Prop :=
  (p.siteIndexEquiv x).val ≤ (p.siteIndexEquiv y).val

end GaussianRing

end BlockBand.Adapters.ErdosRiabov.CyclicModel
