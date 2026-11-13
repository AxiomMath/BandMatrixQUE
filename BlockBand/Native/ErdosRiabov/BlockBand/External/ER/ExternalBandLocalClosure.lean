module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.LocalLawBootstrapAssembly
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.DeterministicMDECore
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpResolventWeightedDysonAssembly
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpCoordinateIndexReorganization
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.TensorizedGaussianPoincare
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.RingAdapterMeasurability

/-!
# The Erdős–Riabov short-ring local law: unconditional ingredients

This module contains no declarations. It collects, through its imports, the ingredients of
the external band local law that are proved without hypotheses:

* the exact Gaussian covariance, block tensorization, both-parity profile facts, and
  constant-weight covariance operator;
* the corrected deterministic MDE stability inverse and cyclic Green bounds;
* the Gaussian coordinate IBP identities under the Gaussian-ring law and the entrywise
  resolvent bounds at the deterministic resolvent scale;
* the sharp centered second-moment tail;
* the algebraic conventions and measurability facts for the short-ring entry error
  `shortRingEntryError`.

The tail bound of the short-ring local law is not part of these ingredients. The short-ring
local law `Inputs.ShortRingLocalLaw` is proved by the zigzag route, as
`BlockBand.Native.ErdosRiabov.shortRingLocalLaw_holds`.

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, Definition 2.1, Proposition 2.8(ii), Theorem 3.3, and (3.17).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERExternalBandLocalClosure

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open ERProfile ERExactGaussianMoments ERLocalLawBootstrapAssembly
open ERDeterministicMDECore ERSharpCoordinateIBP
open ERTensorizedGaussianPoincare ERRingAdapter
open ERRingAdapterMeasurability
open ERDiscreteFourier ERCharacterAngle ERFluctuationMoments
open ERGaussianPoincareIntermediate

local instance (p : Params) : NeZero p.n := p.nNeZero

end ERExternalBandLocalClosure
end GaussianRing
end ERNative.BlockBand
