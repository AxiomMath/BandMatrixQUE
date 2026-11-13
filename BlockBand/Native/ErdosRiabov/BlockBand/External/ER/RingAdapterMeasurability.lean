module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.RingAdapter
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ProductCoordinateAnalysis
public import BlockBand.Native.ErdosRiabov.BlockBand.LinearAlgebra.MeasurableMatrixInverse

/-!
# Measurability adapter for the ER short-ring entry error

This module proves the measurability of the resolvent entries, and hence of the entry
error, for every `GaussianRing.Law`.  The proof uses
the totalized finite matrix inverse, so it applies at every deterministic height,
including `η = 0`; nonreal invertibility is not needed merely for measurability.

Source and normalization: Erdős–Riabov, arXiv:2506.06441v1, Definition 2.1,
Theorem 3.3 and (3.17).  The random matrix is the exact `Params`/`Law` Gaussian
ring, the ER resolvent is `-(zI-H)⁻¹`, and the error is measured entrywise
against the deterministic semicircle diagonal.  No stochastic domination,
tail estimate, asymptotic limit, or bootstrap input is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand.GaussianRing.ERRingAdapterMeasurability

open MeasureTheory ERConcrete
open ERProductCoordinateAnalysis

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The resolvent `(zI - H)⁻¹` is measurable for every fixed spectral parameter.
Unlike the nonreal analytic API, this statement uses the totalized nonsingular
inverse and therefore requires no hypothesis on `z.im`. -/
theorem Law.measurable_matrixResolvent_total {p : Params} (M : Law p) (z : ℂ) :
    Measurable (fun ω => matrixResolvent (M.H ω) z) := by
  unfold matrixResolvent
  apply Measurable.matrixNonsingInv
  apply Matrix.measurable_iff.mpr
  intro i j
  exact measurable_const.sub (M.measurable_entry i j)

/-- Every entry of the totalized fixed-parameter resolvent is measurable. -/
theorem Law.measurable_matrixResolvent_entry_total {p : Params} (M : Law p)
    (z : ℂ) (x y : Site p.n p.W) :
    Measurable (fun ω => matrixResolvent (M.H ω) z x y) :=
  (Law.measurable_matrixResolvent_total M z).eval_matrix

/-- ER's Green entry is measurable, with its resolvent minus sign
made explicit in the definition of `green`. -/
theorem Law.measurable_green_entry_total {p : Params} (M : Law p)
    (z : ℂ) (x y : Site p.n p.W) :
    Measurable (fun ω => green M z ω x y) := by
  change Measurable (fun ω => -(matrixResolvent (M.H ω) z x y))
  exact (Law.measurable_matrixResolvent_entry_total M z x y).neg

end ERNative.BlockBand.GaussianRing.ERRingAdapterMeasurability
