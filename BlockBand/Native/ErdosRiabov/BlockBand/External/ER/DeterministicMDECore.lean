module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.CyclicGreenSummation
public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ResolventIdentities

/-!
# Deterministic MDE core on the ER spectral domain

This module packages the deterministic pieces of the Erdős–Riabov MDE lemma that are
consequences of the sign-dependent semicircle branch and
the explicit cyclic Fourier inverse.  It does not assert the full vector-MDE
node and does not package any of the seven control-family clauses.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERDeterministicMDECore

open scoped BigOperators
open ERHerglotz ERDiscreteFourier ERFourierInverse ERCharacterAngle
  ERNearestNeighbor ERCyclicDecay ERCyclicSummation

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The sign-dependent semicircle value is the unique solution of the scalar Dyson
equation whose imaginary part has the sign of the nonreal spectral parameter. -/
theorem erSemicircleStieltjes_unique_herglotz {z m : ℂ}
    (hz : z.im ≠ 0)
    (hroot : m ^ 2 + z * m + 1 = 0)
    (hsign : 0 < m.im * z.im) :
    m = erSemicircleStieltjes z := by
  let s := erSemicircleStieltjes z
  have hsroot : s ^ 2 + z * s + 1 = 0 := erSemicircleStieltjes_dyson z
  have hssign : 0 < s.im * z.im := erSemicircleStieltjes_same_sign hz
  have hmnorm : ‖m‖ < 1 := norm_lt_one_of_dyson_and_same_sign hroot hsign
  have hsnorm : ‖s‖ < 1 := norm_lt_one_of_dyson_and_same_sign hsroot hssign
  by_contra hne
  have hms : m ≠ s := by simpa [s] using hne
  have hsum : m + s + z = 0 := by
    have hfactor : (m - s) * (m + s + z) = 0 := by
      linear_combination hroot - hsroot
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hms)
  have hprod : m * s = 1 := by
    have hz' : z = -(m + s) := by linear_combination hsum
    have hroot' := hroot
    rw [hz'] at hroot'
    have hone : 1 - m * s = 0 := by
      calc
        1 - m * s = m ^ 2 + (-(m + s)) * m + 1 := by ring
        _ = 0 := hroot'
    exact (sub_eq_zero.mp hone).symm
  have hnorm := congrArg norm hprod
  rw [norm_mul, norm_one] at hnorm
  nlinarith [norm_nonneg m, norm_nonneg s]

end ERDeterministicMDECore
end GaussianRing
end ERNative.BlockBand
